# Cluster build iteration — exact pending fixes (2026-08-05)

CURRENT STATE (2026-08-05, later session): **the build is fully green.**
3710/3710 targets, no errors and no warnings under
`-DwarningAsError=true`, and `lake build Audit` is green too.  The
per-module sections below are kept as a record of how each failure was
diagnosed; they are history, not a TODO list.  Two notes for next time:

* Lake is now 5.0.0 and has **no `-j`/`--jobs` flag** — cap the build
  with `taskset -c 0-31 lake build` instead.
* `lake` is not on the default remote PATH; prefix remote commands with
  `export PATH=$HOME/.elan/bin:$PATH`.

## What MSI Agate can and cannot do (measured 2026-08-05)

Agate is RHEL 8.10, kernel `4.18.0-553`, **glibc 2.28**.  Consequences, all
verified rather than guessed:

* **No Lean executable can be built there.**  The toolchain's bundled `clang`
  needs `GLIBC_2.29` and dies with a version error, so any `lake build` that
  reaches a `:c.o` target fails.  Library builds are unaffected because they
  stop at oleans -- which is why the corpus has always built fine and why
  `lean4export` cannot be built there at all.  Anything needing a Lean binary
  has to run on GHA (Ubuntu) or inside a container.
* **No Landlock** (needs kernel >= 5.13), so `landrun` -- and therefore
  `leanprover/comparator`'s sandbox -- cannot run on Agate.  `systemctl --user`
  also has no bus on the compute nodes.
* **Cargo builds need `RUSTFLAGS=` cleared.**  The login profile injects
  `-llapack -lopenblas`, which leaks into *build-script* linking; every crate
  with a build script fails with `unable to find library -lopenblas` before
  any real code compiles.

## Do not try to walk proof terms from a downstream script

In Lean 4.32 an importing module cannot see the proof bodies of imported
theorems: `ConstantInfo.value?` is `none` for them, in the elaboration
environment *and* in `env.setExporting false |>.checked.get`.  Axiom data is
precomputed per-module by `exportedAxiomsExt` when the olean is written, and
`Lean.collectAxioms` reads that table rather than re-walking bodies -- see the
comment in `Lean/Util/CollectAxioms.lean`, "axiom collection never crosses
module boundaries".  So a `lake env lean` script that traverses `value?` is
silently walking *types only* and will report a closure far smaller than the
truth.  Re-checking actual proof terms requires a tool that reads the oleans
directly: `leanchecker` (already in CI) or `lean4export`.

State: MSI auth works (breaker off; pushes via one-off credential helper
pinned to SauersML: `git -c credential.helper= -c credential.helper='!f() {
echo "username=SauersML"; echo "password=$(gh auth token -u SauersML)"; }; f'
push origin main`). Build loop: put changed files with `msi put f
/projects/standard/hsiehph/sauer354/nonsofic_existence/f`, then `lake build`
remotely. 3685/3689 targets green; four modules remain, errors fully
diagnosed from full bodies (task byuok6c6f):

## AlmostMinimalDisplacement
- :32 `Finset.le_sup' _ hg` can't infer f (displacement is semireducible).
  Fix: `by unfold displacement; exact Finset.le_sup' (fun g ↦ ‖ρ g ξ - ξ‖) hg`.
- :74 pin's `add_le_add_right h a : a + b ≤ a + c` (left-add!). Replace with
  `add_le_add (norm_le_displacement ρ Q hQ η hg) le_rfl`.

## HilbertCircumcenter
- :33 `hR ht : t ∈ closedBall x R` vs `dist x t ≤ R`: use
  `Metric.mem_closedBall'.mp (hR ht)`.
- :57 same add_le_add_left convention issue: use
  `add_le_add le_rfl (dist_le_coveringRadius hbdd y hs)`.
- :208 stuck `IsOrderedRing ?m` metavar near `div_le_one (by positivity)`
  in hm2/hn2 region (~line 205-212): add type ascriptions to the casts
  (read the lines first).
- :321 hinv forward branch beta mismatch persists even with `by exact`:
  replace with `refine ⟨g * h, ?_⟩; show φ (g * h) x₀ = φ g (φ h x₀);
  exact (hmul g h x₀).symm`.

## DiagonalClassGroup
- :82/:86: fin_cases mangles Fin literals + decide-proofs (type-incorrect
  under instances transparency). RESTRUCTURE diagUnit_conj_mem's `mem` case:
  prove a single general lemma instead of two special ones:
  `diagUnit_conj_elementaryUnit (u) (i j hij a) : diagUnit u *
   elementaryUnit i j hij a * (diagUnit u)⁻¹ = elementaryUnit i j hij
   (![(u:R),1] i * a * ![((u⁻¹:Rˣ):R),1] j)` proved at val level via
  `!![(u:R),0;0,1] = Matrix.diagonal ![(u:R),1]` (ext, fin_cases, simp) and
  `Matrix.diagonal_mul_single` / `Matrix.single_mul_diagonal`
  (names to verify), D(1+S)D' = DD' + DSD' with DD' = 1.
  Then mem-case: `obtain ⟨i,j,hij,a,rfl⟩ := hz; rw [diagUnit_conj_elementaryUnit];
  exact elementaryUnit_mem _ _ _ _` — no fin_cases at all.
- :121 `No goals`: in stableUnits_normal the `congr 1; exact map_inv ...`
  inside the show-block over-splits. Replace whole rewrite with:
  `have h := map_mul/map_mul/map_inv chain on diagUnitHom` then rw.
- :171 diagPair_mul entries need `simp [Units.val_mul]` (goal
  `↑u * ↑u' = ↑(diagPair (u*u') _) 0 0`).
- Downstream :213/:228/:235/:244/:281/:283/:285 errors were cascades/stale;
  re-check after above.

## UltralimitGeometry
- :422/:430 whnf timeout in bddAbove_orbit_seqNorm even at 1e6 heartbeats:
  whnf unfolds stdPart's `OrderRingHom.comp Classical.ofNonempty` dite.
  Fix: `attribute [irreducible] seqNorm seqNormSq` placed after
  seqNormSq_parallelogram (before Center section), keeping earlier
  unfold-based proofs working (they precede the attribute). If that breaks
  earlier proofs' rw [seqNorm]-style steps, scope it: set it just before
  the Center section. :434 kernel unknown-constant is cascade.

## ShalomFinitePresentation / others
- Not yet re-built after toGroup.of/lift_apply_of fixes; expect new errors
  after deps compile. GaussianPositiveDefinite: header now
  `open scoped Matrix InnerProductSpace Nat` (⟪⟫_ℝ is in InnerProductSpace
  scope, NOT RealInnerProductSpace).

## Rose-K₁ breakthrough (record!)
Unstable descent is now elementary: diag(u,1…1) ∈ E_{2^m}(L) ⟹ via
elementaryBlockGroup_map + prefix-code self-similarity, diag(κ_w(u),1) ∈
E₂(L), and κ_w(u) ≡ u mod H (proved) ⟹ u ∈ H. So H = ker(Lˣ → K₁(L)) and
ScalarReduction ⟸ STABLE K₁(L₂) = 0 (ABC09 at n=1 only). Candidate routes:
BHS-style splitting for the corner-skew Laurent presentation; or graded
triangulation induction on normal-form support through GE₂ over blocks.
Draft the unstable-descent theorem next (all ingredients proved).

## Teammate (tex-align-sweep)
Line-by-line on UltralimitGeometry still queued. All static sweeps clean.

## Rose-K₁ formalization roadmap (from ABC09 full text, user-supplied)
NOT eliminated: the paper's mathematical content. Eliminated: the need for
its full machinery (spectra, homotopy fibrations, Waldhausen NK-vanishing
in all degrees). With the proved unstable descent (H = ker K₁), the target
is STABLE K₁(L₂) = 0 over a field k, degree-1 only. Concrete plan mirroring
ABC09 §4 specialized to the 2-rose (no sinks, no sources, e₀ = 1):
1. L = L₀[t₊,t₋,φ] (corner-skew Laurent; their eq. (skewle), cites
   [skew, Lemma 2.4]); t₊ = a chosen s-generator, φ(x) = t₊ x t₋.
   L₀ = ⋃_n L_{0,n}, L_{0,n} = span{s_α t_β : |α|=|β|=n} ≅ M_{2^n}(k) —
   ultramatricial; repo's leftCombCode/prefix machinery covers this.
2. Twisted Bass–Heller–Swan at K₁ ONLY via Higman-style linearization for
   corner-skew Laurent rings (concrete matrix moves; Yao's proof low-degree
   part). Gives: units of L modulo E generated by units of L₀ modulo the
   relation u ~ φ(u) (plus NK₁-terms).
3. K₁ of ultramatricial-over-field: GL_N(M_{2^n}k) = GL_N·E with
   determinant; K₁(L₀) = colim kˣ — elementary over a field.
4. coker(1−φ) on kˣ = the proved c ≡ c² mechanism (n−1 = 1).
5. NK₁-vanishing for the specific von Neumann regular L₀ (low-degree only —
   NOT Waldhausen's general theorem). Research exact elementary proof.
Their explicit Δ_n/Ω_n transition matrices (proof of thm:skewle) are the
concrete forms to formalize for step 3-4.

## Rose-K₁ status (2026-08-05, after degree-zero milestone)
DONE and green (modules StableUnitsGenerators, FamilyDiagonalClass,
FieldMatrixReduction, LeavittDegreeZero):
- pairKappaUnit: corner insertion along ANY pair t*s = 1, with the
  GL₂-intertwiner coset identity (generalizes word-kappa).
- mem_stableUnits_of_val_unipotent: units 1 + a·b with b·a = 0 are in H.
- centralClassGroup A ≤ Aˣ: units = central·H; ScalarReduction A ⟺ all
  units in it (scalarReduction_of_forall_mem_centralClassGroup).
- CompleteMatrixFamily transvection pullback → H; diagonal-with-central-
  entries pullback → centralClassGroup (Finset-induction corner-sum
  factorization Π κᵢ(dᵢ)).
- unitsEquiv_field_matrix_mem_centralClassGroup: any unit identified by a
  family with a matrix over a FIELD (Mathlib Matrix.Pivot transvection
  decomposition) lies in centralClassGroup.
- fullBinaryCode n (all 2ⁿ words, complete) + entry scalar extraction:
  any unit with value in span{s_α t_β : |α|=|β|=n} is in centralClassGroup
  (mem_centralClassGroup_of_val_mem_levelSpan). With the proved central
  collapse c̄ = c̄² ⇒ c̄ = 1̄, degree-zero units are IN H.

REMAINING (the one frontier): Laurent width-reduction — arbitrary unit of
L₂ ≡ degree-zero unit modulo E-moves. Sharpened plan:
- Grading facts (all trivial identities): t₀^d s₀^d = 1; L_d = L₀·s₀^d for
  d ≥ 0, L_{−d} = t₀^d·L₀; normal form u = Σ_{e>0} t₀^e A_{−e} + A₀ +
  Σ_{d>0} A_d s₀^d, A_i ∈ L₀-span.
- Padding: span{balanced ≤ n} = span{balanced = n} via 1 = Σ_c s_c t_c
  (needed to feed mem_centralClassGroup_of_val_mem_levelSpan).
- Width reduction: E-move [[1,v],[0,1]]·diag(u,1)·[[1,0],[w,1]] =
  [[u+vw, v],[w,1]] with v := −A_N s₀^{N−1}, w := s₀ kills the top
  s₀-degree (and dually t₀ side); iterate at growing matrix size
  (Higman linearization) until all entries degree-zero; then
  fromMatrix(V) is degree-zero (s_γ(balanced)t_δ) → in H; descend via
  the (to-be-generalized to 2^m) mem_stableUnits_of_diagUnit_mem.
- KEY structural fact (why no ℤ-winding survives): L₂ has NO units of
  nonzero pure degree — rank obstruction in L₀ = ⋃ M_{2^m}(k)
  (a·p₀·b = 1 impossible: rank ≤ 2^{m−1}); ker(1−φ₀ on K₀) = 0 in ABC09
  terms. λ(u) = Σ s_b u t_b ≡ u² mod H for EVERY unit (fromMatrix of
  diag(u,u) = κ₀(u)κ₁(u)) — the c ↦ c² mechanism at unit level.

## Laurent endgame analysis (2026-08-05, second session)
Groundwork now green (FamilyDescent, LeavittGradingSpans):
- mem_stableUnits_of_cornerDiag_mem: descent at EVERY matrix size (the
  2^m generalization item is DONE — elementary group pulls back to H
  through any family; single-slot diagonal pulls back to pairKappa).
- levelMonomials_eq (length form), span_levelMonomials_mono (padding),
  monomial_factor_s0/t0 (positive monomial = balanced′·s₀; negative =
  t₀·balanced′), exists_corner_move (the Φ-move: for all v w,
  ∃ unit ≡ u mod H with value s₀(u+vw)t₀ + s₀vt₁ + s₁wt₀ + s₁t₁).
THE WALL, precisely: Φ-move with vw := −(positive part) kills positive
degrees of u but reinjects ONE positive-degree entry (v or w carries
it). This is the K₀-patching obstruction of classical BHS. Two
candidate elementary resolutions, in preference order:
1. Bass XII §7 semisimple-style ending using von Neumann REGULARITY of
   the balanced subalgebra: pseudo-inverses exist concretely — for
   balanced x at depth n, x = Θ(scalar matrix C) and C⁺ from Mathlib
   Pivot decomposition C = E₁DE₂, C⁺ := E₂⁻¹D⁺E₁⁻¹ (D diagonal, D⁺
   entrywise). Use idempotent pivots eB = top coefficient support to
   split the linear matrix and cancel the reinjected entry against the
   t-side. Needs on-paper derivation of the exact induction BEFORE
   coding; do width-1 case by hand first: u = t₀p + a + bs₀ unit.
2. If (1) stalls: no-pure-degree-unit rank argument is formalizable
   NOW: map balanced elements to scalar matrices (entry extraction),
   use Mathlib Matrix.rank + rank_mul_le; p₀^{(d)} has scalar matrix =
   0/1 diagonal of rank 2^{m−d} < 2^m = rank 1. Gives ker-part; the
   coker-part needs the coordinate-free lattice argument (heavier).
Audit note: audit re-run after the six new modules — GREEN, 6680
declarations, closure exactly [propext, Classical.choice, Quot.sound],
ASSUMPTION_INSTANCE still exactly 26.

## Laurent endgame ARCHITECTURE (width-1 hand-derivation, do in order)
Step A (Bass/vN-regular reduction — the remaining hard induction):
  every unit ≡ mod H to (balanced unit)·(code-permutation unit).
  Mechanism found: in the 2×2 picture [[a, −b],[σ, 1]] (reached by the
  proved Φ-composite from u = a + bσ), pivot on the invertible corner
  b̃ : fL₀ ≅ eL₀ of b (e := bb⁺, f := b⁺b, pseudo-inverse b⁺ from the
  Pivot decomposition at the FIXED matrix level M_{2^n}(k) of the
  original representation — all operations stay at level n, and
  rank(f) ≥ 1 strictly decreases per round, so ≤ 2^n pivots terminate.
  The exact op-sequence still needs a symbol-level paper derivation
  (watch: clearing ops reinject σ·(...)·b̃⁻¹ terms — verify the final
  matrix is triangular with UNIT diagonal before coding).
Step B (done): balanced units ∈ H (degree-zero theorem + central
  collapse).
Step C (new discovery — code-permutation units ∈ H, elementary):
  - Equal-length leaf transpositions T(w,w') = s_w t_{w'} + s_{w'} t_w
    + (1 − p_w − p_{w'}) are BALANCED → ∈ H by Step B directly.
  - Unequal-length transpositions: conjugate by a code-unit g with
    |g·w| = |g·w'| (prefix-replacement makes lengths equal); the
    conjugation identity g·T(w,w')·g⁻¹ = T(gw, gw') is a word
    computation; then T(w,w') ∈ H by NORMALITY of stableUnits — no
    abelianness needed.
  - General code-permutation unit = product of transpositions: Higman
    generation for Thompson's V — finite tree combinatorics; OR avoid
    it by making Step A's endpoint transposition-factored directly.
Alternative fallback for C if V-generation is painful: every
code-permutation unit U = U_{C'→leftComb} · U_{leftComb→C}⁻¹; reduce to
V_C := Σ s_{c_i} t_{ℓ_i} vs leftComb by induction on leaf-splitting.

## Step A DERIVATION RESULTS (third session — the state of the math)
1. WIDTH ≥ 2 IS ALREADY REDUCIBLE with the proved exists_corner_move:
   u with degrees in [−M, N], N ≥ 2: factor positive part = b·σ
   (monomial_factor_s0, b degrees [0, N−1]), apply the move with
   (v, w) := (−b, σ): result degrees max(N−1, 1) on top, negatives not
   grown. Mirror: (v, w) := (τ, −c) with negative part = τ·c kills
   bottom to max(−(M−1), −1), top unchanged. So mod H every unit
   reaches degrees ⊆ [−1, 1] — NO new math, just the induction to
   formalize (measure: max monomial |α|−|β| spread of a REPRESENTATION;
   representation-directed, no canonical components needed).
2. THE RESIDUAL CLASS: one more move funnels [−1,1] units to
   R := {units with value c + s₁s₀t₀, c balanced} (fixed universal
   tail β := s₁s₀t₀; note 1 + β ∈ H already: unipotent with A := s₁,
   B := s₀t₀, BA = 0). Remaining gap = R ⊆ H·(balanced units).
3. GRADED INDEPENDENCE IS FORMALIZABLE: weight the existing
   streamFamily (UniversalLeavittOver) over K := RatFunc k with
   s_i ↦ X·prefixOperator, t_i ↦ X⁻¹·deleteOperator (relations still
   hold); a finite sum Σ x_d of pure-degree elements maps to
   Σ X^d·ρ₀(x_d) with ρ₀ the unweighted action, so vanishing forces
   ρ₀(x_d) = 0 by X-transcendence, and ρ₀ is INJECTIVE because L₂ is
   simple (kernel is an ideal; 1 acts as identity ≠ 0 — simplicity is
   already proved: exists_mul_mul_eq_one). Gives canonical degree
   components, componentwise unit equations.
4. R-ENDGAME plan: for u = c + β ∈ R with inverse y = Σ y_d
   (canonical components by 3): top-degree cascade βy_{d*} = 0 forces
   support conditions (βx = 0 ⟹ t₀x = 0 and p₀x = 0 ⟹ x = p₁x);
   combine the cascade with the fixed-level M_{2^m}(k) rank argument
   (scalar-entry extraction + Matrix.rank + rank_mul_le) to force
   y = y₀ + y₋₁-shape and then solve. This replaces K₀-patching by a
   finite matrix-rank computation. Derive fully on paper next turn
   BEFORE coding; then formalize 1 → 3 → 4 in that order.

STATUS UPDATE (fourth session): item 1 IS FORMALIZED AND GREEN —
LeavittWindowReduction (degreeMonomials windows, exists_decomp_top/bot,
wrap_mem_span, corner_terms_mem_span, exists_top_cut/bot_cut,
exists_window_reduction) + BinaryLeavittWindow
(exists_narrow_representative: every unit of L_k(1,2) ≡ mod H to a
[−1,1]-window unit). Audit green at 6731 decls, ratchet still 26.
GRADED INDEPENDENCE (item 3) refined plan for FINITE fields (𝔽₂!):
scaled stream representations ρ_c (s_i ↦ c•P_i, t_i ↦ c⁻¹•D_i) over
K := RatFunc k give ρ_c(x_d) = c^d • ρ_1(x_d) on pure degree d; the
∀c-relation Σ c^d v_d = 0 over the INFINITE field K forces v_d = 0
(coordinate functional via Basis.extend + Polynomial.funext /
eq_zero_of_infinite_isRoot on Kˣ); ρ_1 over L_K faithful by simplicity
(kernel ideal + 1 ↦ id ≠ 0); base change β : L_k → L_K (lift of
family K along Algebra k L_K := RingHom.toAlgebra of composed
algebraMaps) is injective by simplicity of L_k, and maps degree-d
spans to degree-d spans — transports independence back to any k.
Then item 4 (residual class R = {c + s₁s₀t₀}) via componentwise unit
equations.

STATUS (fifth session): GREEN — VandermondeExtraction
(eq_zero_of_forall_units_zpow_smul; pin quirks: Module.Basis namespace
needs `open Module`; linearIndepOn_singleton_iff takes explicit R;
deprecations eval_finsetSum/finsetSum_coeff/Infinite.sdiff; rw of
b i₀ = v d₀ under dependent i₀-type needs congrArg-not-rw) and
GradedIndependence (graded_independence over [Infinite K]; supply
K,V explicitly to the extraction lemma).
REMAINING, in order:
(b) base change: letI : Algebra k (BinaryLeavittAlgebra (RatFunc k))
  := RingHom.toAlgebra ((algebraMap _ _).comp (algebraMap k _));
  β := lift (family (RatFunc k)); β on wordS/wordT by lift_generator
  induction; β injective by exists_mul_mul_eq_one k + Nontrivial;
  β maps degree-d spans into degree-d spans (span_induction; k-smul
  becomes algebraMap k K •[K]); Infinite (RatFunc k) via X-powers or
  Polynomial infinite + IsFractionRing injectivity. Conclusion:
  graded_independence for EVERY field.
(c) residual endgame for u = c + β₀ (β₀ := s₁s₀t₀, c balanced):
  canonical components now available — write u⁻¹'s components, cascade
  from top degree, fixed-level rank argument. Derive on paper first.

## Iteration log (continued)
- GREEN as of this round: DiagonalClassGroup, LeavittDiagonalClass,
  AlmostMinimalDisplacement, UltralimitGeometry, HilbertCircumcenter,
  GaussianPositiveDefinite.
- Root causes found this round (reusable): pin swaps add_le_add_left/right
  argument-side (use add_le_add h le_rfl / le_rfl h); Bracket instance for
  group commutators is SCOPED (open scoped commutatorElement); open scoped
  Nat imports the totient notation clobbering identifier phi; simp needs
  structure-def names (diagUnit, diagPair) to unfold vals; rw with same-term
  pattern consumes all occurrences (drop duplicates); section variables not
  in the STATEMENT are invisible in proofs (include L in); include-in must
  precede docstrings; single_apply_of_row_ne/col_ne have explicit index/value
  args; attribute [irreducible] seqNorm seqNormSq fixed the whnf blowup.
- Still to verify: DelormeFixedPoint, ShalomFinitePresentation, KazhdanCover,
  GLIsElementary, BinaryLeavittDiagonal, DiagonalDescent (first builds).

## Residual-class derivation state (sixth session, in progress)
For u = c + β (β := s₁s₀t₀, c balanced), y := u⁻¹ with canonical
components y_d (graded_independence_all now green):
- β² = 0 (t₀s₁ = 0 inside).
- Component equations: c·y_e + β·y_{e−1} = [e=0] and
  y_e·c + y_{e−1}·β = [e=0].
- Top degree N ≥ 1 (toward contradiction/reduction): β·y_N = 0 and
  y_N·β = 0; β·x = 0 ⟹ t₀x = 0 ∧ p₀x = 0 ∧ x = p₁x (extract via
  t₀t₁·β = t₀); annihilation chain β·y_{e−1} = −c·y_e for 1 ≤ e ≤ N.
- Factorizations: y_e = B_e·s_{0^e} with B_e := y_e·t_{0^e} satisfying
  B_e = B_e·p_{0^e} (right-supported); y_N·s₁·p₀ = 0.
- Next: push the chain into the fixed-level M_{2^m}(k) picture (all
  B_e, c at common depth m) and run the rank bound: B_N = p₁B_N p_{0^N}
  gives rank ≤ 2^{m−N}; combine the uy = 1 degree-0 equation
  c·y₀ + β·y₋₁ = 1 with the chain to force N ≤ 0 dually M ≤ ... then
  the [0,0]-case is a balanced unit (done). Alternative if rank path
  stalls: multiply chain by t₁-extractions to convert into explicit
  matrix equations over k.

## Residual endgame derivation, session 7 — MAJOR simplifications
- The residual tail IS a corner isometry: β = s₁s₀t₀ = s₁·p₀ (since
  s₀t₀ = p₀). So R-units are u = c + s₁p₀, c balanced.
- FREE MOVE FAMILIES (all in H by mem_stableUnits_of_val_unipotent):
  1 + s₁Xt₀ for ALL X (A := s₁X, B := t₀, BA = t₀s₁X = 0); dually
  1 + s₀Xt₁ for all X. Useful products against u:
  (1 + s₁Xt₀)·u = u + s₁·X·(t₀c)   [t₀β = 0]
  u·(1 + s₁Yt₀) = u + (cs₁)·Y·t₀   [p₀s₁ = 0]
  (1 + s₀Xt₁)·u = u + s₀X(t₁c) + s₀X·p₀  [t₁β = p₀]
- KILL CRITERion: u + s₁X t₀c balanced ⟺ X·(t₀c) + s₀t₀ ∈ L₋₁;
  u + cs₁Yt₀ balanced ⟺ (cs₁)·Y + s₁s₀ ∈ L₊₁.
- UNIT RELATIONS (y := u⁻¹, y₀ its balanced component — canonical by
  graded_independence_all): t₀·u = t₀c gives (t₀c)(ys₀) = 1, and the
  degree-0 component gives (t₀c)·z = 1 with z = Zs₀ PURE degree +1,
  hence (p₀c)(Zp₀) = p₀ with Zp₀ BALANCED.  Dually y·u = 1 right-mult
  s₁ gives y(cs₁) = s₁, degree-split y₀(cs₁) = s₁, hence
  p₁(y₀c)p₁ = p₁ with everything balanced.
- So in M_{2^m}(k): (p₀c)·(Zp₀) = p₀ (p₀-corner of c right-invertible
  in the corner) and (p₁y₀)·(cp₁) = p₁ (cp₁ full column rank).
- REMAINING CHIRALITY GAP: the left-move needs X(t₀c) ≈ −s₀t₀ (a
  LEFT-division by t₀c) but unit-ness gives its RIGHT inverse; the
  right-move needs (cs₁)Y ≈ −s₁s₀ (RIGHT division) but we have the
  LEFT inverse.  Next ideas: (i) use BOTH relations simultaneously —
  p₀-corner right-invertible + p₁-column-full may force c's rank
  structure to make one division solvable over M_{2^m}(k) via
  rank(p₀c) = 2^{m−1} ⟹ rowspace(p₀c) is a complement question;
  (ii) exploit that solvability is only needed MOD degree slack;
  (iii) symmetrize with the mirror residual (t-side tail) using the
  swap; (iv) failing exact kill, split c by vN-regular idempotents of
  p₀c and reduce the failure rank inductively (rank strictly drops,
  fixed level m, ≤ 2^m steps).

## Residual endgame, session 8 — unimodular matrix picture (KEY)
For u = c + s₁p₀ (c balanced), U := toMatrix(u) at depth 1 is
  U = [[a, b], [d + s₀, e]],  a := t₀cs₀, b := t₀cs₁, d := t₁cs₀,
  e := t₁cs₁ — ALL BALANCED, single tail entry s₀ at (2,1).
- (R1) ⟹ the ROW (a,b) is right-unimodular OVER THE BALANCED
  SUBALGEBRA: a·z₀ + b·z₁ = 1, z_j := t_jZs₀ balanced.
- (R2) ⟹ the COLUMN (b,e) is left-unimodular balanced:
  w₀·b + w₁·e = 1, w_j := t₁y₀s_j balanced.
- STABLE RANK 1 for L₀ = ⋃M_{2^m}(k) (formalizable, elementary):
  A·Z₀ + B·Z₁ = 1 in M_N(k) ⟹ ∃ T, A + BT invertible.  Proof: pick
  complement K' of ker A, complement W of im A; dim ker A = dim W
  (rank-nullity); im A + im B = k^N ⟹ basis w_i of W with
  w_i ≡ B u_i mod im A; T := (ker A ∋ e_i ↦ u_i, 0 on K');
  A + BT injective ⟹ invertible.  Inverse at the SAME level ⟹
  balanced.  Mathlib: finrank_range_add_finrank_ker,
  Submodule.exists_isCompl.
- PIVOT: col-op c₁ += c₂·t makes â := a + bt balanced-invertible;
  clearing row/col (free E-moves) gives [u] = [ê],
  ê = (e − d̂â⁻¹b) − s₀·(â⁻¹b) = ẽ − s₀g, ẽ,g BALANCED.
  Dually pivot on e via (R2) gives â' = b̃ + h·s₀ shape.
- For ê = ẽ − s₀g: t₁ê = t₁ẽ (t₁s₀ = 0) ⟹ (t₁ẽ)(ê⁻¹s₁) = 1 right-
  invertible; e := ê⁻¹s₁t₁ẽ = ê⁻¹p₁ê (p₁s₀ = 0!) idempotent conjugate
  to p₁; kill-move solvability for the tail ⟺ g·e = g.  Free move
  X := g·(ê⁻¹s₁) adds s₀·g·e EXACTLY, leaving tail −s₀·g(1−e) — but
  e is NOT balanced, so the balanced-shape bookkeeping breaks; the
  swap-conjugate converts s₀g-tails to s₁g'-tails (general residual
  shape u = c + s₁g).
- CHIRALITY WARNING (recurring): unit relations give RIGHT inverses
  where the kill-moves need LEFT division and vice versa.  The sr1
  pivot is the tool that BREAKS the symmetry: it converts
  unimodularity (which we do get from unit-ness) into an honest
  invertible balanced entry.  Next session: iterate the sr1-pivot on
  the [0,1]-shape ê = ẽ − s₀g itself: its depth-1 matrix has row
  (t₀ẽs₀ − gs₀?, ...) — NO: first swap-normalize to s₁-tail
  c' + s₁g', then matrixify: entries t_i(s₁g')s_j = δ_{i1}g's_j not
  balanced unless g' = p₀-shaped.  ALTERNATIVE next attack: use BOTH
  unimodularities at once — 2×2 over balanced with ONE non-balanced
  entry and both a-row and e-column completable: after making â
  invertible AND ê'-column invertible simultaneously (two independent
  sr1 choices), the Whitehead-style factorization of U may land in
  E₂(balanced)·diag(balanced-unit, unit-with-tail-in-p₀-corner) where
  the tail sits INSIDE a corner killed by rank descent at fixed level.

## Session 9: sr1 GREEN + new kappa move families
- StableRankOne.lean GREEN: exists_isUnit_add_comp_of_sup_range
  (End version; injectivity via projections only — no quotients) and
  exists_isUnit_add_mul_of_unimodular (Matrix version via
  Matrix.toLinAlgEquiv'; note: module ToLin, NOT ToLinAlgEquiv, at
  this pin; Submodule.projectionOnto takes p q EXPLICIT before h,
  apply-lemmas take them implicit).
- NEXT BRICK (mechanical, fully specified): transport sr1 to the
  balanced span: Θ := (family).prefixRingEquiv-fromMatrix ∘
  (algebraMap k A).mapMatrix : Matrix ι ι k →+* A is INJECTIVE
  (algebraMap injective entrywise + fromMatrix iso) with range =
  balanced span at depth n (monomials = images of single matrices;
  Θ C ∈ span since scalar•monomial ∈ span).  Transport unimodular
  rows a·z₀ + b·z₁ = 1 to matrices, apply sr1, pull back T and the
  INVERSE (same level ⟹ balanced): yields â := a + b·t balanced
  invertible WITH balanced inverse.
- NEW MOVE FAMILIES (session-9 discovery): for ANY z ∈ L,
  (s₀ + s₁z, t₀) is an isometry pair (t₀s₁ = 0!), giving
  [w] = [κ₀(w) + s₁·z·(w−1)·t₀] for every unit w and every z.
  Dually (s₀, t₀ + z·t₁) gives [w] = [κ₀(w) + s₀·(w−1)·z·t₁].
  These generalize pairKappaUnit beyond word pairs and give
  z-parameterized freedom to reshape residual tails — combine with
  the sr1 pivot loop: after pivot [u] = [ẽ − s₀g] (t₁ẽ right-
  invertible), try the dual pair with z chosen from ê⁻¹-data to
  cancel the reinjected tail.  Watch: κ₀ deepens tails (s₀s₁p₀t₀);
  apply the z-pairs BEFORE funneling, at the [−1,1] stage.

## Session 10: the obstruction is level-invariant — pivot must close it
For general residual u' = c' + s₁g (tail s₁g, g balanced): the kill
succeeds iff rowsp_m(g) ⊆ R := rowsp_m(p₀c') (kill-move changes g by
A·(p₀c'), arbitrary A).  The relation (p₀c')(Z'p₀) = p₀ holds for ALL
residual representatives (t₀ kills any s₁-tail), so rank(p₀c') is
always full (2^{m−1}).  KEY NEGATIVE FINDING: every level-m move is
δ-invariant, where δ := dim((rowsp g + R)/R):
- left family (1+s₁Xt₀): g += A(p₀c') — adds R-rows, δ fixed;
- right family (1+s₁Yt₀): (c', g) ↦ (c'(1+V), g(1+V)) simultaneous
  right-mult by unipotent V = p₁Vp₀-corner — δ fixed;
- block-diagonal balanced units: rowsp-preserving on both — δ fixed.
Hence the closing argument MUST use the depth-changing moves (the
toMatrix 2×2 sr1-pivot), which relate level-m data to level-(m+1)
data.  Plan: track (g, p₀c') through one full pivot+funnel cycle and
exhibit the self-similar rank relation that forces δ = 0 after
enough iterations (the ker(1−φ₀) = 0 mechanism: φ halves ranks, so
an invariant obstruction of positive rank contradicts stability).
z-κ families (session 9) may implement the tracking cleanly.

## Session 10b: the flip loop (derivation nearly complete)
GREEN this session: BalancedStableRank.lean (balancedEmbed n :
M_{2^n}(k) →+* A injective with range = balanced span;
exists_balanced_sr1_pivot: balanced unimodular pair ⟹ balanced t with
a + b·t a unit with balanced inverse).
DERIVATION (general residual u = c + s₀h₀ + s₁h₁, all balanced):
1. Depth-1 matrix: U = C̃ + H·S, C̃ := (t_i c s_j) balanced 2×2,
   H := (h₀,h₁)ᵀ balanced column, S := [s₀,s₁] co-isometry row
   (S·(t₀,t₁)ᵀ = 1, (t₀,t₁)ᵀ·S = I₂).
2. UNIT RELATIONS, degree-0 component of U·toMatrix(y) = I₂ gives
   C̃·V₀ + H·[q₀,q₁] = I₂ with V₀ := (t_i y₀ s_j), q_j := y₋₁·s_j all
   BALANCED — a 2×2 balanced right-unimodularity of (C̃ | H).
3. RECTANGULAR sr1 (generalize exists_isUnit_add_comp_of_sup_range to
   g : V' →ₗ V arbitrary source — same proof) ⟹ ∃ balanced row T
   (1×2): Û := C̃ + H·T invertible with balanced inverse.
4. U = Û + H(S − T) ⟹ [u] = [1 + H·S'] with S' := (S−T)·Û⁻¹ (row).
5. WHITEHEAD FLIP [1 + XY] = [1 + YX] (X := H 2×1, Y := S' 1×2;
   formalizable: diag(1+XY,1) ~E diag(1,1+YX) via 4 explicit
   elementary matrices; the four E-factors have arbitrary-entry
   blocks, all free).  Result: [u] = [σ], σ := 1 + S'·H ∈ Lˣ —
   an ELEMENT again, with σ = (balanced) + S·(Û⁻¹H), i.e. residual
   shape with new tail column H' := Û⁻¹·H.
6. LOOP: u ↦ σ maps tail-data H ↦ Û⁻¹H (balanced-invertible times H)
   plus re-extraction.  This move is NOT level-m-invariant (it uses
   depth) — the δ-invariance obstruction of session 10 does not
   apply.  REMAINING: find the terminating measure for the loop
   (candidates: the balanced ideal generated by entries of H against
   the corner filtration; or show one flip with OPTIMAL T from the
   sr1-freedom already lands h' with rowsp(h') ⊆ rowsp(p₀c')-solvable;
   or two flips compose to a level-m-solvable kill).
FORMALIZATION order once termination nailed: rectangular sr1 →
2×2-unimodularity extraction (needs component-calculus for toMatrix
of products — straightforward with graded independence) → Whitehead
flip → the loop.

## Session 11: element-level identification + level bookkeeping
- The "2×2 balanced unimodularity" IS the degree-0 component of
  u·y = 1 directly: for u = c + h (h := degree-1 part, h = s₀h₀+s₁h₁):
  c·y₀ + h·y₋₁ = 1, with h·y₋₁ balanced.  No matrix detour needed for
  the STATEMENT; the matrix picture is needed to APPLY sr1 (the
  pivot-parameter t ranges over window[−1,−1], and {h·t} corresponds
  to the rectangular block family B·T via the block dictionary:
  t_i(h·t)s_j = h_i·(t·s_j), t ↔ (ts₀, ts₁) bijective).
- RECTANGULAR sr1 (g : W →ₗ V arbitrary fin-dim source) — same proof
  as exists_isUnit_add_comp_of_sup_range verbatim; gives the ELEMENT
  pivot: ∃ t ∈ window[−1,−1]-span, û := c + h·t unit with balanced
  inverse [via block dictionary + level-m matrices].
- FLIP STEP: u = û + h(1−t): [u] = [1 + û⁻¹h(1−t)] = (flip, GREEN) =
  [1 + (1−t)û⁻¹h] = [c' + h'] with c' := 1 − tû⁻¹h balanced and
  h' := û⁻¹h — one full round, all pieces formalizable NOW.
- LEVEL BOOKKEEPING (important correction): the round maps the level
  pair (level c, level H) as (m, low-canonical) → then the C̃-level
  drops by one per round but the H-level FOLLOWS one behind and the
  pair PLATEAUS around (m−2, m−1).  The naive level-induction does
  NOT terminate by itself.
- BASE-CASE INSIGHT (works, formalizable): scalar-coefficient
  residuals γ + λ₀s₀ + λ₁s₁ (γ, λᵢ ∈ k, some λᵢ ≠ 0) are NEVER units:
  the stream representation image γ + Σλᵢ·prefixOperator is not
  surjective (the recursion f(w) = γ⁻¹(g(w) − λ_{w₀}f(tail w)) cannot
  terminate on constant streams; concrete non-preimage witness
  exists).  So IF the loop reaches scalar level, tails must vanish
  and u ≡ central ∈ H.
- REMAINING GAP (the one unknown): the plateau — show the loop
  composed with level-m moves strictly reduces a finite measure at
  the plateau level (candidates: rank of the kill-obstruction of H
  against rowsp(p₀c'); the affine self-map H ↦ Û(H)⁻¹H analyzed as
  the ABC09 transition action, ker(1−φ₀) = 0 realized as eventual
  solvability).  Alternatively strengthen the non-unit argument:
  characterize which (c, h) at the plateau admit units and show the
  kill is always solvable there.

## Session 12: corner-support discovery (sharpest lead for the finish)
Run one flip-round on the CANONICAL residual u = c + s₁p₀ with pivot
û := c + s₁p₀t.  Then the new balanced part is c' = 1 − w·p₀ with
w := tû⁻¹s₁p₀ (RIGHT-SUPPORTED: w = wp₀), and consequently:
- p₀c' = p₀(1−w)p₀ is CORNER-SUPPORTED (p₀c'p₁ = 0 since wp₀p₁ = 0);
- if the corner element p₀ − p₀wp₀ is invertible INSIDE the corner
  p₀Mp₀, then rowsp(p₀c') = rowsp(p₀) — the FULL half-coordinate
  row space;
- the new tails h'ᵢ = tᵢ(û⁻¹s₁p₀) are right-supported on p₀, and
  x = x·p₀ ⟹ rowsp(x) ⊆ rowsp(p₀).  KILL-CONDITION SATISFIED
  rowsp(tail) ⊆ rowsp(p₀c') whenever the corner-invertibility holds!
So the endgame reduces to TWO finite sub-steps at the plateau level:
(a) handle the h₀'-component (either choose t with t₀û⁻¹s₁ = 0 to
    make h₀' = 0, or solve the augmented system A·[p₀c' | s₀h₀'] =
    [−h₁' | 0] — the junk-vanishing condition As₀h₀' = 0 is finitely
    many balanced equations);
(b) show t can be chosen with BOTH û invertible AND p₀ − p₀wp₀
    corner-invertible (another sr1-flavored freedom argument: the
    corner condition is again a unimodularity statement in the corner
    algebra ≅ level-(m−1); candidate: derive corner-unimodularity of
    p₀(1−w)p₀ from û-invertibility + the p₀-corner of û⁻¹-relations).
If (a)+(b) close, the FULL CHAIN is: width-reduction (green) →
funnel to canonical (green machinery) → one flip-round (flip green,
element-pivot needs the block dictionary) → kill (green move
families) → balanced → H (green).  ScalarReduction follows; B4, B5,
B6 and Theorem C assemble; the manuscript is complete.

## Session 13: normal-form loop in closed form + the flag condition
GREEN: ResidualNormalForm.lean (exists_prefix_kill: z free mod L·t₀;
exists_corner_transport: [1+s₁βt₁] = [1+β] with corner inverse
t₁u⁻¹s₁, x = 1 − βx two-sided trick).
DERIVATION HARVEST:
- Normal form: every residual class = [1 + s₁z], z ∈ window[−1,0].
- THE LOOP in closed form: z ↦ û_L⁻¹(1−t_L)z₀ (left-sr1 pivot û_L,
  balanced part transforms z₀ ↦ û_L⁻¹z₀).  All level-preserving moves
  leave rank(z₀·p₁ mod L₀p₀) invariant — the kill succeeds iff
  z₀p₁ ≡ 0 mod the free ideal, i.e. iff p₀û_L⁻¹p₁ = 0 for the
  canonical-converted form.
- BLOCK-FLAG ANALYSIS: p₀M⁻¹p₁ = 0 ⟺ M(p₁V) = p₁V ⟺ colsp(cp₁) =
  p₁-coordinate half (M := û_L has Mp₁ = cp₁).  (R2) gives cp₁ full
  column rank; block-diagonal balanced conjugation can rotate
  colsp(cp₁) onto p₁V iff colsp(cp₁) ∩ p₀V = 0 ⟺ corner block
  c₁₁ = p₁cp₁ injective.  So the remaining question is now:
  (*) can the pre-moves always achieve c₁₁ invertible (or dually
  colsp(cp₁) transverse to p₀V)?  Candidates: sr1 inside the corner
  (c₁₁ + correction·(stuff) invertible via corner-unimodularity from
  (R2): p₁y₀·cp₁ = p₁ IS corner-left-unimodularity of (c₀₁-stack) —
  transversality via one more sr1-pivot with the s₁p₀-tail as the
  perturbation: u ↦ u(1 + s₁Y t₀)-moves change cp₁?? (they change
  c-columns only in p₀?): check which moves move colsp(cp₁).
- Non-units found: 1 + s₀ (stream surjectivity), 1 + s₁s₀t₁ (flip to
  1 + s₀).  Unit-ness genuinely constrains z₀.

## Session 14: THE ENDGAME MATHEMATICS IS COMPLETE (verify then batch-write)
For canonical residual u = c + s₁w (c, w balanced, p := p₀):
KILL-SEQUENCE (all moves already-green families; four steps):
0. NORMALIZE (right-mult by balanced unit h): make p·c·p' = 0 with
   p-corner pcp invertible.  Possible since rank(pc) = half (R1);
   column-reduce: ∃h invertible: (pc)h = [block | 0]  [F3-lemma].
   After this: kill-condition ⟺ w·p' = 0; kill-ideal = {X : X = Xp}
   (the move w += A(pc) reaches ALL of Mp since pcp invertible).
1. ROW-MIX (left-mult by block-diagonal balanced unit g = g₀⊕g₁,
   preserves pcp' = 0): tail w ↦ g₁'w.  Choose g₁' invertible so the
   p-rows of the new ω := wp' span rowsp(ω) — always possible since
   rank(ω) ≤ #columns(ω) = half ≤ #p-rows  [F1-lemma].
   Result: rowsp(p'ω) ⊆ rowsp(pω), i.e. ∃N: p'ω = −N(pω)  [F2-lemma:
   solvability of N·M = B from row-space containment].
2. SET wp (free via kill-moves): pwp := 0, p'wp := N from step 1.
3. TWIST (right-mult by the free unipotent 1 + s₀Yt₁ realizing
   V' := −pω, a p-row/p'-col corner): (c, w) ↦ (c(1+V'), w + V').
   The kill equation w_new = A·(p c_new) with c_new = c(1+V') splits
   into: p-cols: Ap := wp (free ✓); p'-cols: ω + V' = (wp)·V' —
   p-rows: (1 − pwp)V' = −pω: holds by V' := −pω, pwp = 0 ✓;
   p'-rows: p'ω = (p'wp)(−pω) = −N(pω)·(−1)-sign-check: holds by
   step 1-2 choice of N ✓.
4. KILL: A(p c_new) = −w_new solvable ⟹ tail dead ⟹ u ≡ balanced
   ⟹ ∈ H (balanced units green).  ScalarReduction FOLLOWS.
SUPPORT LEMMAS TO FORMALIZE (all finite linear algebra over k):
F1: ∀ω (n×half): ∃G invertible: bottom-rows(Gω) ∈ rowspan(top-rows).
F2: rowsp(B) ⊆ rowsp(M) → ∃N: N·M = B (Basis.constr lift, transpose).
F3: rank(M) = #rows → ∃H invertible: M·H = [M' | 0], M' invertible
    (column reduction).
MOVE-LEMMAS (element-level val-computations, all in green families):
- right-mult h: (c, w) ↦ (ch, wh); left block-diag g: (gc, g₁'w) with
  g₁' := t₁gs₁; kill-family: w += A(pc) via (1 + s₁(As₀)t₀);
  V'-twist via (1 + s₀Yt₁) with s₀Yt₁-image = V' = pV'p':
  (c, w) ↦ (c + cV', w + V').  [each: verify val-identity + junk-free]
ENTRY: width-reduction (green) → [−1,1] → funnel (exists_corner_move
with (v,w) = (−b, s₀)) → canonical c + s₁p₀.  EXIT: balanced → H.
SIGN/BLOCK details need re-verification during formalization — the
derivation was single-pass; treat each block identity as to-check.
Then: ScalarReduction (BinaryLeavittAlgebra k) unconditional →
upgrade BinaryLeavittDiagonal (drop hscalar) → B4/B5/B6 → final
manuscript assembly.  BATCH-WRITE ALL OF THIS NEXT (user directive:
write fully, then debug).

## Session 15 (continuous run): corrected moves + the DEEP kill module
- CORRECTION: right-mult by 1 + s₀Yt₁ acts as (c,w) ↦ (c(1+V), w(1+V))
  — session-14's kill-sequence step 3 was invalid.  Move algebra:
  (ch, wh) / (gc, g₁w) / (c, w + A·p₀c).  ResidualMoves.lean WRITTEN
  (blockDiagUnit, blockDiagUnit_mul_residual, kill_move_residual,
  kill_mover_mem) — not yet compiled (continuous-run mode).
- z₋ = 0 CLASSIFICATION: 1 + s₁z₀ (z₀ balanced) is a unit ⟺ s₁z₀ is
  nilpotent (geometric series is forced finite; negative components
  of the inverse vanish by downward recursion).
- COUNTEREXAMPLE to depth-1 kill-sufficiency: u = 1 + s₁s₀₀t₁₁ is a
  unit ((s₁s₀₀t₁₁)² = 0 via t₁₁s₁ = t₁, t₁s₀ = 0) with z₀ = s₀₀t₁₁,
  z₀p₁ = z₀ ≠ 0.  It IS trivially in H (unipotent a := s₁s₀₀,
  b := t₁₁, ba = 0).  Hence δ := rank(z₀p₁) is NOT class-invariant:
  the moves enumerated so far miss the DEEP families.
- THE DEEP KILL MODULE: movers 1 + s_{1α'}·X·t_{0β''} (incomparable,
  |α'| = |β''| for balance) change the tail by s_{α'}·A·(t_{0β''}c)
  with NO junk (t_{0β''}s₁ = 0).  K_c := span of all such changes ⊇
  old kill-ideal (α' = β'' = ∅ gives A·p₀c).  For c = 1 the module
  contains all s_{α'}At_{β''}-balanced elements — kills the
  counterexample (X := 1, α' = 00, β'' = 11).  CONJECTURE (final
  form): u = c + s₁w unit ⟹ w ∈ K_c.  Deep-matrix heuristic:
  K_c-membership ⟺ rowsp_deep(w) ⊆ rowsp of the deep matrices of
  t₀c; (t₀c)(ys₀) = 1 gives t₀c full row rank at EVERY depth.
  Remaining: prove the conjecture (candidates: induction on depth of
  w's representation using the full-row-rank at matching depth;
  or the z₋ = 0-classification generalized: reduce to nilpotent case
  by the loop, then nilpotent tails are killable via their explicit
  finite inverse).  NOTE the nilpotent-route: if z₋ = 0 then
  u = 1 + s₁z₀ with s₁z₀ nilpotent — u·(1 − s₁z₀ + (s₁z₀)² − …) = 1
  — and each partial product mover 1 + (finite sum) may itself be an
  H-member via iterated unipotent/flip decompositions of nilpotents:
  CHECK: is every unit of the form 1 + n (n nilpotent, n ∈ s₁·L₀!)
  in H?  1 + n with n^D = 0: 1 + n = Π-telescoping?  For n = s₁z₀:
  [1 + s₁z₀] = flip = [1 + z₀s₁] with (z₀s₁) nilpotent balanced-shifted
  … z₀s₁ pure degree +1 nilpotent ⟹ 1 + z₀s₁: window [0,1] with
  NILPOTENT tail: try induction on nilpotency degree D via the flip:
  each flip conjugates/shortens?  (s₁z₀)² = 0-case: 1 + s₁z₀ IS
  unipotent-lemma-able?? a := s₁z₀, b := 1: ba ≠ 0.  a := s₁, b := z₀:
  ba = z₀s₁ ≠ 0 but NILPOTENT — generalize mem_stableUnits_of_val_
  unipotent from ba = 0 to ba NILPOTENT: diag(1+ab, 1) vs 1+ba:
  Whitehead flip gives [1+ab] = [1+ba]; induct on nilpotency index:
  [1 + ba] with (ba)^{D−1}... (ab)^k-relations: THE FLIP REDUCES
  NILPOTENCY INDEX?? (1+ab)(1+ba): if (ab)² = 0 then 1+ab = unit and
  [1+ab] = [1+ba] with (ba)³ = b(ab)²a·… = 0-index-shifts by one!
  (ba)^{k+1} = b(ab)^k a: (ab)^D = 0 ⟹ (ba)^{D+1} = 0 — WRONG
  DIRECTION (index grows).  Decompose instead: 1 + n, n^D = 0:
  n = n', use 1 + n = (1 + n·e₁)(1 + n·e₂)···-idempotent-splittings?
  OVER A FIELD: nilpotent balanced-level N: 1 + N = product of
  ELEMENTARY transvections in M_{2^m}(k)!!  — 1 + N is UNIPOTENT
  matrix ⟹ ∈ E_{2^m}(k) ⟹ its image is in H by the
  field-matrix-reduction (unitsEquiv_field_matrix... centralClass)!!
  But s₁z₀ is NOT balanced (degree 1) ✗.  HOWEVER: 1 + s₁z₀ with
  (s₁z₀)^D = 0: pure-degree-1 nilpotent: at depth-D-matrix picture
  toMatrix_D(1 + s₁z₀) = I + (strictly-lower-triangular-by-degree
  block structure)?? — degree-+1 elements SHIFT the grading-blocks:
  the depth-j matrix of a degree-1 element has a SHIFT-structure ⟹
  1 + (degree-1-nilpotent) is I + (block-shift-nilpotent-matrix) ⟹
  UNIPOTENT MATRIX over the deep level ⟹ product of elementary
  transvections OVER THE BALANCED-DEEP-RING (not field — entries are
  L-elements... at depth D the entries of s₁z₀'s matrix: t_γ(s₁z₀)s_δ
  — NOT scalar).  Hmm.  Simplest honest: prove
  mem_stableUnits_of_val_unipotent' for n with n² = 0 directly:
  1 + n, n² = 0: diag(1+n, 1): [[1,n],[0,1]]·[[1,0],[?,1]]-…:
  1 + n = (1+n)·1: E₂-identity: [[1+n, 0],[0, (1+n)⁻¹-wait use
  diagPair_inv_self + flip with x := n, y := 1?? flip x=n,y=1:
  [1+n·1] = [1+1·n] trivial.  x := 1+?, …  DIRECT: n² = 0:
  1 + n unit with inverse 1 − n: is diag(1+n,1) ∈ E₂?
  [[1,n],[0,1]]·[[1,0],[-n?,1]]… compute [[1,n],[0,1]][[1,0],[y,1]]
  = [[1+ny, n],[y,1]]: want [[1+n,0],[0,1]]: ny = n: y := 1?? then
  [[1+n, n],[1, 1]]-no.  Known fact: 1+n (n²=0) IS a product of two
  of OUR unipotents?  n = n·1: n² = 0 ⟹ 1+n = (1 + a b) with
  a := n, b := 1 − n/2?? char-2-issues.  In fact for n² = 0:
  1 + n = (1 + n)·— just use the FLIP-form: n = s₁z₀ = a·b with
  a := s₁, b := z₀: [1 + s₁z₀] = [1 + z₀s₁] (flip ✓ green!) and
  z₀s₁: DEGREE +1 with (z₀s₁)² = z₀(s₁z₀)s₁: (s₁z₀)² = 0 ⟹
  (z₀s₁)³ = z₀(s₁z₀)²s₁ = 0: index ≤ 3… circles.  NEXT SESSION:
  settle "1 + nilpotent-in-tail ∈ H" cleanly, then reduce general
  residuals to the nilpotent case via the z₋-elimination (the
  y-negative-component recursion suggests: LOOP kills z₋?).

## Session 15b (continuous run): square-zero tails DIE + written modules
NEW MATH (verified on paper twice):
- z₋ = 0 classification: 1 + s₁z₀ (z₀ balanced) unit ⟺ s₁z₀ nilpotent.
- SQUARE-ZERO KILL: (s₁z)² = 0, z balanced ⟹ 1 + s₁z ∈ H via
  pseudo-inverse: a := s₁z, b := ξz (zξz = z): ab = s₁z, ba = ξ(zs₁z)
  = 0 since zs₁z = 0 by s₁-left-cancellation.  Uses vN-regularity of
  balanced elements (matrix generalized inverse via Pivot
  diagonalization: C = PDQ, C⁺ = Q⁻¹D⁺P⁻¹).
- z₋-elimination observation: in the loop, if 1 + z₋s₁ is invertible
  take t := 0: z ↦ (1+z₋s₁)⁻¹z₀ is PURE balanced-part — z₋ gone.
WRITTEN THIS RUN (uncompiled): ResidualMoves.lean,
ResidualReduction.lean (NarrowReduction hypothesis + full chain to
ScalarReduction/B4/GL₂/GL₄), BalancedRegularity.lean
(exists_pseudoInverse_matrix [name-risk: Matrix.Pivot or
TransvectionStruct namespace for prod_mul_reverse_inv_prod],
exists_balanced_pseudoInverse, square_zero_tail_mem_stableUnits).
REMAINING MATH for NarrowReduction: (i) general nilpotency index D
(flag/filtration splitting compatible with the ψ(e) := t₁es₁ twist,
or dyadic induction — index-2 case DONE); (ii) z₋-elimination in the
non-invertible case (sr1-t reinjects −û⁻¹tz₀; check whether the
REACHED form after one loop always has invertible 1 + z₋'s₁ — the
new z₋' = −û⁻¹tz₀ with t from sr1: is 1 − û⁻¹tz₀s₁ unit?
û = 1 + z₋s₁ + tz₀s₁ ⟹ û − tz₀s₁ = 1 + z₋s₁: 1 − û⁻¹tz₀s₁ =
û⁻¹(û − tz₀s₁) = û⁻¹(1 + z₋s₁) — PRODUCT OF INVERTIBLE-IFF:
1 − z₋'s₁-NEW-c₂' = û⁻¹(1 + z₋s₁)?!?! CHECK THIS: c₂' := 1 + z^new₋s₁
= 1 − û⁻¹tz₀s₁ = û⁻¹(û − tz₀s₁) = û⁻¹(1 + z₋s₁): INVERTIBLE ⟺
1 + z₋s₁ invertible.  So: if 1 + z₋s₁ invertible: eliminate now;
else c₂' is NON-invertible again — the invertibility of 1 + z₋s₁ is
loop-INVARIANT?!  New attack for (ii): 1 + z₋s₁ non-invertible:
z₋s₁ balanced: use IT as data — u = 1 + s₁z: FLIP: [1+s₁z] =
[1+zs₁] = [(1 + z₋s₁) + z₀s₁] — the balanced part of the flipped
form IS 1 + z₋s₁: run sr1 on the OTHER side/dual pivot, or note
(1+zs₁)-unit with balanced-part-singular still fine — kill z₀s₁-part
against it...  CONTINUE HERE NEXT MATH TURN.

## Session 15c: the γ-invariant — NarrowReduction reduces to TWO lemmas
Define γ(1 + s₁z) := 1 + z₋s₁ (balanced).  Facts derived:
- γ is MULTIPLICATIVE on [−1,0]-form products:
  γ((1+s₁a)(1+s₁b)) = γ(a-form)·γ(b-form)  [only (−1,−1) hits deg −1].
- γ is INVARIANT under both free families (t₀s₁ = 0 protects it) and
  transforms by left-mult under the loop (c₂' = û⁻¹(1 + z₋s₁)) and by
  conjugation under block-diagonal moves — its (non)invertibility is
  an invariant of all known moves.
- If γ invertible: flip + absorb: [1+s₁z] = [1+zs₁] = [γ]·[1+γ⁻¹z₀s₁]
  = [1 + s₁γ⁻¹-moved z₀-pure form] ⟹ z₋ = 0 case ⟹ tail NILPOTENT
  (classification) ⟹ kill by (i).
NARROWREDUCTION ⟸ (G) + (i):
(G): u = 1 + s₁z unit ⟹ γ = 1 + z₋s₁ invertible in the balanced
  algebra.  [Test-verified on κ₁-images (⟺ unit-condition), free
  movers (γ = 1), products (multiplicativity).  Attack: the
  (XX_d)-system (1+s₁z₋)y_d = [d=0] − s₁z₀y_{d−1} plus py_d-facts
  downward induction; or stream-representation invertibility
  restricted to a γ-detecting subspace.]
(i): 1 + s₁z₀ with (s₁z₀)^D = 0 ⟹ ∈ H.  Index 2 PROVED
  (square_zero_tail_mem_stableUnits, written).  General D: filtration
  splitting compatible with ψ(e) = t₁es₁, or dyadic induction via
  [1+n]² = [1+n²]-char-2-plus-odd-part, or flag idempotents from
  vN-regularity of the P_k := (z₀s₁)^k z₀ kernel chain.
Also: entry into 1+s₁z-form from the [−1,1]-window: [window-unit] =
[c + s₁w-funnel-output] — then LEFT-round (sr1-pivot) gives the
1 + s₁z-form; both formalizable with existing machinery (sr1 needs
the element-level block dictionary — the remaining nontrivial
formalization plumbing).

## Session 15d: exact p-split; (i) reduced to p'-supported tails
- EXACT IDENTITY: (1 + s₁z₀p₀)(1 + s₁z₀p₁) = 1 + s₁z₀ (cross term has
  p₀s₁ = 0).  First factor has square-zero tail ((s₁z₀p₀)² = 0 same
  way) ⟹ in H by square_zero_tail_mem_stableUnits.  So
  [1 + s₁z₀] = [1 + s₁(z₀p₁)] ALWAYS — tails reduce to p₁-supported.
- p₁-supported tail: s₁(z₀s₁t₁)·— κ₁-sandwich: 1 + s₁(z₀s₁)t₁ =
  κ₁(1 + z₀s₁) ⟹ corner transport (green) gives [1+s₁z₀] = [1+z₀s₁]
  — an independent derivation of the flip for these shapes, with all
  factors explicit.
- Twisted-product criterion: n = s₁z₀ nilpotent of index D ⟺
  Q_{D−1} := z₀·φ(z₀)·…·φ^{D−1}(z₀) = 0 where φ(x) := s₁xt₁
  (multiplicative!).  Flag-splitting attempts (support idempotents
  σ_k): D = 2, 3 terminate; D ≥ 4 the junk factors block clean
  telescoping — needs the fixed-point support construction or another
  route.  Deep-matrix triangularity fails (degree persists).
- STATE: (i) index-2 proved; index-general open but tails now
  p₁-supported WLOG (formalizable now); (G) open with the
  (XX_d)-system attack.  These two remain the entire mathematical gap
  for NarrowReduction ⟹ ScalarReduction ⟹ manuscript completion.

## Session 16: (i') reformulation, vacuous-split traps, W-induction base
- (i) ⟺ (i'): units 1 + ζ with ζ pure degree +1; unit-ness FORCES ζ
  nilpotent automatically (downward recursion kills negative inverse
  components, x_d = (−ζ)^d, finiteness ⟹ nilpotency).  So (i') is:
  1 + ζ, ζ ∈ L₁ nilpotent ⟹ ∈ H.
- σ-form criterion: ζ = Bσ, ζ^D = R_{D−1}σ^D with
  R_j := B·φ₀(B)···φ₀^j(B), φ₀(x) := s₀xt₀; nilpotency ⟺
  R_{D−1}·p_{0^D} = 0 (NOT R = 0 — σ not right-injective).
- VACUOUS-SPLIT TRAPS (documented so they're not retried): for
  Bσ-forms, right-support splits of B are vacuous (pσ = σ, p'σ = 0);
  for Cs₁-forms, left-p-splits vacuous (p's₁ = s₁, ps₁ = 0);
  left-support splits vacuous by definition of support.  The ONE real
  split is the proved s₁z-form/right-support: [1+s₁z] = [1+s₁zp₁].
- Width-of-inverse induction: base W = 0 works (y balanced-valued
  unit ⟹ y ∈ centralClass green ⟹ [u] = [y]⁻¹ trivial).  But width
  is invariant under balanced multipliers and degree-(±1) H-movers
  miss the top component — the step needs the same missing mechanism.
- char-2 shortcut evaluated and rejected: (1+n)² = 1+n² gives only
  2-torsion, not triviality.
NEXT: (G) via the (XX_d) system remains the most structured target;
for (i') the twisted-flag fixed-point construction (session 15d) with
the ψ-compatible idempotents is the open front.  Also consider:
represent 1 + ζ at depth D (index): entries of toMatrix_D(ζ) vanish
except γ-starting-1-blocks with SHORTER words — check whether ζ^D = 0
forces a STRICT block-triangular structure at depth D against the
cylinder flag {p_{1^k0...}} — the cylinder flag is the natural
φ-compatible flag and may make every nilpotent tail literally
strictly triangular w.r.t. a balanced idempotent chain, giving the
telescoping product decomposition into square-zero pieces with the
ordered cross-conditions holding by flag-position.

## Session 17: TailSupportReduction written + (G)-unimodularity extracted
WRITTEN (uncompiled): TailSupportReduction.lean — mul_p0_mem_span /
mul_p1_mem_span (right multiplication by corner projections selects
monomials by first t-letter, staying in the balanced span at depth
n+1), and exists_tail_support_reduction: the exact p-split
[1 + s₁z] = [1 + s₁(z·p₁)] with the explicit square-zero left mover
1 − s₁(zp₀) ∈ H.
(G)-DERIVATION ADVANCE (from the (V_d) bottom cascade of the flipped
form v = γ + z₀s₁, x := v⁻¹):
- L_{−M} elements expand as Σ (x s_w) t_w with BALANCED coefficients;
  {t_w}-independence (right-multiply by s_w) extracts balanced
  equations from every graded component.
- The degree-0 equation yields the UNIMODULARITY
  γ·x₀ + (z₀p₁)·Y = 1 with Y := s₁(x₋₁s₀)t₀ + s₁(x₋₁s₁)t₁ balanced
  (every p₁-row-supported balanced Y arises as s₁(t₁Y s₀)t₀ +
  s₁(t₁Y s₁)t₁).
- Rectangular sr1 (green) ⟹ ∃T balanced: û := γ + (z₀p₁)T invertible
  with balanced inverse.
- Pivot + flip: [v] = [1 + s₁·z^new] with
  z^new = (1 − t₁T)û⁻¹z₀:  z^new₀ = û⁻¹z₀,  z^new₋ = −t₁Tû⁻¹z₀,
  and the balanced part of the new flipped form is
  c = 1 − p₁Tû⁻¹z₀, giving p·c = p EXACTLY (kill-ideal = Mp).
- γ^new = 1 − t₁Tû⁻¹z₀s₁; invertibility of γ^new ⟺ invertibility of
  1 − p₁Tû⁻¹z₀ = c (ab/ba flip).  So the loop's γ-question becomes
  the invertibility of the new balanced part c — one more application
  of the SAME extraction to the new form may close (G) by a
  finite-descent (each round the balanced part is 1 − p₁(...) with
  p-corner IDENTITY — its singularity lives in the p₁-corner only;
  the p₁-corner of c is 1 − (p₁Tû⁻¹z₀)-corner: iterate the corner:
  candidate终 termination: the corner perturbations are compressions
  by t₁·(...)·s₁ which STRICTLY deepen the cylinder support —
  after finitely many rounds the perturbation's corner support
  exhausts and c becomes unipotent-plus-identity ⟹ invertible).
NEXT: nail the corner-depth termination for (G); then (i') general
index remains (p₁-supported reduction now WRITTEN).

## Session 18: LEMMA (i') PROVED — nilpotent tails die, all indices
THEOREM: z balanced, n := s₁z, n^D = 0 ⟹ 1 + s₁z ∈ H.
PROOF (induction on D; base D ≤ 2 = square_zero_tail_mem_stableUnits,
written):
Let D ≥ 3, r := (zs₁)^{D−2}z (pure degree D−2; nonzero else lower
index).  Facts: r·s₁·z = (zs₁)^{D−1}z = 0 (from n^D = 0 by
s₁-cancellation).
1. PSEUDO-INVERSE OF PURE-DEGREE ELEMENTS: r = R·σ_d with d := D−2,
   σ_d := wordS(0^d), R := r·τ_d balanced, R = R·p_{0^d}
   automatically.  Take Ξ balanced with RΞR = R (balanced regularity,
   written) and η := τ_d·Ξ.  Then rηr = R(σ_dτ_d)ΞRσ_d = RΞRσ_d = r.
2. e := η·r = τ_d(ΞR)σ_d: idempotent (e² = η(rηr) = ηr), BALANCED
   (τ_d·(balanced)·σ_d sandwich — needs the span-closure lemma
   t-word·span·s-word ⊆ span, same pattern as mul_p0_mem_span), and
   r·e = r.
3. KEY VANISHING: z·e·s₁·z = zη(r·s₁·z) = 0.
4. THE MOVE: mover m := 1 − s₁(ze): (s₁ze)² = s₁·(zes₁z)·e = 0,
   ze balanced ⟹ m ∈ H by square_zero_tail_mem_stableUnits.
   Product: m·(1 + s₁z) = 1 + s₁(z − ze − zes₁z) = 1 + s₁·z(1−e).
5. INDEX DROP: z' := z(1−e): expand (z's₁)^{D−2}z' over choices
   {zs₁, −zes₁} and final {z, −ze}: any term with e in a NON-final
   position contains zes₁·z = 0; the two survivors are
   (zs₁)^{D−2}z = r and −(zs₁)^{D−2}ze = −re = −r: they CANCEL.
   Hence (z's₁)^{D−2}z' = 0: index of s₁z' ≤ D−1.  Induction. ∎
LEAN PLAN (module NilpotentTailKill.lean):
- span-closure: mul by t-words on left / s-words on right of the
  balanced span (τ_d X σ_d sandwich) — generalize mul_p0_mem_span to
  arbitrary single letters, then induct over words;
- pure-degree right-mult: r·τ_d ∈ balanced span for r in
  window[d,d]-span (same machinery);
- the theorem by strong induction on D with the five steps above;
  the expansion step 5 needs a finite product-expansion lemma — do it
  by direct induction on D−2 with the two-term recursion
  (z's₁)^k z' = (zs₁)^k z(1−e) for all k ≤ D−2, proved by:
  (z's₁)((zs₁)^k z(1−e)) = (zs₁)^{k+1}z(1−e) − zes₁(zs₁)^k z(1−e);
  and zes₁(zs₁)^k z = zes₁z(...) = 0 for k ≥ 0 — WAIT check:
  zes₁·(zs₁)^k·z: starts zes₁z when k = 0 ✓ = 0; for k ≥ 1:
  zes₁·zs₁(...) = (zes₁z)s₁(...) = 0 ✓ ALWAYS.  So the recursion is
  CLEAN: (z's₁)^k z' = (zs₁)^k z (1−e) by induction on k — no
  binomial expansion needed!  Then k := D−2 gives r(1−e) = 0.
REMAINING for NarrowReduction: only the z₋-elimination/(G) — with
(i') done, NarrowReduction ⟸ (G) alone.

## Session 19: (G) dichotomy + worked instance; Fitting framework
- DICHOTOMY (proved): for u = 1 + s₁z, γ' := 1 + s₁z₋ (BALANCED —
  note s₁z₋ is degree 0!): γ' invertible ⟺ u⁻¹ has no negative
  graded components.  (⟸: bottom equation (1+s₁z₋)y_{−M} = 0 with
  y_{−M} = Σ C_w t_w, t_w-independence gives balanced kernel
  elements; ⟹: same equation kills y_{−M}.)  Note γ' vs γ = 1+z₋s₁:
  flip-equivalent invertibility.
- WORKED INSTANCE of (G): z₋ := −t₁ (γ' = p₀, maximally singular):
  u = p₀ + s₁z₀ is NEVER a unit: uy = 1 forces s₁z₀y = p₁ hence
  z₀y = t₁ hence y = z₀⁻¹t₁ (z₀ must be balanced-invertible), and the
  p₀-component equation forces p₀z₀⁻¹t₁ = p₀ — degree −1 = degree 0,
  contradiction by graded independence.
- GENERAL (G) FRAMEWORK: Fitting decomposition of the BALANCED
  element γ' at its level: π' := projector onto the generalized
  kernel (γ'π' =: N nilpotent, commutes with π'; γ'(1−π') corner-
  invertible).  The π'-corner unit equation reads (N + M)y = π' with
  M := π's₁z₀ pure degree +1; graded components give
  N·y_d + M·y_{d−1} = [d=0]π'; applying N^{K−1} isolates
  N^{K−1}My₋₁ = N^{K−1} ≠ 0, and coefficient extraction (x = Σ(xs_j)t_j
  valid for ALL x) turns this into balanced equations.  The worked
  instance is the K = 1 case where the (1−π')-side forces the graded
  contradiction.  CONJECTURED PROOF SHAPE: induction on K, pushing
  the contradiction of the K = 1 case through the nilpotent cascade.

## Session 20: second (G) instance + staircase formulation + chain plan
- Second non-unit verified: u = (1 − p₁₁) + s₁₁t₁ (γ' = 1 − p₁₁
  singular): the downward cascade forces t₁y₋₁ = t₁₁ and then
  γ'y₋₁ acquires an s₁t₁₁-component outside Im(s₁₁t₁·) = s₁₁·L,
  unsolvable by monomial prefix independence.  Pattern matches the
  p₀-instance: singular γ' + unit-ness ⟹ cascade escapes the image.
- (G) staircase formulation: u unit ⟺ 1 ∈ image of the staircase
  operator (y₀,…,y_{−M}) ↦ γ'y₀ + s₁z₀y₋₁ subject to
  γ'y_d + s₁z₀y_{d−1} = 0; (G) ⟺ solvability forces γ' invertible.
  Fitting corner analysis (K=1): all corner equations are consistent
  (tautological) — the contradiction must use monomial/prefix
  independence ACROSS levels as in both instances.  Note π = p₁π
  (kernels live under p₁ since p₀γ' = p₀), and the collapse
  Z·s₁ = W₁ with πs₁W₁ = πs₁, πs₁W₀ = πs₀.
- γ-ELIMINATION CHAIN (writable now, given γ-invertibility):
  γ = 1 + z₋s₁ invertible ⟹ γ⁻¹ balanced (γx = 1 ⟹ γx₀ = 1 at the
  balanced component ⟹ matrix-invertible in the subalgebra) ⟹
  [1+s₁z] = flip = [γ(1 + γ⁻¹z₀s₁)] = [1 + γ⁻¹z₀s₁] = flip =
  [1 + s₁(γ⁻¹-moved z₀)] pure z₋ = 0 ⟹ nilpotent automatic ⟹
  NilpotentTailKill.  Writing this as GammaReduction.lean with
  γ-invertibility as the explicit hypothesis.

## Session 21: (G) system fully catalogued; GammaReduction.lean written
WRITTEN: GammaReduction.lean (complete, hypotheses explicit).
(G) DERIVATION STATE — the master catalogue:
- MASTER FORM: u = p₀ + s₁·h with h := t₁ + z ∈ window[−1,0];
  h·(ys₁) = 1 (h right-invertible ALWAYS); (ys₁)h = 1 − yp₀ with
  f := yp₀ idempotent ≠ 0, p₀fp₀ = p₀, hf = 0.
- Λ-IDENTITY: s₁·Λ(x) = γ'x − p₀x where Λ(x) := (t₁ + z₋)x = h₋x.
- THE (S)-SYSTEM (t₁-extraction of positive equations):
  z₀y_d = −Λ(y_{d+1}) for 0 ≤ d ≤ N (y_{N+1} = 0).
- THE (C)-SYSTEM (negative side, coefficients C^{(j)}_w = y_{−j}s_w):
  γ'C^{(M)}_w = 0 at the bottom; z₀C^{(j+1)}_{wi} = −Λ(C^{(j)}_w)s_i;
  z₀C^{(1)}_i = [i=1] − Λ(y₀)s_i.
- ker γ' = {q : p₀q = 0, h₋q = 0}; kernels live under p₁; the flip
  kernel: left-kernel rows q' satisfy q's₁(1 + z₋s₁) = 0.
- INSTANCE VERIFICATIONS through (S): instance 1 (Λ = 0): z₀
  invertible forced, positive side forces z₀y₀ = 0 ⟹ y₀ = 0 ⟹
  contradicts p₀y₀ = p₀.  Instance 2: (S)-top forces y_N = 0 (N ≥ 1),
  then y₀ = p₀, then (XX₀) demands s₁₁t₁y₋₁ = p₁ — impossible by
  prefix independence (p₁₁ ≠ p₁).
- TAUTOLOGY TRAPS documented: p₀s₁ = 0 absorbs every naive q'-pairing;
  the corner equations are self-consistent — the contradiction is
  GLOBAL, coupling the finite (S)+(C) system with p₀y₀ = p₀.
- NEXT ATTACK: dimension/rank count over k of the finite staircase
  system: the unknowns (y_d components at bounded window/level) vs
  the equations; γ'-singularity creates a strict solvability defect
  that p₀y₀ = p₀ cannot meet — formalize the count on the finite-
  dimensional filtration pieces (all data at a common level m and
  bounded degree window; the staircase matrix is block-bidiagonal
  with γ' on the diagonal and s₁z₀ off-diagonal; det-style argument:
  the system forces 1 ∈ Im(bidiagonal operator) whose cokernel
  contains the γ'-cokernel at the 0-block — CHECK: is the d=0 block
  row exactly γ'y₀ + s₁z₀y₋₁ = 1 with coker(γ') obstructing modulo
  the s₁z₀-column? The instances say the s₁z₀-column cannot cover the
  γ'-cokernel because its image is s₁-prefixed while the cokernel
  needs p₀-content: p₀·(s₁z₀X) = 0 but p₀·1 = p₀ ≠ 0 — wait:
  p₀γ'y₀ = p₀y₀ = p₀ ✓ consistent... the p₀-row of the d=0 equation
  is auto-satisfied; the obstruction sits in the p₁-row where
  γ'|p₁-part = p₁ + s₁z₋ acts — TRY: q'-left-kernel pairing against
  the d = 0 equation DIRECTLY: q'γ' = 0 ⟹ q' = q's₁z₀y₋₁ (derived);
  iterate this DOWN the C-system: q' = q's₁z₀C-terms and
  z₀C^{(j)} = −Λ(C^{(j-1)})s-recursion pushes q' into
  q'·s₁·(z₀-Λ-chains) of length M+1 ending at γ'C^{(M)} = 0-kernel
  coefficients... then the chain terminates with q'·(...)·0 = q' ⟹
  q' = 0 IF each step is genuinely composable — CHECK THIS NEXT:
  q' = q's₁z₀y₋₁ = q's₁z₀(C_0t_0 + C_1t_1), substitute
  z₀C_i-hmm z₀C_i appears LEFT-multiplied inside; the recursion gives
  z₀C^{(1)}_i in terms of Λ(y₀) NOT of deeper C's — the descent
  direction is (G_{w,i}): z₀C^{(j+1)} = −Λ(C^{(j)})s_i: so
  q' = q's₁·z₀·y₋₁ needs z₀y₋₁ = z₀(C_0t_0+C_1t_1): z₀C_i-BUT the
  system gives z₀C^{(1)}_i directly = [i=1] − Λ(y₀)s_i!!! SUBSTITUTE:
  q' = q's₁([1-slot term] + corrections): q' = q's₁(z₀C_0t_0 + z₀C_1t_1)
  = q's₁(−Λ(y₀)s_0·t_0 + (1 − Λ(y₀)s_1)t_1)
  = q's₁t_1 + q's₁Λ(y₀)(−s_0t_0 − s_1t_1)
  = q'p₁ − q's₁Λ(y₀)  [since s_0t_0+s_1t_1 = 1]
  AND s₁Λ(y₀) = γ'y₀ − p₀y₀ = γ'y₀ − p₀ (Λ-identity + P!):
  q's₁Λ(y₀) = q'γ'y₀ − q'p₀ = 0 − q'p₀:
  ⟹ q' = q'p₁ + q'p₀ = q' — TAUTOLOGY AGAIN (p₀+p₁ = 1).  ALL linear
  pairings are consistent; the contradiction MUST be nonlinear
  (rank/dimension count) or use the mirror system (yu = 1) jointly.

## Session 22: (G) rank-count exhausted consistent; γ' IS MOVABLE
- M = 1 nonlinear relations derived: pairing the two inverse systems
  gives y_{−M}·s₁z₀·y_{d−1} = [d=0]·y_{−M}; for M = 1 this yields
  BALANCED idempotents P := s₁z₀y₋₁ (= p₁P, rank δ) and
  E := C₁z₀ with C₁z₀C_j = C_j, colsp(C₁) = ker γ' exactly,
  rank(C₁) = δ = corank(γ'), 1 − P ∈ γ'·Mat with colsp(1−P) =
  colsp(γ') exactly.  EVERY rank/subspace constraint checks out
  consistently, including the level-(m+1) scaling (rank P = 2δ_m from
  both computations).  The abstract matrix model of the system admits
  no contradiction — the instances' contradictions used the LEVEL
  EMBEDDING structure (s₁Xt_j corner copies), not the level-m algebra.
- VERDICT: (G) via rank counting at a fixed level is DEAD; (G) itself
  is possibly false as stated, and definitely not needed:
- KEY DISCOVERY: the p-split mover 1 − s₁(z·p₀) is in H for ARBITRARY
  z ∈ window[−1,0] (mem_stableUnits_of_val_unipotent with
  a := −s₁zs₀, b := t₀, ba = 0 — NO balancedness needed).  Hence
  [1 + s₁z] = [1 + s₁(z·p₁)] for mixed z, and more generally for all
  0-rooted cylinder projections V = p_{0w'} (t_{0w'}s₁ = 0):
  [1 + s₁z] = [1 + s₁·z(1 − p_{0w'})].  These moves CHANGE
  z₋ ↦ z₋·p₁ etc. — γ' is NOT invariant under them (session 15c's
  invariance was only for the other families).
- NEW ROUTE to NarrowReduction WITHOUT (G): use the mixed p-splits +
  corner transports + flips to normalize z₋'s column support, aiming
  to make 1 + s₁z₋ invertible (or z₋ = 0) reachable.  Note
  z ↦ zp₁ = zs₁t₁ then corner transport 1 + s₁(zs₁)t₁ = κ₁(1 + zs₁)
  gives [1+s₁z] = [1 + zs₁] for MIXED z — the flip — and zs₁ has
  components (zs₁)₋ = z₋s₁... iterate: the composite z ↦ t₁-shifted
  data: TRACK what happens to the negative part under
  z ↦ (the normal form of 1 + zs₁): worth computing whether the
  γ'-obstruction provably shrinks (column-depth of z₋'s 1-rooted
  content) per cycle.  ALSO available now: mixed-z tail support
  reduction means the ENTIRE session-13 loop machinery applies to
  mixed z with more freedom than previously exploited.

## Session 23: dynamics computed; the invariant sharpened to 1 + ẑ
- CORRECTION to session 22: the A-moves change γ' as an ELEMENT but
  not its invertibility class: (z₋(1−p_{0w}))s₁ = z₋s₁ always
  (t_{0w}s₁ = 0), and both old and new γ' are invertible iff
  1 + ẑ is, ẑ := z₋s₁ BALANCED.  So the true obstruction datum is
  the invertibility of 1 + ẑ — invariant under A-moves, prefix
  kills, and the flip (γ ↔ γ' are flip partners of it).
- THE FLIP EATS THE WINDOW: [1 + s₁z] = [1 + zs₁] with
  zs₁ = ẑ + z₀s₁ ∈ [0,1] — no negative part.  If 1 + ẑ invertible:
  factor and flip back ⟹ pure tail ⟹ NilpotentTailKill ⟹ DONE
  (this is GammaReduction, already written).
- CHIRALITY THEOREM (negative): [0,1]-forms with s₁-SUFFIX tails have
  NO mirror p-split (s·t words never vanish; only t·s do) — all
  annihilation-based movers live on the 1 + s₁(·) side.  Return to
  normal form hence requires the sr1-pivot loop.
- TWISTED ACTION found: right-mult by balanced h on v = c + z₀s₁ acts
  as (c, z₀) ↦ (ch', z₀φ₁(h)) via s₁h = φ₁(h)s₁, φ₁(h) := s₁ht₁ —
  wait: v·h = (1+ẑ)h + z₀φ₁(h)s₁ — the pair transforms with the
  CORNER TWIST φ₁ on the tail.  Left-mult: (gc, gz₀).  The
  (g,h)-orbit of (c, z₀) with the φ₁-twist is the corner-skew
  structure at the unit level; φ₁(h) is never invertible (image in
  p₁ corner) — the twist COMPRESSES the tail's right support.
- REMAINING QUESTION (sharpest yet): unit 1 + s₁z with 1 + z₋s₁
  singular: exhibit a move sequence reaching either invertible
  1 + ẑ' or H directly.  Available: M = 1 nonlinear idempotent data
  (P = s₁z₀y₋₁, E = C₁z₀, colsp(C₁) = ker γ', exact rank equalities),
  the twisted (g,h)-action, sr1-pivot loop, deep A-moves.  IDEA for
  next session: use the twisted action with h := suitable balanced
  unit to compress z₀'s right support INTO the corner where the
  M=1-idempotent data lives, making the balanced part invertible on
  the complement — i.e. exploit that φ₁(h)-compression can REMOVE
  exactly the tail content that couples to ker(1+ẑ), decoupling the
  singular part which then must vanish by the unit equations (the
  pure-singular case 1 + s₁z₋ + [tail coupling only to the regular
  part] should force the M=1 system into the instance-1 pattern
  where positive-side equations kill y₀'s p₀-part).

## Session 24: MAJOR — (G) reduced to one finite-dim case; three new theorems
REFORMULATION (P): u = 1+s₁z flips to v = γ + z₀s₁ ∈ window [0,1]
with BALANCED PART γ.  So (G) ⟺ (P): every [0,1]-window unit
w = c + ζ (c balanced, ζ ∈ L₁) has c invertible.  If (P): w = c(1+c⁻¹ζ),
pure positive tail, nilpotent automatically (below), done — NO
dynamics needed, GammaReduction's hypotheses all discharge.

NEW THEOREM 1 (no homogeneous units): L(1,2) has no units of pure
degree d ≠ 0.  Proof: pad w to level matrices: W is 2^p×2^q with
p−q = d ≠ 0; WX = I_{2^p}, XW = I_{2^q} impossible by rank.  Also the
ONE-SIDED version for d ≥ 1: a degree-(+1) element with a RIGHT
inverse of degree −1 is impossible (tall matrix ΞΡ = I_{2D}, rank ≤ D).

NEW THEOREM 2 (automatic nilpotency): unit 1 + ζ, ζ pure positive
degree ⟹ ζ nilpotent.  Proof: inverse x = Σx_d; degree recursion
x_d = δ_{d0} − ζx_{d−1} from the bottom: negative components vanish
(x_m = 0 for m < 0 directly!), x_0 = 1, x_d = (−ζ)^d, finite support
⟹ ζ^{M+1} = 0.  [Formalize via graded decomposition extraction.]

NEW THEOREM 3 (γ upgrade): 1+ẑ (ẑ balanced level q) invertible in L
⟺ invertible in B_q ≅ M_{2^q}(k) (singular matrix ⟹ zero divisor);
inverse automatically balanced.  So GammaReduction's hginv is free.

CORNER NORMAL FORM: mod H (balanced pivot units), any [0,1]-unit
becomes w = e + ζ, e = diagonal cylinder idempotent, f := 1−e.
FULL cross-corner unipotent toolkit: 1 + eηf, 1 + fηe ∈ H for ANY η
(a := eη, b := f, ba = 0 — mem_stableUnits_of_val_unipotent!).

CASE ANALYSIS on x := w⁻¹'s lowest degree m (c singular ⟺ m < 0):
- degree-0 f-compressions (hold for ALL m): (fx₋₁)(ζf) = f and
  (fζ)(x₋₁f) = f.  So ζf INJECTIVE (left-invertible), fζ surjective.
- m = −1: x₋₁ = fx₋₁f (from ex_m = 0 = x_me) ⟹ ξ := fζf is
  INVERTIBLE in corner fLf ≅ (amplified) L, homogeneous degree 1
  ⟹ contradiction by Theorem 1.  **m = −1 IMPOSSIBLE.**
- rank bound (all m): ζ_{fe}(ex₋₁f) + ξ(fx₋₁f) = f = I_{2D} at level:
  rank ≤ E + D ⟹ **E ≥ D: singular balanced part has rank ≥ 1/2.**
- equality E = D: forces Ξ full column rank (injective); but for
  m ≤ −2: x_m = fx_mf ≠ 0 with ξx_m = 0 ⟹ x_m = 0 contra.
  **E = D IMPOSSIBLE for m ≤ −2.**
- REMAINING: m ≤ −2, E > D strictly.  Chain equations: fζx_d = 0 and
  x_dζf = 0 for m ≤ d ≤ −2; im(ζf) ⊆ ker X_d; x_d = β_dx₀ − β_{d+1}x₋₁
  (β_d := x_de) for d ≤ −2, β_m·(from x_me = 0)... plus twisted trace.

MODULAR TRACE: normalized trace τ on L₀ (level-invariant); for
y ∈ L_d, z ∈ L_{−d}: 2^d·τ(yz) = τ(zy) (rectangular trace identity).
Gives τ(ex₀e) = 1 (all char, incl. char 2 — state multiplied form).
No positivity over 𝔽₂ (the MAIN case is 𝔽₂!) so trace alone can't
finish; it's one more constraint on the remaining case.

NEXT: (a) attack m ≤ −2, E > D by the β-recursion + padding rigidity
(the M=1 hand-case died by ⊗I₂-parallelism — generalize); AND
(b) actively search for a counterexample unit (rank e = 3·2^{q}/4,
m = −2 ansatz).  Even if (P) fails, mod-H moves + corner toolkit give
the fallback.  Meanwhile: Theorems 1–3 + corner form are formalizable
NOW and are needed regardless.

## Session 24b: the peeling isomorphism; K₀ is no obstruction; plan
MONOMIAL FACTS (recorded to avoid rederiving): S(a)T(b) nilpotent ⟺
a,b prefix-incomparable (else powers persist: S(a)T(b)² = S(a)T(db)
etc.).  t_is_j = δ_ij means NO t-before-s monomials exist; conjugation
experiments (1+ν)(1+σ)(1−ν) with ν = S(1)T(00), σ = S(00)T(1) give
window [−1,1] with negative part νσν-type surviving — no easy
[0,1]-singular unit from small conjugates (νσ = S(1)T(1), σν =
S(00)T(00), νσν = ν).

PEELING THEOREM (new, verified by direct ring computation): let
w = e + ζ be a unit ([0,1]-window normal form), x := w⁻¹, B := ζf =
wf, b := x₋₁ (so bB = f from the graded equation x₋₁ζf = f, and
x_dζf = 0 ∀d ≠ −1 — refined graded identities, both sides).  Set
P := B·b = ζf·x₋₁: then
  • P is a BALANCED idempotent (deg +1 · deg −1), P·B = B, (1−P)B = 0;
  • τ(P) = τ(f)/2 (modular trace);
  • Φ := (1−P)we : eL → (1−P)L is a RIGHT-MODULE ISOMORPHISM:
    injective: Φy = 0 ⟹ wy = P wy = B(bwy) ⟹ y = (xB)(bwy) = f(bwy)
    and y = ey ⟹ y = 0, using xB = Σx_dζf = f;
    surjective: Φ(ex v) = (1−P)v since (1−P)B = 0.
  ⟹ [e] = [1−P] in V(L).  BUT V(L(1,2))\{0} is the trivial monoid
  (all nonzero f.g. projectives ≅), so NO K₀ obstruction — as
  expected, the content is K₁-level.  Peeling gives a NEW [0,1]-unit
  u'' := (1−P)we + ψ (ψ ∈ PL₁f an explicit cylinder-matching
  partial isometry, degree +1 forced by trace scaling), but defect
  bookkeeping rank((1−P)e) is not guaranteed to improve without
  aligning P with e — open.
DECISION FOR NEXT TURN: settle (P) for m ≤ −2 COMPUTATIONALLY first:
implement exact L_𝔽₂(1,2) arithmetic (dict on word-pairs, prefix
collapse), then for structured/random ζ with e = 1−p₁₁ (E=3, D=1,
q=2) solve the LINEAR system wx = xw = 1 over 𝔽₂ with bounded
monomial support (|a|,|b| ≤ 5, ~4k unknowns, bitset Gaussian
elimination).  A solution = genuine counterexample certificate (then:
moves route with corner toolkit + peeling).  No solutions across the
sweep = strong signal (P) is true ⟹ hunt the proof via peeling
alignment / β-recursion + ⊗I₂ rigidity.

## Session 25: (P) PROVED — the corner-factorization rank argument
**THEOREM (P).**  L_k(1,2) has no unit of the form w = e + ζ with e a
balanced idempotent ≠ 1 and ζ pure degree +1.  Consequently every
[0,1]-window unit has invertible balanced part (rank normal form
C = g·E·h over the balanced matrix algebra reduces c to an idempotent
e mod balanced units, which preserves unit-ness and degree windows).

PROOF.  Let f := 1−e ≠ 0, x := w⁻¹ = Σ_{d=m}^{M} x_d graded.
(1) Graded equations: (A_d) ex_d + ζx_{d−1} = δ_{d0},
    (B_d) x_de + x_{d−1}ζ = δ_{d0}.
(2) Right-multiply (B) by f (ef = 0):  x_dζf = δ_{d,−1}f  ∀d.
    Left-multiply (A) by f:            fζx_d = δ_{d,−1}f  ∀d.  (R2)
(3) Downward expansion from (A) for d ≤ −1 (x_{m−1} = 0):
    x_d = Σ_{j=0}^{d−m} (−ζ)^j (f x_{d−j}).
(4) Substitute (3) into (R2) at d = −1 and right-multiply by f.
    With Y_c := f x_c f ∈ fL_cf and G_j := (−1)^j fζ^{j+1}f ∈ fL_{j+1}f:
        Σ_{j=0}^{−1−m} G_j · Y_{−1−j} = f.        (★)
    (If x has NO negative components the LHS is empty: f = 0, i.e.
    e = 1 — that is the invertible case.  So assume m ≤ −1.)
(5) RANK CONTRADICTION.  Fix level ℓ ≥ (max depth) + |m| + 1 and
    represent corner elements as rectangular matrices between the
    f-supported level spaces (dim D_ℓ = |f|·2^{ℓ−q}, D_{ℓ+c} = 2^c·D_ℓ),
    multiplicatively (prefix collapse = matrix product; f ↦ I_{D_ℓ}).
    Each term G_j·Y_{−1−j} factors V^{(ℓ)} → V^{(ℓ−1−j)} → V^{(ℓ)},
    so rank ≤ D_{ℓ−1−j}.  Hence
      D_ℓ = rank I ≤ Σ_{j=0}^{J} D_ℓ·2^{−1−j} = D_ℓ(1 − 2^{−(J+1)}) < D_ℓ.
    Contradiction.  ∎
Subsumes both the old m = −1 case and the E-vs-D dichotomy — no case
split at all.  Sanity: e = 1 gives D_ℓ = 0 (no contradiction) ✓; the
𝔽₂-computational search (running) expects ZERO hits ✓ to confirm.

CONSEQUENCE CHAIN (all side conditions of GammaReduction discharge):
[0,1]-unit w ⟹ c invertible ⟹ w = c·(1 + η), η := c⁻¹ζ ∈ L₁;
1+η unit ⟹ η nilpotent (Theorem 2, session 24); κ₁-transport
[1+η] = [1 + s₁(ηt₁)] with ηt₁ BALANCED and (s₁ηt₁)^D = s₁η^Dt₁ = 0
⟹ NilpotentTailKill ⟹ **every [0,1]-window unit ∈ H·(scalars)…**
actually ∈ H directly (c balanced-valued unit ∈ H).  Mirror statement
for [−1,0]-window units via the s↔t anti-automorphism (or rerun the
argument on xw-side).

## Session 25b: tree-rebalancers are in H — width-3 obstruction dissolves
- Test element ρ := S(0)T(00) + S(11)T(01) + S(10)T(1): verified
  ρρ' = ρ'ρ = 1 with ρ' the mirror — a genuine width-[−1,1] unit
  (Higman–Thompson/code-change element).  Its balanced part CAN be
  singular for width-3 units (explicit conjugate example, level 2,
  rank 1 of 4) — so (P) does NOT extend to width 3, LDU fails
  (explicit obstruction computed), and pivots are needed.
- **Incomparable unipotents:** for ANY prefix-incomparable words a,b:
  1 + λS(a)T(b) ∈ H via mem_stableUnits_of_val_unipotent with
  α := λS(a), β := T(b), βα = λT(b)S(a) = 0.  ALL degrees at once!
- **Mixed swaps:** σ̃_{ab} := 1 − p_a − p_b + S(a)T(b) − S(b)T(a) =
  (1+e_{ab})(1−e_{ba})(1+e_{ab}) ∈ H (SL₂ swap identity), and the
  sign-fix d := 1 − 2p_b is balanced-valued ∈ H, so the honest swap
  σ_{ab} = 1 − p_a − p_b + S(a)T(b) + S(b)T(a) ∈ H — for any
  incomparable pair a,b, ANY relative depths.
- Higman–Thompson V is generated by such incomparable transpositions
  (comparable moves route through an auxiliary disjoint cylinder,
  3-cycle of swaps) ⟹ ALL code-change units ρ ∈ H.
- REMAINING (the last mathematical gap, now very narrow): width-3 →
  width-2 mod H: show every [−1,1]-window unit reduces, using swaps +
  incomparable unipotents + balanced pivots (Bruhat/LPU over the
  cylinder groupoid), to a [0,1]- or [−1,0]-window unit; then (P)
  chain finishes NarrowReduction, hence ScalarReduction, B4, Theorem C.

## Session 25c: (P) computationally CONFIRMED over F2
Exact L_F2(1,2) arithmetic (scratchpad leavitt_search.py): monomial
prefix-collapse product, stream-module equation generation, linear
solve for bounded-support inverse, EXACT algebra verification of any
solution.  Selftests: relations, t_is_j, known unit/non-unit ✓.
RESULT: e = 1−p₁₁ (singular, rank 3/4): exhaustive over all 1023
nonzero degree-1 perturbations on the 10 shallow monomials (|b|≤1),
plus 100 random deeper samples (|b|≤2, up to 6 terms): ZERO units.
Control with e = 1 and nilpotent tail: unit correctly found.
Matches THEOREM (P) exactly.  The mathematics is settled; remaining
math gap is ONLY width-3 → width-2 (session 25b plan).

## Session 25d: Lean writing begun; exact roadmap for the (P)-chain
WRITTEN (uncompiled, registered in aggregator):
- IncomparableUnipotents.lean: incomparable_unipotent_mem_stableUnits
  (any unit valued 1 + s_a·y·t_b, a,b incomparable, ∈ H);
  incomparableUnit (explicit unit, inverse 1 − s_a y t_b);
  signedSwap := product of three incomparable unipotents ∈ H;
  signedSwap_val = 1 − p_a − p_b + s_at_b − s_bt_a (X/Y collapse
  lemmas hXX hXY hYX hXYX then calc + noncomm_ring).
- ShapeCalculus.lean: shapeMonomials p q; ShapeRep p q M x
  (x = ΣΣ M γ δ • s_γt_δ, index types Fin p → Fin 2);
  shapeRep_mem_span; exists_shapeRep (span_induction; Matrix.single —
  check pin API: `Matrix.single` vs `Matrix.stdBasisMatrix`!);
  shapeRep_entry (t_γ·x·s_δ = algebraMap (M γ δ), via
  prefixCode_orthogonal (fullBinaryCode _)); shapeRep_unique (needs
  hinj : Injective (algebraMap k A)); shapeRep_one (via
  fullBinaryCode_complete; unfolds IsComplete/fullBinaryCode — check
  those defs' exact shapes); shapeRep_mul (quadruple sum collapse);
  span_shapeMonomials_le_succ (trailing-cylinder split; ofFn/snoc
  juggling `List.ofFn_succ'`, `Fin.snoc` — COMPILE-RISK, may need
  hand lemma).

REMAINING LEAN MODULES for the (P)-chain (in dependency order), all
mathematics settled in sessions 24–25:
1. GradedComponents.lean:
   a. exhaustion: ∀ x : A(=BinaryLeavitt k) ∃ lo hi, x ∈ span
      (degreeMonomials lo hi).  Route: RingQuot.mkAlgHom_surjective +
      FreeAlgebra induction; generators s0,s1,t0,t1 ∈ window [−1,1];
      products via window_mul_mem_span; sums via span-window-union
      (monotone: span_degreeMonomials_mono).
   b. component decomposition: x ∈ span(window lo hi) → ∃ y_d ∈
      span(deg d d), x = Σ_{d=lo}^{hi} y_d (span_induction).
   c. uniqueness of components (graded_independence_all) + extraction
      lemma: two window elements equal ⟹ components equal.
2. PureTailNilpotency.lean (THEOREM 2): u unit, ↑u = 1 + η,
   η ∈ span(deg 1 1) ⟹ ∃ D, η^D = 0.  Decompose u⁻¹ by (1);
   componentwise equations of u⁻¹·(1+η) = 1 and (1+η)u⁻¹ = 1;
   downward induction kills negative components (x_m = 0 for m < 0
   directly from x_m + ηx_{m−1} = 0 chain bottom-up: at the LOWEST m:
   x_m = 0 if m<0 — careful: equation at degree m is x_m + ηx_{m−1}
   = δ_{m0} with x_{m−1} = 0); then x_0 = 1, x_d = (−η)^d, top:
   η·x_M = 0 gives η^{M+1} = 0.
3. RankNormalForm.lean (THEOREM 3 + normalization): c ∈ span
   (levelMonomials q):
   a. IsUnit c ↔ IsUnit (its balancedEmbed matrix) — have
      exists_balancedEmbed_eq + injectivity + multiplicativity in
      BalancedStableRank; inverse stays balanced.
   b. c = g·e·h with g,h balanced-VALUED units of A and e a 0/1
      diagonal cylinder idempotent (Matrix.Pivot diagonal + absorb
      units into diagonal scaling).
4. ZeroKOne.lean (THEOREM (P), the keystone):
   statement: [Nontrivial A] (hdiv …) {c ζ : A} (hc : c ∈ span deg 0 0)
   (hζ : ζ ∈ span deg 1 1) (u : Aˣ) (hu : ↑u = c + ζ) : IsUnit c.
   Proof skeleton (sessions 24/25, VERIFIED numerically):
   - normalize c = geh (3b); pass to unit w := g⁻¹uh⁻¹-value e + ζ'.
   - suppose e ≠ 1 (else done).  x := w⁻¹; decompose (1); graded
     equations; (R1/R2): x_dζf = δ_{d,−1}f, fζx_d = δ_{d,−1}f
     (f := 1−e); downward expansion x_d = Σ_j (−ζ)^j f x_{d−j};
     corner system Σ_j G_j Y_{−1−j} = f, G_j := (−1)^j fζ^{j+1}f,
     Y_c := fx_cf.
   - shapes: pick interface ℓ big; G_j ∈ span(shape ℓ (ℓ−1−j)), Y_c ∈
     span(shape (ℓ−1−j) ℓ) (padding); exists_shapeRep; shapeRep_mul;
     f's canonical matrix at (ℓ,ℓ) is 0/1-diagonal with D_ℓ = |T|·2^{ℓ−q}
     ones; shapeRep_unique identifies Σ M(G_j)M(Y_j) with it.
   - rank: D_ℓ = rank(diag) ≤ Σ_j rank(M(G_j)M(Y_j)) ≤ Σ_j 2^{ℓ−1−j}
     ≤ 2^ℓ − 2^{ℓ−1−J}.  Wait — need the SHARPER f-corner bound only
     if e-rank enters; actually the plain bound suffices when f = 1…
     NO: correct bound: rank ≤ min dims = card(Fin (ℓ−1−j) → Fin 2)
     = 2^{ℓ−1−j}, and D_ℓ ≥ 2^{ℓ−q} ≥ … CHECK: need Σ_j 2^{ℓ−1−j} <
     D_ℓ?  D_ℓ = |T_f|2^{ℓ−q} with |T_f| ≥ 1: Σ_{j=0}^{J}2^{ℓ−1−j} =
     2^ℓ−2^{ℓ−1−J} which EXCEEDS D_ℓ when f is small — MUST use the
     corner-supported rank bound: Y_c = f·x_c·f ⟹ M(Y_c) = M(f at
     (ℓ−1−j))·M(x-part) ⟹ rank ≤ rank M(f at ℓ−1−j) = D_{ℓ−1−j};
     then Σ_j D_{ℓ−1−j} = D_ℓ(1−2^{−(J+1)}) < D_ℓ ✓.  (Session 25
     proof used exactly this; keep f-factorization of Y explicit.)
   - Mathlib rank lemmas: Matrix.rank_mul_le_left/right,
     rank_add_le (check name; else via LinearMap.range sup),
     rank_diagonal, rank_one.
5. WidthTwoReduction.lean: every unit with value ∈ 1 + span(window
   [0,1])… general: value ∈ span(window 0 1) ⟹ u ∈ stableUnits:
   (P) → c unit → c-balanced-valued ∈ H (mem_stableUnits_of_val_mem_
   levelSpan via span_degree_zero_le_levelSpan); tail 1 + c⁻¹ζ:
   Theorem 2 nilpotency; κ₁-transport (pairKappaUnit s₁ t₁) to
   1 + s₁(ηt₁) with ηt₁ balanced (window mult); nilpotency transports
   ((s₁ηt₁)^D = s₁η^Dt₁); NilpotentTailKill.  Mirror [−1,0] version
   via the same argument on the anti-side OR omit (probably only one
   side needed).
6. Width-3 → width-2: MATH STILL OPEN (session 25b: Bruhat/LPU with
   swap pivots; swaps now ∈ H).  THE remaining mathematical gap.
   After it: NarrowReduction ⟹ ScalarReduction (ResidualReduction
   wiring, written) ⟹ B4 ⟹ Theorem C.

## Session 25e: GradedComponents.lean written
- exists_components: window element = Σ_{d ∈ Icc lo hi} y d with
  y d ∈ span(deg d d), vanishing outside window (span_induction;
  if-then-else component functions; Finset.sum_eq_single).
- components_unique: via graded_independence_all on differences.
- exists_mem_span_degreeMonomials ALREADY EXISTS (BinaryLeavittWindow,
  compiled green) — exhaustion is done.
- NEXT MODULES TO WRITE (roadmap in 25d): PureTailNilpotency (use
  exists_components on u⁻¹ + components_unique on the product
  equations — the product of window elements decomposes via
  window_mul_mem_span then extract componentwise equations by
  comparing the two decompositions of ↑u·↑u⁻¹ = 1);
  RankNormalForm; ZeroKOne (the (P) keystone); WidthTwoReduction;
  then the width-3 math.

## Session 26: PureTailNilpotency + RankNormalForm written
- PureTailNilpotency.lean (Theorem 2 formalized): widen inverse's
  window to lo ≤ −1 ≤ 0 ≤ hi; exists_components on ↑u⁻¹; two
  decompositions of 1 over Icc lo (hi+1) (shifted sum via
  addRightEmbedding + Finset.map_add_right_Icc + insert-argument);
  components_unique; upward kill of negatives (ℕ-indexed induction
  from lo); y 0 = 1; y n = (−η)^n; top equation ⟹ η^(hi.toNat+1) = 0
  (even/odd sign handling via Even.neg_pow/Odd.neg_pow).
  NAME RISKS for sweep: Finset.sum_ite_eq' arg order,
  Finset.map_add_right_Icc, addRightEmbedding simp,
  add_eq_zero_iff_eq_neg, pow_succ' direction, neg_mul_eq_neg_mul.
- RankNormalForm.lean: balancedEmbed_diagonal (diagonal ↦ weighted
  cylinder sums via matrixRingEquiv_diagonal + diagonal_map);
  balancedEmbed_indicator (Finset.sum_ite_mem + univ_inter);
  isUnit_matrix_of_isUnit (singular ⟹ zero divisor via
  Matrix.exists_mulVec_eq_zero_iff, all-columns-v matrix X);
  inv_mem_levelSpan_of_val_mem (THEOREM 3: balanced units have
  balanced inverses — inverse-uniqueness calc);
  exists_rank_normal_form (Pivot decomposition, D = D₁·E splitting,
  transvection products invertible via det route, g/h :=
  Units.map balancedEmbed of Pu⁻¹/Qu⁻¹, value = cylinder sum over
  S := filter (dvec ≠ 0), S = univ → IsUnit c).
  NAME RISKS: Matrix.exists_mulVec_eq_zero_iff (field/domain +
  direction), Matrix.TransvectionStruct.prod_mul_reverse_inv_prod,
  Units.map_inv direction, Matrix.dotProduct vs dotProduct in simpa,
  RingHom.mapMatrix_apply, Matrix.diagonal_map hypothesis.
- Registered in aggregator.  NEXT: ZeroKOne.lean (the (P) keystone —
  see 25d roadmap step 4), then WidthTwoReduction, then width-3 math.

## Session 27: THE KEYSTONE IS WRITTEN — ZeroKOne.lean and supports
- DegreeShapeBridge.lean: exists_ofFn_eq, monomial_mem_shapeSpan
  (r-induction over trailing pads), exists_shapeSpan_of_degreeSpan
  (uniform interface thresholds via span_induction + max),
  shapeRep_add, shapeRep_finsetSum, rank_finsetSum_le
  (RISKS: Matrix.rank_add_le, Matrix.rank_zero, Finset.induction_on
  case-binder names).
- CylinderCornerRank.lean: appendFun + ofFn_appendFun
  (List.ext_getElem / getElem_ofFn / getElem_append — API RISK),
  appendFun_injective, wordT_cylSum_wordS (full delta computation),
  cylSum_mem_shapeSpan, card_le_rank_of_shapeRep_cylSum (U·M·V = 1
  certificate over {γ // γ ∈ T} × (Fin (ℓ−n) → Fin 2); rank_one,
  rank_mul_le_left/right, Fintype.card_fun), and
  rank_le_card_of_shapeRep_cylSum (per-cylinder s_γ·t_γ isometry
  factorization; rank_le_card_width RISK).
- ZeroKOne.lean: balanced_component_isUnit — the FULL (P) proof:
  by_contra; rank normal form ⟹ e, f = Σ_T cylinders, T ≠ ∅;
  hcyl/hfe/hff orthogonality; w := g·u·h with value e + ζ';
  graded components of w⁻¹ + componentwise equations (same
  sum-splitting pattern as PureTailNilpotency); hsubst
  (y d = f·y d − ζ'·y (d−1) for d ≤ −1, both in-window and
  out-of-support cases); the remainder induction hclaim
  (GG j := f·ζ'·(−ζ')^j, YY j := f·(y(−1−j)·f) — NOTE: GG has NO
  trailing f so the induction is pure noncomm_ring + pow_succ; hff
  needed only in the base case); termination at M := (−lo).toNat;
  interface ℓ := n + M + 1 + B (B := sup of shape thresholds);
  dependent choose over range M with attach-sums (Finset.sum_attach);
  lower bound via card_le_rank_of_shapeRep_cylSum, upper via
  factor-through-Mf; geometric-sum contradiction (sum_range_reflect,
  sum_two_pow, mul_lt_mul_of_pos_left, pow_pos).
  RISKS: Finset.sum_ite_eq' arg-order, Finset.sum_mul_sum shape,
  add_eq_zero_iff_eq_neg, attach/sum_attach forms, set-vs-rw
  interactions, `simp only [] at` beta-reduction usages.
- All registered in aggregator.  REMAINING: WidthTwoReduction.lean
  (assembly: (P) + Theorem 3 + κ₁-transport + NilpotentTailKill ⟹
  every [0,1]-window unit ∈ H); the width-3 → width-2 mathematics;
  then NarrowReduction assembly and the compile-and-fix sweep.

## Session 27b: WidthTwoReduction written — the (P)-chain is complete in Lean
- WidthTwoReduction.lean: window_zero_one_mem_stableUnits — full
  assembly: components split (Icc 0 1 = {0,1});
  balanced_component_isUnit; balanced unit uc ∈ H with balanced
  inverse; residual v := uc⁻¹u value 1 + η; pure_tail_nilpotent;
  κ₁ := pairKappaUnit s₁ t₁ transport to 1 + s₁(ηt₁) (balanced,
  nilpotency transported via (s₁ηt₁)^{m+1} = s₁η^{m+1}t₁);
  nilpotent_tail_mem_stableUnits; assembly u = uc·(κv⁻¹)⁻¹·κ.
  hdiv from LeavittSimplicity.exists_mul_mul_eq_one (implicit-x
  signature: exists_mul_mul_eq_one k hx).
  RISKS: t_one_mem_window name, pairKappaUnit explicit-arg order.
- STATUS: the entire width-2 story is now WRITTEN in Lean end-to-end:
  ZeroKOne (P) → RankNormalForm (Thm 3) → PureTailNilpotency (Thm 2)
  → κ-transport → NilpotentTailKill → H.  What remains
  mathematically: ONLY width-3 → width-2 (narrow units to [0,1] or
  [1 + s₁z] form mod H).  Then: NarrowReduction := width-3 step +
  window_zero_one_mem_stableUnits (+ flip for [−1,0]-forms if
  needed); ScalarReduction wiring already written
  (ResidualReduction); then B4; then the single compile-and-fix
  sweep over all uncompiled modules (list: ResidualMoves,
  ResidualReduction, BalancedRegularity, TailSupportReduction,
  WindowProductClosure, NilpotentTailKill, GammaReduction,
  IncomparableUnipotents, ShapeCalculus, GradedComponents,
  PureTailNilpotency, RankNormalForm, DegreeShapeBridge,
  CylinderCornerRank, ZeroKOne, WidthTwoReduction).

## Session 28: width-3 analysis sharpened (math turn)
- NEW STRUCTURAL FACT (corollary of (P)!): right- or left-
  multiplication by [0,1]-window H-units can NEVER kill a nonzero
  degree-(−1) part: (u·m)₋ = u₋·m₀ and m₀ is INVERTIBLE by (P).
  So width-3 → width-2 requires movers with genuine negative parts:
  the incomparable unipotents 1 + S(α)yT(β), |β| > |α| (∈ H ✓), and
  their products, plus two-sided balanced units.
- Canonical form for the bottom: rank-normalize a's rectangular
  coefficient matrix (balanced g·a·h): WLOG a = τ_r = Σ_{i<r}
  S(α_i)T(β_i), canonical partial isometry (orthonormal families).
- c-invertible sub-case: u ~ 1 + A + B (A := c⁻¹a).  If A nilpotent
  with (1+A) ∈ H then (1+A)⁻¹u = 1 + (1+A)⁻¹B still has negative
  parts from the inverse tail ((−A)^jB ∈ L_{1−j}) — one-sided
  clearing insufficient.  LDU needs Riccati C'(1+C') = −AB
  (Artin–Schreier over 𝔽₂ — not always solvable): exact LDU fails,
  mod-H version open.
- NEXT SESSION PLAN:
  1. COMPUTATIONAL probe (leavitt_search.py is ready): (a) do
     width-3 units with invertible c always have nilpotent c⁻¹a?
     (test 1 + t₀ + B ansatz over 𝔽₂); (b) explicitly H-reduce the
     rebalancer ρ = S(0)T(00)+S(11)T(01)+S(10)T(1) by hand/machine
     to discover the general move pattern (ρ IS in H by K₁ = 0; find
     the witness!).  ρ's reduction pattern likely IS the algorithm.
  2. Try: u·(1+ν) with ν = −ρ₀-pattern... general scheme: mixed
     unipotent right-movers 1 + ν (ν ∈ L₋₁, monomial-incomparable
     form) change a by c·ν (constraint a·ν = 0) — set up the
     linear-algebra of {ν : aν = 0} acting on a via c·ν, iterate
     with balanced renormalizations; measure: rank r of a.
  3. Remember: [−1,0]-window units ∈ H by the MIRROR of the width-2
     chain (s↔t antiautomorphism — formalizable as the op-algebra
     family or by rerunning the argument on xw = 1 side).

## Session 29: EXPLICIT H-witness for the rebalancer; (P) generalizes to [0,N]
- COMPUTED BY HAND (exact monomial calculus, verified stepwise):
  ρ = S(0)T(00) + S(11)T(01) + S(10)T(1) (the basic tree rebalancer),
  σ₁ := swap(01, 1) (incomparable ✓ ∈ H), σ₂ := swap(00, 1)
  (incomparable ✓ ∈ H):
    ρ·σ₁ = S(0)T(00) + S(11)T(1) + S(10)T(01)
    ρ·σ₁·σ₂ = S(0)T(1) + S(10)T(01) + S(11)T(00)  — ALL BALANCED!
  Hence ρ = (balanced unit)·σ₂·σ₁ ∈ H.  **Explicit witness found.**
- THE SWAP-MOVE CALCULUS (general step): right-mult by σ_{β,w}
  (|w| = |β|−1, w incomparable to β): kills a's β-column
  (S(α)T(β) ↦ S(α)T(w), balanced), constraints: a·p_w = 0 (else
  deg −2 junk) and c·p_w = 0 (else NEW deg −1 junk c·S(w)T(β));
  b's β-column up-shifts to degree +2 — so the cascade lands in
  window [0,2], NOT [0,1].
- **(P) GENERALIZES TO [0,N] WINDOWS** (derivation done): for
  w = e + ζ₁ + … + ζ_N, the downward elimination with GROUPED
  coefficients gives f = Σ_{c≤−1} H_c·(f x_c f), H_c ∈ f·L_{−c}·f a
  SINGLE element per degree (sum over composition paths — grouping
  is essential: raw term-counting gives Fibonacci growth and fails);
  the rank argument is unchanged: Σ_c D·2^c < D.  COROLLARIES:
  (i) no units with all-positive windows (e = 0 case);
  (ii) [0,N]-unit ⟹ balanced part invertible.
  Lean note: ZeroKOne's induction needs upgrading from single
  remainder to remainder-per-depth (vector/strong induction) for
  general N — or a separate ZeroKOneN module; N = 2 would suffice.
- REMAINING GAPS in the width-3 plan: (a) free-cylinder supply for
  the swap cascade: need w with a·p_w = 0 AND c·p_w = 0 — after
  rank-normalizing c → e, free-for-c columns are Sᶜ but a's columns
  may cover them; need a pre-move to shrink/align a's column support
  (candidates: prefix kills a ↦ a·(1−p), balanced right-units,
  a's OWN rank normal form τ_r with column family orthogonalized —
  note a·h-normalization changes column support freely!
  a-CANONICAL: a = τ_r = Σ S(α_i)T(β_i): columns = the β-family,
  SMALL (r of them) — then need e's support to avoid β's: e·p_{β_i}
  = 0 ⟺ β_i ∈ Sᶜ-cylinders... adjust by swapping WITHIN balanced
  (permutation units) to relocate Sᶜ onto the β-family?? — the
  β-family sits at depth m+1, S at depth n: refine and match counts:
  |Sᶜ|·2^{m+1−n} ≥ r needed — rank inequality!  This smells like
  exactly the E ≥ D bound from session 24.  DERIVE next session.);
  (b) tail-kill for [0,2]: 1 + η₁ + η₂ ∈ H (κ-transport gives
  z := (η₁+η₂)t₁ ∈ [0,1] NOT balanced — NilpotentTailKill needs an
  upgrade to mixed nonneg tails, or a two-step split).
- The endgame is now a bounded list of concrete lemmas.  NO open
  conceptual mysteries remain — all remaining items have identified
  attack routes.

## Session 29b: [0,2]-tail-kill (B2) reconnaissance
- Unit 1 + τ (τ ∈ [1,N]) has pure-nonneg inverse 1 + τ' with x₀ = 1
  (bottom-up recursion — same as PureTailNilpotency's first half).
- Circularity check: κ-transport → p-split → prefix-kill → corner
  transport returns exactly to 1 + τ (t₁s₁ = 1 collapses zs₁ = τ).
  Flips conserve the window under every row/column split tried
  (first-letter, last-letter, depth-N splits all return [1,N]).
- Corner-localization: κ₁₁-transport (pair S(11), T(11)) puts the
  tail in the p₁₁-corner; right-mult by ν := S(0)yT(11β′) acts as
  PURE ADDITION ((κv)ν = ν since T(11)S(0) = 0); left-mult mixes via
  T(β′)τ.  Free-corner arithmetic is available but no kill found yet.
- MOST PROMISING for (B2, N = 2): generalize NilpotentTailKill's
  induction (lemma i′) to mixed z ∈ [0,1]-window tails 1 + s₁z:
  the p-split z ↦ zp₁ is free for mixed z (session 22), and the
  pseudo-inverse/mover machinery (BalancedRegularity) needs the
  balanced PART of z only — investigate whether the index-drop
  recursion survives with the degree-1 part of z along for the ride.
  Alternatively: (B2) via the session-22-style unipotent factor
  1 − s₀a₀t₁ (∈ H, βα = t₁s₀a₀ = 0) which keeps windows nonneg —
  look for the right composite.
- Meta-status: remaining math = (a) free-cylinder supply for the
  swap cascade (rank-inequality flavored, session 24's E ≥ D bound
  is the template) + (B2, N = 2).  Both concrete, both bounded.

## Session 30: the stable block-move calculus for width-3
- KEY IDENTITY (elementary, two E-ops, all sizes): for ANY unit u and
  any row P, column Q: [diag(u, I)] = [[[u − PQ, −P],[Q, I]]] mod E.
  (M₀ = diag(u,I); right-mult E₂₁(Q): [[u,0],[Q,I]]; left-mult
  E₁₂(−P): [[u−PQ, −P],[Q, I]].)
- Applied with the RIGHT-split of the negative part w₋ = Σ(w₋sᵢ)tᵢ
  (P := (w₋s₀, w₋s₁) balanced row, Q := (t₀; t₁)):
  M₁ := [[w − w₋, −C₀, −C₁],[t₀, 1, 0],[t₁, 0, 1]] — the negative
  content of the class becomes EXACTLY the canonical column (t₀; t₁).
- MIXED-DEPTH TRANSPORT: through prefixMatrixFamily with a complete
  code of lengths (ℓ₁, ℓ₂, ℓ₂), entry (i,j) picks up degree ℓᵢ − ℓⱼ.
  CONSERVATION OBSTRUCTION: any split w₋ = PQ has deg P + deg Q = −1,
  and transport shifts P, Q degrees oppositely — P and Q can never
  both land in [0,1] in ONE move.  With Q-fix (ℓ₂ = ℓ₁ + 1) the
  C-entries land at degree −1; with P-fix the t's stay at −1.
- Col-op kills of the t-column against the I-block exactly undo
  move 1 (trivial circle); row-op kills need inverting non-units;
  support-shrinking subtraction (row₂ −= (t₀s₁)row₃) does not
  terminate.  Iterating the block-move relocates the t-column
  forever (Sisyphus) — monotone depth assignments contradict.
- CONVERGENCE: everything reduces to ONE normalization: make the
  C-row vanish against the code — i.e. pre-kill w₋'s column content
  outside a controlled cylinder set, using (i) rank-normalization
  w₀ → e, (ii) mixed unipotents u(1+ν) shifting w₋ by e·ν (e-row
  content controllable), (iii) the free-cylinder supply question =
  session-24's E ≥ D rank bound.  If w₋ can be arranged with
  C₁ = 0 (single-branch: w₋ = C₀t₀, i.e. w₋p₁ = 0), then code
  (ℓ, ℓ+1, ℓ) — u-block ℓ, t₀-block ℓ+1, spare ℓ — puts M₁ entries:
  X: [0,1] ✓, −C₀ at (1,2): ℓ−(ℓ+1) = −1 ✗ ... still blocked; but
  C₀ = w₋s₀ and single-branch w₋ = C₀t₀ allows instead P := (w₋),
  Q := (t₀) 1×1-split: M₁ = [[w − w₋, −w₋],[t₀, 1]]: (1,2)-entry
  w₋ degree −1 at code (ℓ, ℓ+1): −1 + ℓ − (ℓ+1)?? no: (1,2): ℓ₁−ℓ₂ +
  (−1) = −2 ✗; code (ℓ+1, ℓ): (1,2): +1−1 = 0 ✓✓ (2,1): ℓ−(ℓ+1)−1 =
  −2 ✗.  STILL conserved.  → The block-move ALONE cannot do it; must
  be combined with genuine content-kills (swap cascade / e-row
  unipotents).  NEXT: formalize-friendly plan: (1) rank-normalize
  w₀ → e; (2) use e-row unipotents + swaps to force w₋ = e·w₋ and
  w₋-columns inside Sᶜ-free-cylinders (supply from |Sᶜ|-count vs
  rank w₋ ≤ ... session-24 E ≥ D!); (3) THEN the swap cascade
  (session 29) balances w₋ term by term without new negatives
  (constraints a·p_w = 0, e·p_w = 0 satisfiable by construction);
  (4) land in [0,2]; (5) (P)-N=2 + B2-N=2.  And B2-N=2 itself:
  revisit via the SAME block-move: 1 + η₁ + η₂: P := (s₀,s₁)·η-split
  top-down: [diag] ~ [[1+η₁, −P'],[Q', I]] with P' ∈ L₁-entries,
  Q' = (t·η₂) ∈ L₁-entries: ALL ENTRIES [0,1]-window ALREADY —
  deg P' + deg Q' = +2 splits as 1+1 ✓✓ NO obstruction for the
  POSITIVE side!!  **B2-N=2 SOLVED**: η₂ = Σᵢ sᵢ(tᵢη₂), P := (s₀,s₁)
  (deg 1), Q := (t₀η₂; t₁η₂) (deg 1): M₁ = [[1+η₁, −s₀, −s₁],
  [t₀η₂, 1, 0],[t₁η₂, 0, 1]]: window [0,1] entrywise; transport via
  EQUAL-depth code (any 4-code, pad to M₄ with 2-deep words): entries
  keep [0,1]; matrixRingEquiv → [0,1]-window unit of L →
  WidthTwoReduction → ∈ H; descent: mem_stableUnits_of_cornerDiag /
  glFour-machinery relates [diag(v, I₃)] to [v].  Same for all N by
  induction (top-split drops window by one each time).
  **THE (B2) GAP IS CLOSED.**

## Session 30b: negative-side analysis; conservation law; test queue
- CONSERVATION LAW (proved): under E-block-moves + mixed-depth
  transport, the sum of entry-degrees around any directed cycle of
  the block structure is invariant; DIAGONAL entries' degrees are
  absolutely invariant.  So negative content can never be removed by
  block-moves/transport alone — genuine content-kills (swaps, e-row
  unipotents) are required.  (Positive-side B2 escaped because
  deg-sum +2 splits into two nonneg slots.)
- Case c invertible (e = 1): swap cascade blocked (no free columns:
  c = 1 has full support).  HOPE: A := c⁻¹·w₋ is NILPOTENT for units
  1 + A + B (then 1+A ∈ H by mirror width-2; but naive factoring
  widens the window — needs care even if true).
  Graded equations give: A x_m = 0, x_m = −A x_{m+1},
  (1 − BA) x_{m+1} = −A x_{m+2}, … — nilpotency-flavored.
- COMPUTATIONAL QUEUE (leavitt_search.py ready, run next turn):
  (1) is 1 + s₀ + t₀ a unit in L_F2(1,2)?  (Toeplitz symbol says no
  within ⟨s₀,t₀⟩, but L(1,2) is simple — inverse could use s₁,t₁!)
  (2) search units 1 + A + B with A non-nilpotent (A = t₀-ansatz,
  random B); (3) if all A's nilpotent: conjecture + prove via the
  graded chain; (4) exhaustive small-window [−1,1]-unit census to
  map the singular-c stratum.

## Session 31: computational evidence + the A-nilpotency conjecture
- 1 + s₀ + t₀ is NOT a unit (B=4,5 both fail) — consistent with the
  Toeplitz symbol heuristic even inside simple L(1,2).
- 10/10 randomly-found width-3 units 1 + A + B have NILPOTENT A
  (all index 2); 180 adversarial trials with forced comparable
  monomials (S(0)T(00), t₀, S(1)T(11)) in A: ZERO units.
- CONJECTURE (A-nilp): 1 + A + B unit ⟹ A nilpotent.  Proof
  candidates: (i) T-deformation: U := A + T + T²B is a unit of
  L_{k(T)} (scalar·scaling-automorphism image); clearing
  denominators U·Ṽ = q(T)·1 in L_k[T]; specialize/valuate at T = 0;
  (ii) (P)-style rank argument on the two-sided graded recursion
  A x_{d+1} + x_d + B x_{d−1} = δ_{d0}.
- Under positive-unipotent movers (1+τ, τ ∈ [1,N]) u₋ is INVARIANT
  (both sides); balanced movers act by u₋ ↦ g u₋ h; only swaps and
  negative-unipotents genuinely change u₋.
- NEXT: BFS/greedy move-search engine over H-moves (swaps, balanced
  pivots, unipotents) on the 10 instances + ρ: extract the general
  reduction algorithm from machine-found witnesses, then prove
  termination.  This closes the last math gap empirically first.

## Session 31b: the Ω-homogeneous cofactor system for A-nilpotency
- U := A + T·1 + T²B ∈ L_k[T] is HOMOGENEOUS of weight 1 for the
  grading Ω := deg_T − deg_L.  From unit-ness over k(T): clearing
  denominators UṼ = ṼU = q(T)·1 and PROJECTING onto Ω-components:
  for ANY j with q_j ≠ 0 there is an Ω-homogeneous two-sided
  cofactor P with U·P = P·U = T^j·1.
- Choosing j := r := ord_T(q): r ≥ 1 is FORCED — r = 0 would make U
  invertible in L_k[T], and T := 0 gives A two-sided-invertible of
  pure degree −1, contradicting no-homogeneous-units.  ✓
- The cofactor system (P = Σ T^i P_i, P_i of L-degree i−r+1):
    A·P_i + P_{i−1} + B·P_{i−2} = δ_{ir},   (two-sided versions)
  with A·P₀ = P₀·A = 0 at the bottom and the window finite — the
  same shape as the (P)-corner system with A in the pivot slot.
  REMAINING: extract A-nilpotency (or directly 1+A+B ∈ H) from this
  system by the rank/factorization method; the specialization
  T := 0 of U·P = T^r·1 gives A·P(0)... wait P(0) = P₀: A·P₀ = 0 —
  consistent; the content is in the higher T-coefficients.
- Alternative still open: BFS move-search engine to machine-discover
  H-reduction witnesses for the 10 concrete instances (swaps +
  balanced pivots + unipotents), then generalize.  ENGINE NEXT TURN.

## Session 31c: A-nilpotency — the toy case resolves; BVP structure
- B = 0 toy: U = A + T: polynomial cofactor P with (A+T)P = T^r
  forces P_i = ±A^{r-1-i} by the (now clean, first-order) downward
  recursion, and the bottom boundary A·P₀ = 0 gives **A^r = 0** —
  the mechanism works exactly.  Conversely non-nilpotent A (e.g. t₀)
  makes A+T non-invertible over k(T) (graded independence of powers
  blocks resummation).
- General B ≠ 0: the system A P_i + P_{i-1} + B P_{i-2} = δ_{ir} is
  a two-point BOUNDARY VALUE problem (the BP_{i-2} term refers
  downward), not a recursion; the cofactor P is UNIQUE (U regular);
  boundary: A P₀ = P₀ A = 0.  The claim A^r-ish = 0 should follow
  from solvability + uniqueness + the bottom boundary — likely via
  eliminating B by the SAME grouped-coefficient trick as (P)-N≥2
  (group all paths reaching depth i into a single coefficient).
  Concretely: iterate the substitution P_{i-1} = δ − AP_i − BP_{i-2}
  into itself to express P_{-1} = 0 as (grouped polynomial in A, B
  acting on seeds) — the resulting identity at the bottom is the
  nilpotency statement.  FINISH NEXT TURN.

## Session 32: THE COMPILE SWEEP IS DONE — full tree GREEN (3723 jobs)
All ~20 previously-unverified modules now compile with
-DwarningAsError=true, INCLUDING:
- NilpotentTailKill (lemma i′), GammaReduction, TailSupportReduction,
  ResidualMoves, ResidualReduction, WindowProductClosure,
  BalancedRegularity, IncomparableUnipotents,
- ShapeCalculus, GradedComponents, DegreeShapeBridge,
  CylinderCornerRank (both rank certificates),
- PureTailNilpotency (Theorem 2), RankNormalForm (Theorem 3),
- **ZeroKOne (THEOREM (P)) — the manuscript's [ABC09] K₁-input
  replacement is now MACHINE-VERIFIED**,
- WidthTwoReduction (window_zero_one_mem_stableUnits) — the complete
  width-2 chain, first-try green.
Fix-log highlights (for future reference): z₋-subscript-minus is not
a valid Lean ident; beta-redexes block rw after refine-with-lambda
(beta_reduce); noncomm_ring CANNOT float -1• out of mid-product
factors — isolate negation in pure-rewrite pow-identities
(hpow0-pattern) and distribute subs with mul_sub/sub_mul + congr
before noncomm_ring; Even.neg_pow needs explicit base arg;
prefixCode_orthogonal needs an ofFn-typed have-binding;
obtain-destructuring clears the source hypothesis;
Matrix rank_add_le doesn't exist at pin (proved matrix_rank_add_le
via finrank_sup_add_finrank_inf_eq + finrank_mono);
exists_mulVec_eq_zero_iff lives in ToLinearEquiv;
isUnit_of_mul_eq_one absent — det-route via
left_ne_zero_of_mul_eq_one; Units.coe_map_inv not map_inv;
Int intervals: Mathlib.Data.Int.Interval.
AUDIT: full build green; audit flags = exactly the width-3 frontier:
LAUNDERED_PROP [NarrowReduction def], UNUSED [rank-normal-form &
pseudo-inverse chains awaiting the final wiring], STALE_DISCLAIMER
[3 main-theorem docstrings to update at assembly time].
REMAINING: width-3 math (A-nilpotency finish + swap-cascade supply),
its formalization, NarrowReduction proof + assembly, docstring
updates, final audit.

## Session 33: B2-N=2 is fully formalizable with COMPILED tools; H is normal
- KEY REALIZATION: the commutator lemma is already formalized
  (commutator_mem_elementaryGroup_of_division): H ⊴ Units and
  Units/H is ABELIAN — free rearrangement of products mod H.
  (Scaling-automorphism tricks die over 𝔽₂: k* trivial.)
- B2-N=2 FORMALIZATION ROUTE (all ingredients compiled TODAY):
  v = 1 + η₁ + η₂ ⟹ M₄-matrix M := E₁₂(−P)·diag(v,I₃)·E₂₁(Q),
  P := (s₀,s₁,0), Q := (t₀η₂; t₁η₂; 0): entries in window [0,1];
  transport via the EQUAL-depth code {00,01,10,11} (matrixRingEquiv,
  formalized): û has value in span[0,1] ⟹ WidthTwoReduction ⟹ H;
  diag(v,I₃)-descent via pairKappa/cornerDiag machinery (formalized);
  elementary factors via transvection-pullback (formalized).
  Degree-shift embeddings CANNOT exist (ring homs preserve 1; any
  (s,t) with ts = 1 has balanced degree) — confirmed the transport
  must use equal depths for nonneg windows, mixed depths otherwise.
- Conservation law re-confirmed on 4-element mixed-depth codes
  ({0,10,110,111}): the direct block-move on the NEGATIVE part
  remains impossible (C-row and t-column degrees sum to −1 around
  the cycle).  The negative side genuinely requires content-kills:
  A-nilpotency (cofactor BVP, toy case done) + swap-cascade supply.
- NEXT CONCRETE STEPS: (1) write BlockMoveTailKill.lean (B2-N=2 as
  above — mechanical, all deps green); (2) finish A-nilpotency via
  the grouped-coefficient elimination on the cofactor BVP;
  (3) mirror width-2 chain ([−1,0]-windows) — either θ-antiauto
  formalization or rerun of the chain on the xw-side;
  (4) singular-c width-3 assembly (swap cascade with supply from
  E ≥ D-rank-bound); (5) NarrowReduction wiring, docstrings, audit.

## Session 33b: BVP notes for the fresh session
- Upward elimination of the cofactor BVP produces
  1 = A·P_r + (1−BA)·P_{r−1} − B²P_{r−3} + ... with B^{2j}·A-middle
  terms — A not left-factorable; elimination alone insufficient.
- Modular trace in char 2: τ(AP_r) = τ(BP_{r−2}) = 0 (doubling dies),
  so (L_r) gives τ(P_{r−1}) = 1 — the balanced middle coefficient has
  full normalized trace.  One more constraint for the rank attack.
- The decisive step is expected from combining: degrees of P_i
  (P_i ∈ L_{i−r+1}, so the BOTTOM half P₀..P_{r−2} has negative
  degrees = SHAPE-SHRINKING maps), the boundary AP₀ = P₀A = 0, and
  the shape-rank method: at level ℓ, express the identity-block
  certificate of 1 (from L_r) through composites that factor through
  the bottom chain — mirror of the (P)-argument with the roles of
  raising/lowering swapped.  START HERE NEXT SESSION.

## Session 34: GammaDischarge GREEN — the normal-form case is a THEOREM
- VERIFIER BUG FOUND AND FIXED in leavitt_search.py: monomial-set
  comparison misses equalities needing p₀+p₁ = 1; replaced final
  verification with the faithful stream action.  ρ now correctly
  certified as a unit.  (P)-experiments re-validated with the fixed
  net: still zero counterexamples.  A-nilpotency: FALSE for singular
  c (ρ itself: a = S(0)T(00), a^k = S(0)T(0^{k+1}) ≠ 0); still
  plausible for c = 1 (co-isometric-A searches: zero hits) — BUT NOW
  IRRELEVANT:
- **GammaDischarge.lean (COMPILED FIRST TRY): every unit with value
  1 + s₁(z₋ + z₀) lies in stableUnits.**  Proof: (P) applied to the
  unit's own [0,1]-window value gives IsUnit(1 + s₁z₋); flipUnit
  gives the γ-partner g with value 1 + z₋s₁; inv_mem_levelSpan gives
  the balanced inverse; the double flip w₂ := flip(Y,s₁, g⁻¹·flip(u))
  exposes the pure tail and PureTailNilpotency supplies D; then the
  compiled gamma_reduction closes.  NO dynamics, NO A-nilpotency, NO
  swap cascade needed for this case.
- REMAINING GAP (the only one): NARROW → NORMAL FORM plumbing:
  every [−1,1]-window unit is mod-H equivalent to one with value
  1 + s₁z, z ∈ [−1,0]-window.  Inventory: exists_narrow_representative
  (compiled) gives the [−1,1] window; exists_corner_move (Φ-move,
  compiled) gives [u] = [s₀(u+vw)t₀ + s₀vt₁ + s₁wt₀ + s₁t₁];
  ResidualMoves (compiled) has blockDiagUnit/kill_move machinery;
  exists_prefix_kill + exists_corner_transport (compiled).
  Next: derive the funnel from the Φ-move: choosing v, w to make the
  2×2-corner-form 1 + s₁(·)-shaped — the sr1-pivot (compiled:
  exists_balanced_sr1_pivot) supplies the invertible block.

## Session 34b: the last gap is EXACTLY one termination measure
- With GammaDischarge + WidthTwoReduction compiled, the assembly gap
  reduces to: **[−1,1]-window unit → [0,1]-window unit mod H** (the
  residual c + s₁w forms are [0,1]-window, so WidthTwo covers them
  directly; GammaDischarge covers 1+s₁z, z ∈ [−1,0]).
- Φ-move funnel computations (v := 1, w := −X₋): relocates ALL
  negative content into the (1,0)-corner slot as s₁X₋t₀ — relocation
  only; iterating migrates it deeper (S(1^k)X₋T(0^k)), never kills.
- 3×3 mixed-depth-code E-op game: (1,3)/(3,1)-slots shift degrees by
  ±1, but the conservation law (deg P + deg Q = −1 vs slot-sum ≥ 0)
  blocks every single-split placement.  CONFIRMED yet again: only
  genuine content-kills advance; the compiled ones are the
  p-split/prefix kills (z ↦ zp₁ column-kills on 1+s₁z forms, any z).
- The κ₁-transport of a narrow unit gives 1 + s₁z with z ∈ [−2,0];
  the naive p-split → corner-transport cycle is exactly the identity
  (t₁s₁ = 1).  The cycle must be run with the KILL inserted:
  z ↦ zp₁ destroys z·p₀-content permanently; the corner transport
  then re-expands.  The termination measure must count column
  content across the cycle.  **NEXT SESSION: run the machine BFS
  (fixed verifier!) on 10 narrow units + ρ through the compiled
  move-set (p-splits, swaps, balanced pivots, incomparable
  unipotents, κ-transports, flips) and extract the decreasing
  measure from the machine-found witnesses.**  The ρ-cascade
  (σ-swaps by hand) is one data point; get ten more.

## Session 35: WIDTH-3 SOLVED — the swap/unipotent kill algorithm
Machine campaign (sound verifier): 9/9 random + 6/8 nasty narrow
units reduced to [0,1]-window by 1-3 H-moves; the two stragglers
reduce with depth-4 moves — witnesses reveal the complete mechanism:

**THE TWO KILLS** (for u with value 1 + A + c₀ + B, A = Σλᵢ S(xᵢ)T(yᵢ)
degree −1, WLOG all xᵢ ≠ ε by the padding identity
T(b) = Σⱼ S(j)T(b++j)):
1. UNIPOTENT KILL (right; left is mirror): for an A-monomial (x,y)
   with x incomparable to y, to every T-side of A−ν, and to every
   T-side of c₀ (the "supply condition"): u·(1 − λS(x)T(y)) has
   degree-(−1) part A − ν EXACTLY (junk c₀ν = 0, Aν = 0, deg-(−2)
   = 0, balanced junk Bν harmless).  Monomial count DROPS.
   [1 − λS(x)T(y) ∈ H: incomparable unipotent, COMPILED.]
2. SWAP CONVERT (left): for x-rooted A-content failing supply or
   with comparable sides: σ_{x,β}·u with β FRESH (deep, incomparable
   to x, to all S-sides of A and of c₀'s positive-depth part —
   exists since finitely many non-ε cylinders never cover depth
   |β| ≫ 0): (1−p_x) annihilates ALL x-rooted A-monomials
   ((1−p_x)S(xw) = 0); junk σ₋·(scalar μ of u₀) = μS(x)T(β) is ONE
   fresh monomial with incomparable sides satisfying supply
   (killable by move 1); σ₋·c₀-deep = 0 and σ₋A-deg-(−2) = 0 by
   freshness.  ρ's witness (swap(0,10) left, one move) is the
   μ = 0 special case.
**TERMINATION**: lexicographic (#A-monomials failing supply-or-
comparable, #A-monomials): move 2 strictly drops the first
coordinate (converts ≥1 bad to exactly ≤1 good); move 1 strictly
drops the second keeping the first at 0.  All moves ∈ H via
compiled certificates (signedSwap_mem, incomparable_unipotent).
THEN: [0,1]-window reached ⟹ WidthTwoReduction ⟹ H.  **This
completes NarrowReduction**: narrow → (this algorithm) → [0,1] → H.

LEAN PLAN (final modules):
- NegativePartKill.lean: (i) the padding-WLOG lemma (S-sides
  nonempty); (ii) the two kill lemmas as class-moves with their
  junk computations (pure word calculus + compiled H-certificates);
  (iii) the induction on the finite monomial family (represent A
  via a Finset of monomials with coefficients — use the span-
  induction-friendly formulation: ∃ list of monomials, induct on
  its length/badness); (iv) narrow_to_width2:
  every narrow unit ~mod-H a [0,1]-window unit.
- NarrowReductionProof.lean: assemble with
  exists_narrow_representative + window_zero_one_mem_stableUnits +
  ResidualReduction wiring → ScalarReduction → B4 unconditional.
- Then: docstring updates (STALE_DISCLAIMER×3), audit re-run
  (LAUNDERED_PROP/UNUSED clear once wired), README.
NOTE: user is now handling all compilation — I write, they build.

## Session 35b: honest junk audit — swap raising-part creates degree-2
- CORRECTION to session 35: the swap σ_{x,β} (left) has raising part
  −S(β)T(x), and S(β)T(x)·R hits R's x-comparable S-roots → degree-2
  junk.  Right-swaps have the mirror problem (y vs R's T-sides).
  The machine witnesses succeeded because junk cancelled per-instance
  or was re-killed by later moves — the clean "junk-free swap" needs
  a hypothesis we cannot always discharge.
- REVISED (final) PLAN:
  1. B2-all-N in Lean (units 1 + τ, τ ∈ span[1,N], are in H) via the
     session-30/33 block-move route — ALL ingredients compiled
     (transvection pullback, matrixRingEquiv/equal-depth transport,
     cornerDiag descent, WidthTwoReduction endpoint).  This absorbs
     ALL upward junk permanently.
  2. KillMoves.lean: unipotent_kill_step WRITTEN (exact value
     formula, supply hypotheses, class-iff — no sorry); swap lemma
     restated with honest junk formula (positive junk unconstrained,
     negative-side exactness): A_new = a' + S(x)T(β), positive part
     arbitrary-but-window-bounded.
  3. Induction on the COUNT of negative monomials with the 2-move
     macro (swap-convert then unipotent-kill nets −1 per round;
     positive window grows but B2 doesn't care).
  4. narrow → [0,≤N]-window → c-invertible ((P) generalized: hmm —
     (P)-Lean is N = 1 only!  For the assembly, after killing ALL
     negatives we land in [0,N]: split u = c(1+τ) needs (P)-N.
     EITHER extend ZeroKOne to general N (grouped-coefficient
     remainder vector — session-29 math) OR note c = 1-preserving:
     the kill moves shift c only by junk... simplest: B2 handles
     1 + τ directly; for general c + τ: rank-normalize c and rerun —
     NO: cleanest is (P)-N.  Add ZeroKOneN to the plan (the Lean
     induction upgrades hclaim to a remainder VECTOR indexed by the
     N shifts; rank argument unchanged).
  Order of writing: B2 (BlockMoveTailKill.lean), ZeroKOneN,
  KillMovesSwap, NegativePartInduction, NarrowReductionProof,
  assembly + docstrings.

## Session 36: BlockMoveTailKill.lean WRITTEN (B2, all N)
- pure_positive_tail_mem_stableUnits: units 1 + τ, τ ∈ span[1, N+1],
  are in stableUnits — plain induction on N.  Base: WidthTwo.
  Step: top-component split via exists_components + Icc-insert;
  branch coefficients q_i := t_i·η; corner embed κ at word 00
  (pairKappaUnit, value 1 + S(00)τT(00)); multipliers
  m₂ := (1 − S(00)s₀T(01))(1 − S(00)s₁T(10)),
  m₁ := (1 + S(01)q₀T(00))(1 + S(10)q₁T(00)) — products of compiled
  incomparable unipotents, cross terms die by T(0i)S(00) = 0 /
  T(00)S(i0) = 0; the 18-term expansion of m₂·κ·m₁ collapses
  (X_iK = KY_i = X₀Y₁ = X₁Y₀ = 0; X₀Y₀ + X₁Y₁ = S(00)ηT(00) via the
  completeness split) to value 1 + S(00)aT(00) − X₀ − X₁ + Y₀ + Y₁
  with tail ∈ span[1, N] — IH closes; assembly through κ·u⁻¹ ∈ H.
- All negation isolated (m₂-value via -(s i)-middle in
  incomparableUnit; no mid-product sub before distribution lemmas).
  Cast discipline: window top stated as (N : ℤ) + 1; succ-case
  normalizes ↑(N+1)+1 → ↑N+2 once at entry.
- Registered in aggregator.  Awaiting user's compile.
- REMAINING WRITES: ZeroKOneN (grouped-coefficient (P) for [0,N] —
  needed to factor c out before B2 in the assembly);
  NegativePartInduction (the kill-move induction, needs the honest
  swap lemma with positive junk); NarrowReductionProof + B4 wiring;
  docstrings.

## Session 37: THE WIDTH-3 PROOF IS COMPLETE
**Theorem (W3).** Every narrow unit lies in the diagonal class group.
Proof structure (every move compiled or in written modules):
0. GENERALIZED B2 (upgrade of BlockMoveTailKill, same proof): every
   unit with value in span[0, N] is in H — the block-move step never
   used balanced-part = 1: with value v, κ-value = 1 + S(00)(v−1)T(00)
   and the same X/K/Y collapse lands in span[0, N−1].  Induction to
   N = 1 = WidthTwo.  ⟹ ZeroKOneN IS UNNECESSARY.
1. κ₀₀-TRANSPORT (compiled): [u] = [1 + S(00)(↑u−1)T(00)] puts ALL
   content in the 00-corner: S-sides and T-sides ⊆ 00-cylinder.
   ⟹ INFINITE FRESHNESS SUPPLY: all fresh words chosen in the
   1-cylinder, pairwise-disjoint across rounds.
2. THE MACRO (one round, kills all x-rooted negative monomials):
   for x an S-side root of the negative part A:
   (a) LEFT swap σ_{x,β}, β fresh: (1−p_x) annihilates all x-rooted
       A-monomials ((1−p_x)S(xw) = 0; β-incomparable-to-x extends to
       all x-rooted words); adds ONE monomial λ'S(x)T(β)
       (λ' = 1 + scalar-part, may vanish); junk: balanced
       −S(β)T(x)A-terms and positive; NO deg-(−2) (T(β)S-sides = 0
       by freshness).
   (b) RIGHT swap σ_{v,β}, v fresh: refreshes the S-side:
       λ'S(x)T(β) → S(v)T(β) (A'p_β = 0 freshness; junk S(β)T(v) is
       degree +1; all probes hit fresh v ⟹ vanish).
   (c) RIGHT unipotent kill of S(v)T(β) (KillMoves lemma):
       supply UNCONDITIONAL — A'·ν and C·ν probe T-sides against
       fresh v: zero.  NO resurrection: the balanced junk from (a)
       has OLD T-sides; right-mults probe T-sides only.
   Net: |A| drops by |A_x| ≥ 1.  Comparable and supply-blocked
   monomials handled uniformly (the swap kill needs NO
   incomparability of the monomial's own sides).
3. Induction on the negative monomial count (list-representation of
   A) ⟹ value ∈ span[0, N] ⟹ generalized B2 ⟹ H.
KEY DISCOVERIES en route: the resurrection channel (left-kill of the
fresh monomial hits S(β)T(x)A junk giving back p_xA — hence the
S-side REFRESH step (b)); covering obstruction for freshness (S-sides
can cover the tree — hence the κ-corner transport step 1).
REMAINING LEAN: (i) upgrade BlockMoveTailKill statement to
span[0,N]-values (small); (ii) SwapKill.lean: the two swap-step value
formulas ((a) and (b), word calculus, hypotheses = freshness
incomparabilities); (iii) NegKillInduction.lean: list-induction over
the negative part with the macro; (iv) NarrowReductionProof +
B4/docstrings.  NO other mathematics remains.

## Session 37b: generalized B2 written; swap-macro post-mortem; ρ anatomy
- WindowNonnegReduction.lean WRITTEN (built from the user's fixed
  BlockMoveTailKill by systematic transform, incorporating their
  abel-fix, hK-fold fix, and base-case fix): **every unit with value
  in span[0, N] is in stableUnits** — the block move never needs the
  balanced part invertible.  ZeroKOneN permanently unnecessary.
- GammaDischarge is actually SUBSUMED by window_zero_one (its value
  1 + s₁z₋ + s₁z₀ lies in span[0,1]!) — keep as milestone, note for
  the audit's redundancy pass.
- SWAP-MACRO POST-MORTEM (3 failed repairs, each by the conservation
  daemon): (i) left-kill of the fresh monomial resurrects p_xA via
  the σ's S(β)T(x)A junk; (ii) the S-side-refresh second swap's
  −p_v junk shields the kill (net zero); (iii) the balanced-swap
  refresh's S(x)T(v) half resurrects via the kill.  LESSON: swaps
  are invertible conjugations — content genuinely dies ONLY in
  fully-supplied unipotent kills.
- ρ-WITNESS ANATOMY (exact recompute): over 𝔽₂ the unsigned swap
  contains 1 + p_x which annihilates x-rooted content BY DUPLICATION;
  ρ has NO scalar part, so no fresh monomial appears; and the machine
  chose β = 10 COMPARABLE to content so σ₋-junk collapsed into
  balanced terms (T(10)S(10) = 1).  The machine plays 𝔽₂ billiards —
  not a formalizable uniform strategy.
- STRATEGIC RESET for the remaining gap ([−1,1] with genuine negative
  part): write the MIRROR CHAIN (mechanical mirrors of compiled
  proofs, xw-side): mirror-(P) → mirror-PureTail → mirror-WidthTwo →
  mirror-window-nonneg ⟹ [−N, 0]-window units die.  Then the final
  mixing question is sharply: value = c + A + B with A ≠ 0 ≠ B, and
  the two one-sided theorems + abelian Units/H available.

## Session 37c: the endgame statement — Bruhat/LPU over the tree
With both one-sided theorems (nonneg compiled-track + mirror chain to
write) and V-elements ∈ H (swaps + 3-cycles; Higman–Thompson
generation), the remaining gap is exactly:
**(LPU) every narrow unit factors mod H as
  (nonneg-window unit)·(V-element)·(nonpos-window unit)** —
the Leavitt/tree analog of banded-operator triangular factorization
(the V-pivot absorbs the band's index, cf. the conservation law).
Attack: strip the bottom degree: rank-normalize A_{−M} to a canonical
partial isometry τ_r (compiled machinery), multiply by the matching
rebalancer ω_r ∈ H; bookkeeping of what re-enters the bottom is the
termination question — weighted-depth measure candidate.
This is classical-shaped (Birkhoff via Gauss with pivots).  Next
session: (1) write the mirror chain (mechanical, ~4 modules:
mirror-(P) via xw-side, mirror-PureTail, mirror-κ-transport pieces,
mirror-WidthTwo/window-nonpos); (2) prove LPU by bottom-stripping
with the weighted measure; (3) V-generation lemma; (4) assembly.

## Session 38: the θ-route — mirror chain in THREE files, all written
- OppositeTranspose.lean: oppositeFamily (op-ring carries the family
  with s↔t; relations via op_mul reversal); θ := lift(oppositeFamily
  (family k)); θ̂ := unop∘θ with add/mul-anti/one/zero/smul/sub
  lemmas; generator exchange (lift_generator); word reversal
  θ̂(S(a)) = T(a); adjoin_generators_eq_top (mkAlgHom_surjective +
  FreeAlgebra.adjoin_range_ι + map_adjoin); INVOLUTION via
  adjoin_induction; WINDOW FLIP span[lo,hi] → span[−hi,−lo];
  thetaUnit.
- ThetaStable.lean: thetaMat := entrywise-θ̂ transpose;
  anti-multiplicativity (mul_apply + thetaHat_sum);
  thetaMat_single; thetaMatUnit; closure transport
  (Subgroup.closure_induction: transvections ↦ transposed
  transvections, products reverse — subgroups don't care);
  thetaMatUnit_diagUnit (diagonal is transpose-fixed);
  **thetaUnit_mem_stableUnits_iff** (both directions via involution).
- WindowNonposReduction.lean: [−N,0]-window units ∈ H, three-line
  transport through window_nonneg.
- All registered.  This replaces the planned 4-module mechanical
  mirror chain (mirror-(P), mirror-PureTail, mirror-WidthTwo,
  mirror-nonneg) with one anti-automorphism — and transports ANY
  future one-sided theorem for free.
- REMAINING: the mixing step (narrow with both signs → product of
  one-sided factors mod H: the LPU statement) + V-generation +
  NarrowReduction assembly + docstrings.

## Session 38b: THE MIXING CASE IS SOLVED — the Ω-intertwiner argument
**Theorem (final gap).** Every narrow unit u (value A + c + B,
A ∈ span[−1,−1], B ∈ span[1,1]) lies in H·[V], hence in
centralClassGroup once V-elements are certified in H.
PROOF:
1. Rank-normalize A to the canonical partial isometry
   τ = Σ_{i<r} S(aᵢ)T(bᵢ) (|a|=m, |b|=m+1, orthonormal families) by
   balanced H-units (rectangular pivot — small new lemma).
2. THE INTERTWINER: complete {bᵢ} and {aᵢ} to full prefix codes with
   a bijective pairing whose degree profile is ⊆ {0, +1}: exactly r
   completion pairs of degree +1 (volume bookkeeping:
   Σ 2^{−|a'|}(1−2^{−d}) = r·2^{−m−1} is satisfiable with r
   degree-1 pairs and the rest degree-0), with ALL completion pairs
   (b'ⱼ, a'ⱼ) chosen FRESH: mutually incomparable and incomparable
   to every S/T-side of the value.  Ω := Σ S(a-code)T(b-code), a
   V-element (code-change unit).
3. u·Ω⁻¹ computation: τ·Ω⁻¹ = Σ p_{aᵢ} (balanced!); the negative
   part of u·Ω⁻¹ is EXACTLY c·(degree-(−1) part of Ω⁻¹) =
   Σⱼ (c-column content)·S(b'ⱼ)T(a'ⱼ):
   - c singular: place the degree-1 completion pairs in the FREE
     columns (Sᶜ, refined deep) ⟹ negative part ZERO outright.
   - c = 1 (invertible, normalized): the negative part is the r
     FRESH canonical monomials S(b'ⱼ)T(a'ⱼ) themselves — both sides
     fresh ⟹ the unipotent kills are FULLY SUPPLIED (hasup, hcsup
     hold against all content by construction; no resurrection).
   Either way: u·Ω⁻¹ ~ nonneg-window unit ⟹ ∈ H (compiled).
4. Hence [u] = [Ω]; Ω ∈ H by the V-GENERATION LEMMA: refine to a
   common deep code, factor into incomparable transpositions
   σ (compiled ∈ H) with 3-cycles through incomparable spares for
   comparable moves (Higman's induction on code size).
REMAINING LEAN (fully specified, no open math):
  (a) rectangular rank normal form for degree-(−1) parts;
  (b) the Ω construction + the u·Ω⁻¹ value computation + kills;
  (c) V-generation (induction on codes);
  (d) NarrowReduction assembly → ScalarReduction (wiring compiled)
      → B4 → Theorem C; docstrings; audit.

## Session 38c: V-GENERATION PROOF (the last open item, now closed)
**Lemma.** For complete prefix codes {cᵢ}, {dᵢ} of equal size, the
code-change unit Ω = Σᵢ S(dᵢ)T(cᵢ) lies in H.
PROOF (induction on code size, all steps formalization-friendly):
1. RE-REPRESENT: pad each pair equally (S(d)T(c) = Σ_γ S(dγ)T(cγ))
   so the SOURCE code is the full depth-D code (element unchanged!).
2. SIBLING-PAIR EXISTENCE: any complete prefix code of size ≥ 2
   contains a sibling pair at maximal depth (the sibling of a
   maximal-depth element must itself be in the code: an ancestor
   would violate prefix-freeness).  Classical, 10-line proof.
3. ALIGN: right-multiply by a permutation of the (full) source code
   and left-multiply by a permutation of the target code — both are
   products of transpositions of same-code elements, which are
   pairwise incomparable, so each σ ∈ H (COMPILED) — to place a
   target sibling pair over a source sibling pair.
4. MERGE: S(ev0)T(w0) + S(ev1)T(w1) = S(ev)T(w) (the completeness
   relation).  Both codes shrink by one; induct.  Size 1: Ω = 1.
Composition law Ω_{e,d}·Ω_{d,c} = Ω_{e,c} available throughout.
**NO OPEN MATHEMATICS REMAINS.**  Full endgame stack:
  narrow (compiled width-reduction)
  → A-rank-normalization (rectangular pivot lemma, to write)
  → Ω-intertwiner with {0,+1} degree profile & fresh completions
    (session 38b; to write)
  → u·Ω⁻¹: negative part = r fresh fully-supplied monomials
    → KillMoves (COMPILED) → nonneg window → dies (COMPILED)
  → [u] = [Ω], Ω ∈ H (this lemma; to write)
  → NarrowReduction → ScalarReduction (COMPILED wiring) → B4
  → Theorem C unconditional; docstrings; audit.

## Session 39: CodeChangeInfrastructure.lean written
- IsCompleteCode (list-based: pairwise incomparability + cylinder
  sum = 1); wordS_ne_zero; exists_max_length_mem (list induction);
  exists_term_mul_ne_zero (sum-kill helper);
  merge_identity_one (s_{v0}t_{w0} + s_{v1}t_{w1} = s_v t_w);
  IsCompleteCode.incomp (Pairwise.forall with symmetry);
  **exists_sibling_pair** (max-depth element m = w++[a]; m ≠ ε via a
  second element + nil_prefix; completeness × wordS-nonzero forces a
  code element comparable to the sibling w++[b]; length bookkeeping
  pins it to equal the sibling; proper-prefix branch contradicts
  prefix-freeness through v <+: w <+: m);
  signFlip (1 − 2p_b as p+p, self-inverse via idempotency + abel);
  signFlip_mem (balanced value in levelSpan b.length);
  cylTransposition := signFlip · signedSwap ∈ H with value
  1 − p_a − p_b + s_at_b + s_bt_a (the p_b-collapse calc).
- Registered.  NEXT: CodeChangeUnits.lean — the generation induction:
  code-change units Ω_{d,c} := Σ S(dᵢ)T(cᵢ) ∈ H by induction on
  length, using: sibling pairs on both sides, ≤3 cylTransposition
  multiplications to align the pairing, merge_identity_one to drop
  to length−1, composition law Ω_{e,d}Ω_{d,c} = Ω_{e,c}.
  Then: rectangular pivot; the Ω-intertwiner narrow-reduction;
  assembly.

## Session 39b: CodeChangeSwap.lean written; generation-induction design
- pairValue (list of (target, source) pairs), perm-invariance;
  swapWord; cylTransposition_mul_term (the three-branch collapse
  computation: t = x ↦ y, t = y ↦ x, incomparable ↦ fixed);
  cylTransposition_mul_pairValue (list version).  Registered.
- MAIN INDUCTION DESIGN (CodeChangeUnits.lean, next write):
  theorem: ∀ n P, P.length = n → IsCompleteCode (P.map .snd) →
    IsCompleteCode (P.map .fst) → ∀ u, ↑u = pairValue P → u ∈ H.
  n = 0: complete-empty impossible (0 = 1 vs Nontrivial).
  n = 1: cylinder w = 1 forces w = ε (else the opposite-letter word
    kills it: p_w = 1 ⟹ S(other) = p_w·S(other)·... contradiction
    via wordT_mul_wordS_of_incomparable + wordS_ne_zero);
    both codes = [ε]: value = 1: u = 1 ∈ H.
  n ≥ 2: source siblings (w0, w1) via exists_sibling_pair on
    (P.map .snd); extract their pairs to the head via
    List.perm_cons_erase twice (pairValue-perm-invariant; the pair
    containing w1 survives the first erase since sources are
    distinct); target siblings (v0, v1) on (P.map .fst);
    ALIGN with ≤2 cylTransposition multiplications (4 by_cases on
    x = v0 / y' = v1, using the transposition-mul-pairValue lemma;
    all targets pairwise equal-or-incomparable since they form a
    prefix-free code — IsCompleteCode.incomp);
    MERGE via merge_identity_one: pairValue ((v0,w0)::(v1,w1)::Q) =
    pairValue ((v,w)::Q); new codes complete (cylinder sum unchanged
    by the merge identity; prefix-freeness of the merged word by the
    10-line children argument); IH at n−1; unwind the ≤2
    transposition units (∈ H via cylTransposition_mem).
- After that: rectangular pivot lemma; the Ω-intertwiner
  narrow-reduction (session 38b design); assembly.

## Session 40: CodeChangeUnits.lean — THE V-GENERATION THEOREM WRITTEN
- codeChange_mem_stableUnits: for pair lists P with both projections
  complete prefix codes, any unit valued Σ S(tᵢ)T(sᵢ) is in H.
  Strong induction on |P|:
  n = 0: completeness gives 0 = 1, absurd.  n = 1: cylinder = 1
  forces ε (eq_nil_of_cylinder_eq_one via the opposite first letter),
  value = 1.
  n = m+2: source siblings extracted to the head via perm_cons_erase
  (twice, mem_erase_of_ne); hypotheses transported (IsCompleteCode.
  perm, pairValue_perm); target siblings from exists_sibling_pair;
  TWO alignSteps (uniform id-or-transposition, alignStep_mul_pairValue
  handles both) sending head targets to (v0, v1) — the key
  distinctness hv0y₁ by three-way case analysis on swapWord;
  target-code completeness maintained via map_swapWord_perm
  (nodup + membership); explicit head structure hP₂struct; MERGE via
  merge_identity_one; merged codes complete via IsCompleteCode.merge
  (children-prefix argument + cylinder-sum preservation); IH at m+1;
  unwind with alignStep_mem + group.
- Supporting: swapWord_self/left/right/other; map_swapWord_perm
  (erase-erase decomposition, fixes off-support, Perm.swap);
  eq_nil_of_cylinder_eq_one; alignStep (dependent-if unit) + action
  + membership; IsCompleteCode.{nodup, perm, merge}.
- User is live-fixing binder/deprecation issues in parallel
  (Perm.pairwise_iff symmetry witness inline — thanks!).
- REMAINING WRITES: rectangular pivot; the Ω-intertwiner narrow
  reduction (session 38b); NarrowReduction/B4 assembly; docstrings.

## Session 41: Ω-argument full degree-audit — simplification AND a gap
POSITIVE (real, keeps): **the rectangular pivot is unnecessary.**
Column-canonicalization of the negative part comes from the COMPILED
balanced rank normal form via the squaring trick:
  Â := s₀·A is balanced; g·Â·h = E := Σ_{γ∈S} p_γ;
  then A·h = t₀·g⁻¹·E  (A = t₀s₀A = t₀Â — three lines).
So mod a right H-unit, A = t₀·M·E-form with M balanced: its COLUMN
code is the canonical S-cylinder family.  One-sided suffices.
NEGATIVE (gap in session 38b, found by full degree bookkeeping):
after the κ-corner transport and the profile-balanced Ω
(deg-(−1) pairs 00γ→1γ, deg(+1) pairs 1γ→01γ, deg-0 rest at common
depth D = n+2 — sizes match exactly at that depth!), the value·Ω⁻¹
computation gives negative part = Σ_γ S(1γ)T(01γ) from the scalar,
BUT the balanced image Ã·Ω⁻¹ = Σ (WS(γ))T(1γ) has T-sides exactly
{1γ} — the kill of S(1γ)T(01γ) fails hcsup there, and the kill
formula replaces the monomial by (WS(γ))T(01γ); summed:
new-negative = W·E_S·T(01) vs old Ã = W·E_S·T(00) — A PURE CORNER
ROTATION, zero net progress (conservation in purest form).
Also: the c-singular free-column supply is NOT joint-free in general
(relative column positions are invariant under one-sided moves).
STATUS: the mixing case ([−1,1] with both signs) is STILL OPEN.
What IS newly available and free: the θ-transported mirror of
GammaDischarge (units 1 + z·t₁, z ∈ span[0,1] are in H — three-line
transport), and the t₀ME-structure of the negative part.
SHARPEST REMAINING QUESTION: units with value 1 + t₀M·E + C + B
(M balanced-unit-times-cylsum): kill the t₀-column.  All conserved
quantities identified; the un-conserved handle must involve the
INTERPLAY (the unit equations), as in (P)'s proof — likely a second
shape-rank argument on the mixed system, not a move-hunt.

## Session 41b: TriangularFactorization.lean — the frontier is ONE Prop
- TriangularFactorization k (Prop): every narrow unit factors as
  (nonpos-window unit)·(code-change unit)·(nonneg-window unit).
- narrowReduction_of_triangularFactorization: the factorization
  implies NarrowReduction — each factor dies by a compiled/written
  theorem (window_nonpos [θ-transport], codeChange_mem_stableUnits
  [session 40], window_nonneg [block-move]) — hence ScalarReduction,
  B4, GL₂ = EL₂ etc. all follow through the COMPILED
  ResidualReduction wiring.
- THE ENTIRE FORMALIZATION IS NOW ASSEMBLED MODULO EXACTLY ONE NAMED
  STATEMENT: TriangularFactorization k — the Birkhoff/LPU
  factorization over the binary tree (session 37c; the honest
  remaining mathematics after session 41's audit killed the 38b
  shortcut).  Proof route: level-wise Gaussian elimination on the
  tower with code-change pivots (banded-operator triangular
  factorization); the compiled complement/section machinery
  (StableRankOne) and the shape calculus are the intended tools.
- Registered in aggregator.

## Session 42: RANK-ONE NORMAL FORM — the negative part is ONE monomial
**Breakthrough.** The stable block move with P := A (the whole
degree-(−1) part) and Q := 1 needs NO invertibility: through the
mixed-depth code {00, 01, 1},
  v̂ := (1 − S(00)·a·T(1)) · κ₀₀(u) · (1 + S(1)T(00))
has value  [1 + S(00)(z−a)T(00) − S(00)aT(1)]  +  S(1)T(00),
i.e. a [0,1]-window element plus the FIXED universal monomial
s₁t₀₀ — verified by direct hand computation (the cross terms die by
T(00)S(1) = 0, T(1)S(00) = 0; the T(1)S(1) = 1 collapse performs the
A-kill).  Both multipliers are compiled incomparable unipotents; the
corner embedding is compiled pairKappa.
**RankOneNormalForm.lean WRITTEN** (exists_rank_one_normal_form,
with the two-way stableUnits equivalence).  Registered.
THE REMAINING QUESTION IS NOW (Q): units with value w + s₁t₀₀,
w ∈ span[0,1], lie in central·H.  Notes toward (Q):
- naive kills/code-changes rotate (computed: the S(00)aT(1)-junk
  resurrects A; ρ-style Ω rotates the monomial corner);
- if w is invertible ((P)-rank-one analog — OPEN), then
  [v̂] = [1 + W⁻¹s₁·t₀₀] and the flip gives [1 + t₀₀W⁻¹s₁] — window
  of W⁻¹ uncontrolled either way;
- (Q) is (P)'s sibling: a shape-rank/graded-equation analysis of
  units W + N with N the fixed rank-one lowering monomial.  The
  inverse's graded equations now have the SPECIFIC N with N² = 0,
  N = s₁t₀₀: very rigid.  ATTACK NEXT: mimic ZeroKOne — normalize
  w's balanced part, corner system, but keep N as a known pivot.
TriangularFactorization now follows from (Q) + this module (much
weaker than full Birkhoff!) — next session: derive (Q) or replace
TriangularFactorization by the (Q)-form as the named frontier.

## Session 42b: STRUCTURE THEOREM for nonneg narrow units
NonnegUnitStructure.lean WRITTEN:
- nonneg_narrow_unit_structure: every unit with value in span[0,1]
  equals c·(1+η) with c invertible balanced (balanced inverse cinv,
  via balanced_component_isUnit = compiled (P) + rank normal form +
  inv_mem_levelSpan_of_val_mem) and η pure-degree-1 NILPOTENT
  (pure_tail_nilpotent).
- nonneg_narrow_unit_inv_window: inverses of [0,1]-window units have
  NONNEG windows (truncated geometric series (Σ(−η)^i)·cinv, via
  geom_sum_mul; explicit inverse formula proved by left-inverse
  uniqueness).
This is the rigorous UPPER-TRIANGULAR LEG of Birkhoff.  θ-transport
gives the lower leg for free when needed.
CONSERVATION SHARPENED (derivation this session): for ANY block-move
family, deposits P at (1,j)/Q at (j,1) must share the block pair, so
deposit degrees sum to deg P + deg Q = −1 — one deposit is always
negative; multi-pair splits ΣPᵢQᵢ with all deposits nonneg force
window(ΣPᵢQᵢ) ≥ 0 ≠ deg(−1).  Hence the rank-one normal form
(single monomial S(1)T(00) deposit with scalar 1) is OPTIMAL within
stable elementary moves; (Q) requires using the unit structure of w.
ANSATZ RESULT for (Q): v = w + s₁t₀₀ factors as
(1 + s₁·y·t₀₀)·(nonneg unit)  ⟺  y·(t₀₀·c) = t₀₀ solvable with y
balanced (c := balanced part of w; the quadratic term dies via
t₀₀s₁ = 0!).  Solvable ⟺ V₀·c = V₀ at some level (V₀ := rowspace of
t₀₀, i.e. the 00-corner coordinate subspace).  c = 1 case: y = 1 ✓
(v = 1+N unipotent).  General c fails ⟹ the code-change factor Ω is
genuinely needed exactly when V₀·c ≠ V₀: Ω must move the defect of
the 00-corner flag under c into position.  NEXT: use unit-ness of v
(graded equations c x₀ + b x₋₁ + N x₁ = 1 etc. + the structure
theorem) to prove the corrected flag condition is always reachable
in the H-orbit {g·v·g′} — the last mathematical gap.

## Session 42c: THE SCALAR-PENCIL REDUCTION (derived, not yet formalized)
Level-n corner recoding linearizes every narrow unit COMPLETELY:
for v = a + c + b narrow with all parts representable at level n,
the 2^n × 2^n block matrix V[i,j] := t_i · v · s_j (|i| = |j| = n) has
  t_i c s_j = C[i,j] · 1          (SCALAR — c balanced at level n),
  t_i b s_j = Σ_x B[i·x, j] s_x   (k-combination of s₀, s₁ only),
  t_i a s_j = Σ_x A[i, j·x] t_x   (k-combination of t₀, t₁ only).
So v ≅ the PENCIL  V = A₀t₀ + A₁t₁ + C + B₀s₀ + B₁s₁  with SCALAR
matrices A₀, A₁, C, B₀, B₁ ∈ M_{2^n}(k), invertible over M_m(L).
H-transport: M_m(L)-elementary ops (arbitrary L off-diag entries) and
GL_m(k) row/col ops are all stable-elementary = compiled H-moves.

INFLATION (one more corner level, m → 2m), computed exactly:
  t₀ ↦ [[t₀,0],[t₁,0]], t₁ ↦ [[0,t₀],[0,t₁]], 1 ↦ I₂,
  s₀ ↦ [[s₀,s₁],[0,0]], s₁ ↦ [[0,0],[s₀,s₁]] (entrywise recoding), so
  Â₀ = [[A₀,A₁],[0,0]], Â₁ = [[0,0],[A₀,A₁]], Ĉ = diag(C,C),
  B̂₀ = [[B₀,0],[B₁,0]], B̂₁ = [[0,B₀],[0,B₁]].
C = 0 is inflation-stable.

ELIMINATION STEP (Smith on C): GL_m(k) both sides → C = diag(I_r, 0);
the scalar pivots I_r clear ALL other L-entries in their rows and
columns via elementary H-ops → V ~ diag(I_r, V′) with V′ an
(m−r)-pencil with C′ = 0, still invertible.
CRUX (the whole remaining problem, now finite-dimensional):
  (Q-pencil, C = 0): classify invertible pencils
  A₀t₀ + A₁t₁ + B₀s₀ + B₁s₁ over M_m(k) up to GL_m(k)·(inflation)·
  (elementary H): show they reduce to direct sums realizing
  code-change units (⟹ TriangularFactorization ⟹ K₁ = 0).
Facts derived: pure-t and pure-s pencils are NEVER invertible
(m = 1 checked; grading argument general); m = 1 C = 0 pencils are
never units (to verify); code-change units have C ≠ 0 in general
(every complete-code bijection with only ±1 length shifts must
contain a balanced pair — dyadic mass equation P = 2/3 obstruction;
unbalanced-only code-changes exist but need mixed shift sizes ±2 at
staggered depths).
NEXT SESSION: (1) python-verify the pencil recoding + elimination on
ρ and on v̂ of random narrow units (leavitt_search.py stream solver);
(2) solve (Q-pencil): likely via the "column space filtration"
argument — B̄ := [B₀;B₁] : k^m → k^{2m} and Ā := (A₀,A₁) : k^{2m} → k^m
with invertibility forcing exact interlocking (Fredholm/dimension
count: rank conditions per inflation level stabilize), then peel
rank-1 code-change pivots; (3) formalize: PencilTransport.lean
(corner recoding ≅ + H-transport), PencilElimination.lean (Smith +
clearing), PencilClassification.lean ((Q-pencil)) → discharge
TriangularFactorization.

## Session 42d: (Q-pencil) constraints derived
For V = A₀t₀ + A₁t₁ + B₀s₀ + B₁s₁ (C = 0) invertible over M_m(L):
1. PARITY: V has only odd degrees ⟹ V·X_even = 0 ⟹ X := V⁻¹ is
   supported on ODD degrees only.
2. If 𝔅 := [B₀;B₁] (2m×m scalar) had full column rank m, the top
   equation B∘X_T = 0 (T ≥ 1) kills X_T (left-multiply by t_y and use
   a scalar left inverse of 𝔅), forcing X = X_{−1} pure; then the
   balanced part of V·X_{−1} = 1 splits over the M₂-corner blocks
   into  Bᵢ·Ξⱼ = δᵢⱼ·I_m  (Ξⱼ := X_{−1}sⱼ ∈ M_m(L₀)), i.e.
   𝔅·(Ξ₀|Ξ₁) = I_{2m} — impossible: row-reduce 𝔅 by G ∈ GL_{2m}(k)
   to put ≥ m zero rows; those rows of G·I_{2m} can't be zero.
   CONCLUSION: rank 𝔅 < m, and dually rank(A₀|A₁) < m (row rank),
   via the mirrored bottom equations on X·V = 1.
3. Hence ∃ v ≠ 0 with B₀v = B₁v = 0: column V·v = (A₀v)t₀ + (A₁v)t₁
   is PURE-t (and dually a pure-s row) — the Kronecker
   minimal-index chains begin.  Expected endgame: induction peeling
   Kronecker chains until the pencil is a direct sum of shift blocks
   = pencil forms of unbalanced code-change units; each peel uses a
   stabilized block move (the pure-t column as P with its scalar
   content pivoted by GL_m(k)).
Everything in 1–2 is elementary and formalizable with the compiled
graded-component machinery.  NEXT: finish the peeling induction
(does a pure-t column always split off a shift block after
inflation?), python-check on random invertible C = 0 pencils
(construct from unbalanced code-changes, e.g. shifts +2/−2 at
staggered depths), then formalize the pencil pipeline.

## Session 43: (Q-pencil) SOLVED — complete elimination proof
Setting: V invertible p×q matrix over L, every entry in
k-span{t₀,t₁} ⊕ k ⊕ k-span{s₀,s₁}; write V = A₀t₀ + A₁t₁ + C +
B₀s₀ + B₁s₁ with SCALAR A_z (p×q), C, B_z.  Rectangular allowed
(L^p ≅ L^q via Leavitt).  Two master objects:
  τ_q := [t₀I_q; t₁I_q]  (2q×q):  τ_q'τ_q = I_q (p₀+p₁=1),
         τ_qτ_q' = I_{2q} (t_zs_w = δ_zw), τ_q' := (s₀I_q | s₁I_q).
  ς_a := (s₀I_a | s₁I_a) (a×2a):  ς_aς_a† = I_a, ς_a†ς_a = I_{2a},
         ς_a† := [t₀I_a; t₁I_a].
KEY FACTORIZATION: any pure-t block T' = A₀'t₀+A₁'t₁ = (A₀'|A₁')·τ
with τ two-sided invertible ⟹ T' left-invertible over L ⟺ the
horizontal scalar concat (A₀'|A₁') has FULL COLUMN RANK (rank
argument both ways; scalar left-inverse composed with τ').  Dually
pure-s S' right-invertible ⟺ [B₀''; B₁''] vertical stack full ROW
rank (θ-transpose duality).

STEP 0 (Smith on C): GL(k) two-sided → C = diag(I_r, 0); scalar
pivots clear their rows/cols by elementary L-ops → V ~ I_r ⊕ V',
V' invertible with C' = 0.  [For square m×m narrow-unit pencils.]

STEP 1 (parity): C'=0 ⟹ X := V'⁻¹ supported on ODD degrees.

STEP 2 (branch dichotomy): top equation ((B∘X)_top = 0, strip with
t_y) and bottom (X_bot·(A-part) = 0, strip with s_w):
 (b) if 𝔅 := [B₀;B₁] (2p×q) full column rank: X = X_{−1} pure
     deg −1; corner-split of VX=1 gives B_aΞ_b = δ_ab I_p where
     Ξ_z := X_{−1}s_z, i.e. 𝔅·(Ξ₀|Ξ₁) = I_{2p}, and XV=1 deg-0
     gives Ξ₀B₀+Ξ₁B₁ = I_q ⟹ q = 2p, 𝔅 ∈ GL_{2p}(k), Ξ scalar
     = arrangement of 𝔅⁻¹; deg −2 equations kill A: X = G·τ_p
     (G scalar invertible) ⟹ V = ς_p·G⁻¹ ~ ς_p.  TERMINAL.
 (c) mirror (Ā := (A₀|A₁) p×2q full row rank): V ~ G'·τ_q.  TERMINAL.
 (d) both: X pure deg−1 AND pure deg+1 ⟹ X = 0 absurd. VACUOUS.
 (a) both deficient: rank 𝔅 < q and row-rank Ā < p: proceed.

STEP 3 (block extraction, branch (a)): right-GL: ker𝔅 = last
q−β coords (β := rank𝔅) → cols > β PURE-t; left-GL: coker rows →
rows > α PURE-s (α := row-rank Ā); zero block (rows>α)×(cols>β).
Invertibility blocks of X give: T' (α×(q−β) upper part of pure-t
cols) LEFT-invertible ⟹ (A₀'|A₁') full column rank 2(q−β) ≤ α;
S' ((p−α)×β) RIGHT-invertible ⟹ [B₀'';B₁''] full row rank
2(p−α) ≤ β.  Normalize: left-GL_α: (A₀'|A₁') = [I_{2b}; 0]
(b := q−β) → t-cols become [τ_b; 0]; right-GL_β: [B₀'';B₁'']G =
[I_{2a}|0] (a := p−α) → s-rows become (ς_a | 0 | 0).

STEP 4 (elimination): column-op (block unipotent, sources cols>β,
targets cols≤β, DISJOINT sets ⟹ product of incomparable
unipotents = 1 − Σ s_i x t_j ∈ H): subtract τ_b·(τ_b'·Y) — kills
rows 1..2b of cols ≤ β entirely (τ_bτ_b' = I_{2b}).  Row-op with
ς_a: kills cols 1..2a of rows ≤ α (ς_a†ς_a = I_{2a}); no
interaction (multipliers vanish on already-cleared rows).  Result
after permutation: V' ~ τ_b ⊕ M̃ ⊕ ς_a with M̃ ((α−2b)×(β−2a))
invertible (block-diagonal inverse argument using one-sided
inverses of τ, ς to kill off-diagonal blocks of the inverse),
C(M̃) = 0.  Sizes strictly decrease ⟹ RECURSE (rectangular).
Bases: 0×0 ✓; p×0/0×q force p=q=0; 1×1 impossible.

STEP 5 (assembly): square narrow-unit pencil ⟹ V ~ I_r ⊕ perm ⊕
(⊕ᵢ τ_{bᵢ} ⊕ ⊕ⱼ ς_{aⱼ}).  The transported L-element of this
direct sum: each τ-column j with entries t₀,t₁ at rows i,i'
contributes pairs (i ← j0), (i' ← j1); each ς-row i with s₀,s₁ at
cols j,j' contributes (i0 ← j), (i1 ← j'); each diagonal 1 at
(i,j) contributes (i ← j).  Sources: every col index appears once
as source-block (children for τ-cols, itself otherwise) ⟹
COMPLETE CODE; targets likewise ⟹ pairValue of a complete-code
pair list = codeChange unit ∈ H (codeChange_mem_stableUnits).
All moves: balancedEmbed(GL(k)) units ∈ H, incomparable-unipotent
products ∈ H, permutation-balanced ∈ H ⟹ v ∈ H directly ⟹
NarrowReduction k (no central factor even needed; bypasses
TriangularFactorization, which stays as historical scaffolding).

PENCIL TRANSPORT (level-n form; needed for Step 0 input): for v
narrow with all monomials of depth ≤ n on both sides:
t_i·S(a)T(b)·s_j (|i|=|j|=n) = T(i')S(j') (i = a++i', j = b++j',
zero unless prefix-compatible) ∈ k-span{1, s₀, s₁, t₀, t₁} since
||i'|−|j'|| ≤ 1: entries via wordT_append/wordS_append +
wordT_mul_wordS_self/incomparable.  v = Σ_{ij} s_i V[i,j] t_j via
Σ_{|i|=n} p_i = 1 (complete level-n code).

FORMALIZATION PLAN (in order):
 M1 PencilForm.lean: level-n entry decomposition + scalar-content.
 M2 PencilMoves.lean: balancedEmbed-GL mult (entry transform),
    block-unipotent col/row ops as products of incomparableUnit,
    permutation moves.
 M3 PencilRank.lean: field-linear-algebra: full-col-rank ⟹ GL
    normalization [I;0] (reuse rank-normal-form guts / Mathlib),
    Smith diag(I_r,0).
 M4 PencilBranches.lean: parity, dichotomy (graded top/bottom
    equations via exists_components on the inverse, corner strips).
 M5 PencilRecursion.lean: Steps 3–4 induction.
 M6 NarrowDischarge.lean: Step 5 ⟹ NarrowReduction k; rewire.

## Session 43b: Pencil pipeline M1 + M2 WRITTEN
- PencilCore.lean (M1): balancedEmbed_unit_mem_stableUnits (scalar
  moves ∈ H via levelSpan) and sum_incomparable_unipotent_mem[′]
  (block unipotents with disjoint row/col supports ∈ H, by
  cons-induction peeling incomparable unipotents; cross terms die on
  prefixCode_orthogonal).  Transport layer itself was ALREADY
  compiled: prefixRingEquiv (fullBinaryCode n) : M_{2ⁿ}(A) ≃+* A with
  matrixRingEquiv_apply/symm_apply and unitsEquiv.
- PencilForm.lean (M2): wordT_balancedEmbed_wordS (entry extraction
  via RingEquiv.symm_apply_apply), smul_t/s_expand, pencil_entry_A/B
  (asymmetric peeling: row word's LAST letter → t-generator with
  balanced residue evaluated at level m via a·s_z splits; column
  word's LAST letter → s-generator via s_z·(t_z·b) splits),
  exists_pencil_form: every narrow element = level-(m+1) matrix with
  entries A₀ᵢⱼ•t₀ + A₁ᵢⱼ•t₁ + Cᵢⱼ•1 + B₀ᵢⱼ•s₀ + B₁ᵢⱼ•s₁.
NEXT (M3–M6): Smith-on-C elimination; C=0 branch dichotomy (parity,
rank arguments on 𝔅/Ā via graded equations of the inverse matrix);
the τ/ς extraction recursion; NarrowDischarge.  See session 43 notes
for the complete paper proof.

## Session 43c: CORRECTION to the elimination — Step 0 (Smith-on-C +
## pivot clearing) as stated is WRONG; corrected recursion derived
BUG: after Smith on C the pivot entries are 1 + (odd content), not
clean scalars; Gaussian clearing multiplies odd·odd and creates
degree-±2 debris, leaving the pencil class.  Block-UDL needs the
pivot block invertible — not available.  So DROP Step 0.
FIX: run the τ/ς-extraction on FULL pencils (C included):
- Pure-t columns exist ⟺ ker [B₀; B₁; C] ≠ 0 (the C-row joins the
  stack); pure-s rows ⟺ coker (A₀ | A₁ | C) ≠ 0.
- The extraction + exact elimination (τ_bτ_b' = I_{2b}, ς_a†ς_a =
  I_{2a}) go through verbatim; crucially the correction terms kill
  entire row/column blocks EXACTLY, so the middle block M̃ is the
  ORIGINAL sub-block verbatim — still a (full) pencil.  One-sided
  extraction (only τ or only ς available) also recurses fine.
- Branches: (a) both stacks deficient → extract both, recurse;
  (b)/(c) one deficient → extract one, recurse; sizes strictly drop.
- (d) BOTH stacks full column/row rank: THE REMAINING OPEN CASE
  (parity closed it when C = 0; with C present the top-equation
  chain is B∘x_T = 0; C x_T + B∘x_{T-1} = 0; … — a Wiener–Hopf
  filtration argument is needed).  Examples in (d): V = 1;
  V = 1 + nilpotent-odd-triangular (units ✓).  CONJECTURE (d):
  forces C invertible, and then C⁻¹V = 1 + W with W odd and the
  even-odd decoupling ((1+W) unit ⟺ (1−W²) unit with even inverse)
  or a direct filtration closes it.  NOT YET PROVED.
- Rectangular pure-inverse branches from the C = 0 analysis
  (V = ς·G, V = G·τ) reappear inside (b)/(c) terminals — re-derive
  with C when writing.
STATUS: M1 (PencilCore) + M2 (PencilForm) written and registered.
M3 next = pencilVal transport lemmas (scalar-GL congruence action on
the five matrices; single incomparable-unipotent col/row ops at the
value level) — independent of the branch analysis, safe to build.
M4 = the dichotomy + extraction; its (d)-case needs the filtration
derivation FIRST (paper math next session).

## Session 43d: (d)-branch analysis — top level CLOSED, inner case framed
KEY REALIZATION: at the TOP level (square, word-indexed) the pencil
is just the narrow unit v itself, so window theorems apply:
- If [B₀;B₁] (2p×q, C-less stack) has full column rank: the top
  equation B∘x_T = 0 left-strips (t_y·B∘ = B_y) to B₀x_T = B₁x_T = 0
  ⟹ x_T = 0 for every T ≥ 0 ⟹ the inverse has window ⊆ [−R, −1] ⟹
  v⁻¹ is a NONPOS-window unit ⟹ v⁻¹ ∈ H (window_nonpos_mem_
  stableUnits, COMPILED) ⟹ v ∈ H.  INSTANT.
- Mirror: (A₀|A₁) full row rank ⟹ x's window ⊆ [1, T] via right
  t-strips (x_{−R}A_z = 0) ⟹ v⁻¹ nonneg-window ⟹ v ∈ H.  INSTANT.
- So the top level only needs extraction when BOTH C-less stacks are
  deficient — and then ker[B₀;B₁] ≠ 0 hmm NOTE: pure-t columns need
  ker[B₀;B₁;C] ≠ 0 (with C).  Remaining top-level case: [B₀;B₁]
  column-deficient but [B₀;B₁;C] full — extraction unavailable, window
  argument unavailable.  Handle via the relation system below, or:
  v ∈ ker[B₀;B₁], Cv ≠ 0: column = t-content + constant-content —
  a "quasi-pivot" column; possibly clearable by scalar ops first
  (GL-normalize so that ker[B₀;B₁]-columns have C-content in pivot
  position, then those columns are t₀,t₁,constant-only…).
STRIP CALCULUS facts (all derivable from compiled word lemmas):
- t_y·(B₀s₀+B₁s₁) = B_y;  (A₀t₀+A₁t₁)·s_y = A_y (right-strip);
- s-sums do NOT right-strip (y·s₀ + z·s₁ = 0 does not force y = 0:
  p₁s₀ = 0), so only VX-top and XV-bottom equations strip cleanly.
- XV = 1 expands in PURE T-monomials when X is a scalar t-polynomial:
  exact relation system (S0) Σ_z X_{[z]}B_z = I and
  (S_u) X_u C + Σ_z X_{z::u}B_z + [|u|≥2] X_{tail u}A_{head u} = 0.
- VX = 1 has mixed s_zT(v) monomials; boundary depth 1 gives corner
  relations B_zX_{[y]} = δ_{zy}I via double strips
  (t_a·(eq·S(u))·s_b); deeper: entangled but finite linear algebra.
INNER RECURSION CAVEAT: the rectangular children of the extraction
cannot use window theorems directly (the ambient matVal mixes the
frozen τ/ς blocks' windows).  Options: (i) solve the (S_u)-system
combinatorially for rectangular 4a/4b terminals; (ii) restructure the
recursion to stay at L-level (re-transport each child through a
corner isomorphism p_w L p_w ≅ L so children are again NARROW UNITS
of L at a deeper level — then the WHOLE recursion is: narrow unit →
either window-killed (∈ H instantly) or extraction reduces the
pencil size at fixed level → eventually window-killed; each child is
an honest L-unit and the top-level trichotomy applies verbatim!!).
Option (ii) is much better for formalization: need the corner
transport "unit of p_R·L·p_R-corner with identity complement ↦ unit
of L via a code-change conjugation" — i.e. τ_b⊕M̃⊕ς_a-value ~ (code
change moves) ~ 1⊕M̃'-value with M̃' the SAME pencil re-indexed at
possibly UNEQUAL row/col cylinder sets — needs the rectangular-corner
code-change conjugation lemma (source/target cylinder counts differ;
Leavitt L^p ≅ L^q makes the corners isomorphic via explicit
code-change conjugators).  NEXT SESSION: derive option (ii) cleanly
(the conjugator: pair the R-rows-complement to the C-cols-complement
by a mixed-depth complete-code bijection — exists for any two
nonempty cylinder sets; conjugation by that code-change unit maps
matVal(τ⊕M̃⊕ς) to 1 + (corner content of a DEEPER-level narrow
element) — then recurse as L-units, no matrices).

## Session 44: M3 WRITTEN + the refinement move (index shift) found
- WindowDichotomy.lean (M3) WRITTEN: matrix-free statements!
  mem_stableUnits_of_deg_one_left_full: if ∃ g₀ g₁ with
  g₀·(t₀b) + g₁·(t₁b) = 1 (b := deg-1 part of the narrow unit v),
  then v ∈ H — proof: graded equations of v·v⁻¹ = 1 via
  exists_components + components_unique (z_D := a·y(D+1) + c·y_D +
  b·y(D+(−1)); sum-reindexing via addRightEmbedding +
  Finset.map_add_right_Icc + sum_subset trimming), top-down kill of
  positive components (b·y_d = 0 ⟹ y_d = g₀t₀(b y_d) + g₁t₁(b y_d)
  = 0), then window_nonpos on v⁻¹ and inv_mem.  Mirror:
  mem_stableUnits_of_deg_neg_one_right_full via v⁻¹·v = 1 and
  (a·s₀)h₀ + (a·s₁)h₁ = 1.  NOTE: the full-rank hypothesis is
  equivalent to balanced-coefficient fullness (project g's to their
  degree-0 components), i.e. to the scalar stack ranks.
- THE REFINEMENT MOVE (new, replaces inflation for the stuck branch):
  in a pencil over a PAIR OF COMPLETE PREFIX CODES (row code, column
  code — not necessarily uniform level), any column j whose entries
  are s-FREE (B-content zero, i.e. j ∈ ker of the B-stack after
  right-GL normalization) may be REPLACED by its two children j0, j1:
  E(i, j0) = E(i,j)·s₀ = A₀(i,j)·1 + C(i,j)·s₀ (pencil-legal!), and
  E(i, j1) = A₁(i,j) + C(i,j)·s₁.  No multiplication — same v, refined
  column code.  Effect: the refined columns' A-content → C-content,
  C-content → B-content, A-content of children = 0.  Dually t-free
  rows refine.  This is the Wiener–Hopf partial-index shift.
- LOOP: T1-fail ⟹ ker[B-stack] ≠ 0 ⟹ (right-GL) B-free columns
  exist ⟹ zero columns impossible (invertibility), pure-t columns →
  τ-extraction, else refine.  OPEN: (i) the dichotomy/extraction
  lemmas must be stated CODE-RELATIVE (the current WindowDichotomy is
  intrinsic — fine at top level, but the loop needs the code-relative
  B-stack); (ii) TERMINATION of the refine loop — candidate measure:
  rank of the A-stack (refinement zeroes refined columns' A-content;
  never creates A-content), needs a second tier for rank-preserving
  steps.  Next session: settle code-relative statements + termination
  (python experiments on small pencils can guide), then M4/M5.

## Session 44b: termination probe + recursion without padding
- experiments/pencil_loop.py (exact F2 monomial arithmetic, fresh):
  random narrow units (products of incomparable unipotents, cylinder
  transpositions, ρ-type code changes, filtered to window [−1,1]),
  full round loop [T1/T2 rank checks → extraction availability →
  GL-normalize + refine a B-free column/row].  RESULT: 120/120 reach
  extraction; worst case needed 2 refinements; no illegal entries, no
  stuck states.  Strong evidence for within-round termination.
- NO-PADDING REALIZATION: the cross-round recursion needs no
  squaring-up at all — matVal generalizes to a PAIR of complete
  prefix codes of DIFFERENT sizes (v := Σ S(rᵢ)·E(i,j)·T(cⱼ); unit
  transport works since Σ p_r = 1 = Σ p_c).  The extracted middle M̃
  re-embeds along any complete codes with |R'| resp. |C'| words as an
  honest NARROW UNIT whose pencil is M̃ verbatim; total size |R'|+|C'|
  strictly decreases each round (a, b ≥ 1 blocks extracted).  So
  termination across rounds is BY SIZE; only within-round refinement
  termination needs a proof (probe: ≤ 2 in practice; conjecture: the
  A-stack rank strictly drops per refinement round or extraction
  becomes available — prove next session).
- README now tracks the NarrowReduction program as a checklist under
  B4; tick items as modules land (per user request).
REMAINING LEAN (in order): M4a mixed-code matVal + unit transport
(generalize PencilCore/prefixRingEquiv to code pairs); M4b the
extraction lemma; M4c refinement legality lemma (pure bookkeeping:
E(i,j0) = E(i,j)·s₀ identities); M5 the round recursion (strong
induction on |R|+|C|); M6 NarrowDischarge → NarrowReduction k; then
cleanup + full build.

## Session 45: M4 support modules landed
- CodePairTransport (user-polished): codePair_mul (middle-code
  collapse; outer word maps arbitrary), codePair_mul_eq_one,
  codePairUnit (rectangular two-sided inverses transport to units
  along code pairs of DIFFERENT sizes).
- WindowDichotomy REFACTORED to single-witness hypotheses
  (w·b = 1 / a·w = 1) — strictly stronger interface, simpler kills.
- CodeScalarMoves: codeScalar (scalar-matrix transport along ANY
  complete code), one/mul lemmas, transvections ↦ incomparable
  unipotents, diagonal(d) with d ≠ 0 ↦ product of pairKappaUnit
  insertions of central scalars (Finset product identity with
  orthogonality cross-kills), codeScalar_unit_mem: EVERY invertible
  scalar matrix transports into H along every complete code, via
  Matrix.Pivot transvection decomposition.
- CodeRelativeFullness: smul_mul_smul', t_combo_mul_s_combo
  ((Σα_z•t_z)(Σβ_w•s_w) = (Σα_zβ_z)•1), stack_left/right_inverse_
  transport: scalar stack one-sided inverses give the WindowDichotomy
  witnesses w over ANY code pair.  KEY DESIGN WIN: the witness w is
  written directly in pencil-entry form (t-combos between C-words and
  R-words), so codePair_mul does the whole collapse — no appended
  words, no incomparability side lemmas.
REMAINING: M4b atom-peel factorization (single pure-t column ⟹
v = (moves)·u₁·u₂ with u₁ a code-change and u₂ a strictly smaller
code-pair pencil unit); M4c refinement identities; M5 master
induction (on |ι| + |κ|) assembling: dichotomy-with-witnesses /
peel / refine; M6 NarrowDischarge.  Within-round termination proof
still needed (probe says ≤ 2 refinements; candidate: A-stack rank
drops or extraction fires).

## Session 45b: glue + termination evidence strengthened
- CodeChangeGlue.lean: isCompleteCode_of_family (Fintype → list
  interface), codeBijection_mem_stableUnits (Σᵢ s_{τᵢ}t_{σᵢ} ∈ H via
  the compiled generation theorem), cylinder_split,
  incomparable_append_single, split_family_free/sum (one-word split
  of a complete family, indexed Fin 2 ⊕ {i ≠ j₀}).  These are the
  u₁-ingredients of the atom peel.
- Probe extended (400 random narrow units): every case terminates;
  refinement needed in 183 cases, ALWAYS exactly one refinement, and
  afterwards the s-side extraction fires.  A-stack rank at the refine
  moment is often 0, so the naive rank measure is NOT the mechanism.
- Worked by hand the minimal stuck example (2×2):
  v = s₀t₀² + s₁t₀ + s₁s₀t₁, pencil [[t₀,0],[1,s₀]], unit with
  explicit inverse [[s₀,p₁],[−1,t₀]].  One col-refinement produces
  [[1,0,0],[s₀,s₁,s₀]] over {00,01,1}; row 2 becomes pure-s (u₀ = e₂
  annihilates the A′-stack AND the children's C-content, since
  children's C-cols are the old A-cols); one scalar col-op + one
  exact t-multiplier row-op reach ς ⊕ (−1).  KEY PARTIAL FACT toward
  termination: after refining ALL B-free kernel columns, any
  u₀ ∈ coker(A-stack) automatically annihilates the children's
  C-content (children C-cols = old A-cols); the only obstruction to
  the s-extraction firing is u₀·(C-content of the surviving columns).
  CONJECTURE (matches all 583 machine cases): iterating the batch
  refine forces this obstruction to die — candidate second-tier
  measure: dim(coker A-stack ∩ (surviving-C-cols)^⊥) strictly grows.
- User expanded the goal: after formalization completes → fully
  update nonsofic_groups_exist.tex → pursue new results beyond it.

## Session 46: M4b — the atom peel WRITTEN
AtomPeel.lean: atom_peel — given pencil data E over (R, C) with a
normalized shift-atom column (E i₁ j₀ = t₀, E i₂ j₀ = t₁, rows i₁ i₂
zero elsewhere) and ANY complete code D on {i // i ≠ i₂}, produces
u₂ with value the residual pencil over (D, C) (untouched block + one
scalar pivot at (⟨i₁⟩, j₀)) and u ∈ H ↔ u₂ ∈ H.  Mechanism:
- σ := the split of D at d₁ := ⟨i₁⟩ (children d₁·0 ↦ row i₁,
  d₁·1 ↦ row i₂; others untouched); prefix-freeness by four-way case
  analysis on incomparable_append_single; completeness by
  double-erase + sum_bij' bridge + cylinder_split.
- u₁ := codePairUnit(R, σ-code, δ, δ) — value Σ S(Rᵢ)T(σᵢ) by
  codeDelta_collapse; u₁ ∈ H by codeBijection_mem_stableUnits.
- hrow: a word colliding with D in exactly one place collapses the
  residual double sum to one row (reused 3×: t₁/t₀/scalar patterns).
- hfact: u = u₁·W by per-row case analysis; u₂ := u₁⁻¹·u — NO
  inverse data for the residual needed.
- NOTE: user fixed orientations live in parallel; remaining swaps +
  unused hlen applied.  Recurring bug-class: incomparable_append_
  single argument orientation — ALWAYS instantiate v := the
  non-appended word, w := the appended-to word, and check which of
  .1/.2 matches the goal.
STILL NEEDED for the extraction branch: (i) peel-normalization —
from "ker[B₀;B₁;C] ≠ 0" produce the (h1–h5)-normalized pencil via
codeScalar GL-moves (pair-extension-to-basis linear algebra) and the
exact right-multiplier (1 + N) clearing rows i₁,i₂ outside j₀
(disjoint-support block unipotent, value computation like
BlockMoveTailKill); (ii) the ς-mirror of the peel (or θ-transport);
(iii) M5 master induction; (iv) the stuck-branch progress theorem
(one batch refine ⟹ extraction/dichotomy — see session 45b notes for
the coker-A structural fact); (v) M6 NarrowDischarge; cleanup.

## Session 46b: peel-normalization support modules
- MixedCodeMoves.lean: code_unipotent_mem (block unipotents with
  disjoint supports along ANY prefix code ∈ H — generalizes
  PencilCore from uniform depth); t_combo_not_left_invertible
  (x·(λ₀•t₀ + λ₁•t₁) ≠ 1 via s_z-right-strips forcing s₁ ∈ k·s₀,
  killed by t·s-corners) — this forces the linear independence of
  the shift-column pair from unit-column left-invertibility.
- GLPairNormalization.lean: exists_isUnit_matrix_mulVec_pair —
  independent pair ↦ (Pi.single i₁ 1, Pi.single i₂ 1) by an
  invertible matrix: Basis.extend + two-swap index bijection +
  Basis.equiv + toMatrix'/toLin' transport.  Mathlib-API-heavy
  (name risks: to_subtype_range, extend_apply_self,
  fintypeBasisIndex, finrank_pi, basisFun_apply, toLin'_toMatrix').
NEXT (the extraction-normalization assembly, then M5):
 exnorm: from a unit-pencil (R,C,E) with kernel data
 (v₀ scalar, B_z·v₀ = 0, Cm·v₀ = 0, v₀ ≠ 0):
 (1) right-GL by any G with G⁻¹-hmm column-mix so col j₀ carries
     E·v₀ (pure-t); value-transform via codePair_mul with
     codeScalar-data; membership via codeScalar_unit_mem;
 (2) independence of the resulting (A₀-col, A₁-col) from
     t_combo_not_left_invertible + the left-invertibility witness
     T(Cⱼ₀)·u⁻¹ of the column u·S(Cⱼ₀);
 (3) left-GL from exists_isUnit_matrix_mulVec_pair putting the
     column into atom shape;
 (4) right block-unipotent (code_unipotent_mem, support
     {j₀}×(κ\{j₀})) clearing rows i₁ i₂ exactly (t₀s₀ = 1-cross);
 (5) atom_peel.  All five composed give: extraction-eligible unit ⟹
     ∃ smaller-code-pair pencil unit, H-membership equivalent.

## Session 46c: PencilEntryArith landed
pencilEntry (a₀•t₀ + a₁•t₁ + c•1 + (b₀•s₀ + b₁•s₁)) — matches
exists_pencil_form's parenthesization exactly (definitional bridge);
smul_mul_algebraMap / algebraMap_mul_smul; pencilEntry_mul/
mul_pencilEntry (coefficientwise scalar action); sum_pencilEntry;
pencilVal_mul_codeScalar and codeScalar_mul_pencilVal: right/left
transported-GL moves act as right/left matrix multiplication on the
five coefficient matrices (via codePair_mul + beta_reduce pattern).
ASSEMBLY MAP for exnorm (next session, all ingredients now exist):
 given kernel vector v₀ of [B₀;B₁;Cm]:
 (1) G_right := any invertible G with G·e_{j₀}-column = v₀
     (single-vector case of GLPairNormalization — need the 1-vector
     variant: v₀ ≠ 0 extends to a basis; SIMPLER: take the pair
     (v₀, any-independent-partner) or prove exists_isUnit_matrix_
     mulVec_single analogously; or transpose-trick);
     u' := u · codeScalarUnit(C, G_rightᵀ-hmm orientation: want
     new-col-j₀ = Σₗ E l·v₀ l: pencilVal_mul_codeScalar gives
     coefficients Σₗ A₀ i l G l j: col j₀: Σₗ A₀ᵢₗG_{l j₀}: need
     G-COLUMN-j₀ = v₀: same single-vector normalization, inverted;
 (2) new col j₀: B/C-coefficients vanish (kernel!), A-pair columns
     (a := A₀G-col, b := A₁G-col); independence: else t_combo_not_
     left_invertible contradicts left-invertibility of
     u'·S(C.word j₀) (witness T(C.word j₀)·u'⁻¹);
 (3) left move by exists_isUnit_matrix_mulVec_pair-G';
     codeScalar_mul_pencilVal;
 (4) clear rows i₁,i₂ outside j₀: right multiplier
     1 − Σ_{j≠j₀} S(C j₀)·x_j·T(C j), x_j := s₀·pE(i₁-row) +
     s₁·pE(i₂-row); membership code_unipotent_mem
     ({j₀}×(κ\{j₀})-support); value via codePair_mul with
     (δ + N)-data; entry-identities t₀s₀ = 1 kills exactly;
 (5) atom_peel.  Note: also need the 1-vector GL-normalization
     lemma (exists G invertible with G.mulVec e_{j₀} = v₀ — i.e.
     v₀ as a COLUMN of an invertible matrix; equivalently extend
     {v₀} to a basis — write exists_isUnit_matrix_col_eq next).

## Session 47: normalization toolkit COMPLETE
All extraction-step ingredients now written (pending user compile):
- CompleteCodeSupply: family_transport, exists_complete_family
  (induction: root code + split_family via equivOfCardEq),
  exists_complete_family_of_nonempty.
- GLVectorNormalization: exists_isUnit_matrix_col (v ≠ 0 as the
  j₀-column of an invertible matrix, via linearIndependent_unique +
  linearIndepOn_id + Basis.extend + one swap; NOTE the modern name
  linearIndepOn_id replaces to_subtype_range — user fixed the pair
  version).
- RowClearMove: pencilVal_mul_wordS (column collapse),
  t_zero/one_collapse, row_clear — the correction N (square-zero,
  code_unipotent_mem on {j₀}×erase j₀), the atom-column value
  (u·S(C j₀) = S(R i₁)t₀ + S(R i₂)t₁), the correction identity
  u·N = Σ_{j≠j₀}(atom-row terms), and the final six-way
  add_sum_erase split closed by abel.
REMAINING for goal (1): (a) FullExtraction.lean — compose:
 exists kernel vector of [B₀;B₁;Cm]-stack ⟹ (right codeScalar move
 with exists_isUnit_matrix_col putting v₀ into column j₀;
 pencilVal_mul_codeScalar) ⟹ (column j₀ pure-t; independence via
 t_combo_not_left_invertible against the witness T(C j₀)u⁻¹ +
 dependence-dichotomy over k) ⟹ (left codeScalar move with
 exists_isUnit_matrix_mulVec_pair; codeScalar_mul_pencilVal) ⟹
 row_clear ⟹ atom_peel (D from exists_complete_family_of_nonempty;
 nonempty since independence forces card ι ≥ 2).
 (b) the ς-mirror (mirror FullExtraction: pure-s ROW: either θ-
 transport or the symmetric proofs — the row-versions of
 pencilVal_mul_wordS-hmm wordT-mul-pencilVal etc).
 (c) M5 master induction (strong induction on card ι + card κ;
 branches: b = 0/a = 0 window-kill-direct; witness-dichotomy via
 CodeRelativeFullness + WindowDichotomy; extraction via
 FullExtraction; stuck-branch: batch refine + progress theorem).
 (d) M6 NarrowDischarge (exists_pencil_form bridge; top-level codes
 are fullBinaryCode; conclude NarrowReduction k).
 (e) cleanup + full build.

## Session 48: FullExtraction WRITTEN — the size-reduction engine
FullExtraction.full_extraction: from a kernel vector v₀ of
[B₀;B₁;Cm] (columnwise scalar equations), produces i₂, a complete
code D on {i ≠ i₂}, residual five-matrix data over (D, C), and u₂
with u ∈ H ↔ u₂ ∈ H.  Composition: exists_isUnit_matrix_col →
pencilVal_mul_codeScalar → (independence: LinearIndependent.pair_iff
by_contra, both dependence cases reduced to t_combo_not_left_
invertible against the witness (T(C j₀)·u1⁻¹)·(u1·S(C j₀)) = 1;
t = 0 case gives a = 0 directly, t ≠ 0 gives b = (−t⁻¹s)•a) →
fintype_card_le_finrank + finrank_pi + exists_pair_of_one_lt_card →
exists_isUnit_matrix_mulVec_pair → codeScalar_mul_pencilVal →
row_clear → atom_peel, with the residual-data bridge (per-(p,j)
split_ifs; pivot row becomes the Cm'-scalar 1 at (⟨i₁'⟩, j₀)).
H-chain: four-step iff-calc through uG, uG', row-clear m, u₁-peel.
REMAINING (goal 1): (a) ς-mirror of full_extraction; (b) the
rank-fullness → scalar one-sided inverse lemma (feeds
CodeRelativeFullness witnesses from stack-rank facts; via
LinearMap.exists_leftInverse-machinery); (c) M5 master induction
(measure card ι + card κ; branches recorded) + the stuck-branch
progress theorem (the only open math; 583/583 machine-verified);
(d) M6 NarrowDischarge; (e) cleanup + build; then goals 2–3.

## Session 49: MirrorExtraction landed + M5 architectural finding
- MirrorExtraction.lean WRITTEN: thetaHat_pencilEntry (θ̂ swaps t/s
  coefficient slots), thetaHat_pencilVal (θ̂ transposes code
  pencils), mirror_extraction: row-stack kernel vector ⟹ pencil
  unit over one fewer COLUMN, by full_extraction on the transposed
  side + thetaUnit_mem_stableUnits_iff transport.  Short (θ-route),
  no re-mirroring of the six modules.
- M5 FINDING (important): WindowDichotomy is a TOP-LEVEL argument —
  it needs the pencil parts to be pure-degree components, i.e.
  UNIFORM-depth codes.  Inner recursion nodes have mixed-depth codes
  (the peel's intermediate D), where deg(S(Rᵢ)t_zT(Cⱼ)) =
  |Rᵢ|−|Cⱼ|−1 varies.  So the inner T1/T2-full branches need a
  DIFFERENT terminal.  DERIVED (mostly): the ENTRYWISE-GRADED KILL:
  strip the unit equations to Σⱼ xᵢⱼ·y_{ji'} = δᵢᵢ' with
  y_{ji} := T(Cⱼ)u⁻¹S(Rᵢ); at the top entry-degree D of Y the
  s-part gives Σⱼ B_wᵢⱼ·y^{(D)}_{ji'} = 0 (t_w-strips; SCALAR
  combinations of the entry components!), so a full B-stack kills
  all positive entry components: Y-entries nonpositive.  MIRROR
  (A-stack full): entries nonnegative.  REMAINING QUESTION: the
  terminal conclusion from "u⁻¹ has nonpos-degree pencil entries"
  at mixed codes.  Candidate resolutions, ranked:
  (1) BOTH-FULL SANDWICH: if the node has BOTH stacks full (can the
      branching arrange this?), entries are balanced ⟹ u⁻¹ is a
      balanced-entry code-pair matrix ⟹ u⁻¹ = (code change)·
      (balanced unit)-decomposable ⟹ H by compiled machinery.
      Check: is inner-T1-full ∧ T2-deficient reachable? If the
      branch order tests extraction FIRST (both kernels empty in the
      T-branches), T1-full ∧ ker[B;C] = 0 ∧ coker[A;C] = 0 forces…
      analyze: T1-full ⟹ kerB = 0 ⟹ ker[B;C] = 0 ✓ consistent;
      coker[A;C] = 0 does NOT give A-stack-full.  So one-sided-full
      is reachable.  BUT: with Y-nonpos from T1, RERUN the kill on
      the OTHER equation side (u⁻¹u = 1, strips by T(Cⱼ)·…·S(Cⱼ')):
      gives the A-stack-of-u¹-hmm — the second kill needs the
      A-stack of u to be full, not given.  Partial.
  (2) UNIFORMIZING CONJUGATION: code-change ω's re-index (C,R) to
      uniform codes; blocked by the size-vs-depth constraint
      (Σⱼ2^{dⱼ} = 2^P forces varying dⱼ, which re-mixes degrees).
      Might be fixable by conjugating with ω on ONE side only and
      re-running the dichotomy at the new mixed shape.
  (3) Restate the master induction so inner nodes carry uniform
      codes: replace the peel's D by "refine everything to uniform
      after each peel" — needs re-narrowing (compiled window
      reduction) but breaks the size measure; would need a new
      measure (e.g. number of atoms extracted is NOT monotone…).
  (4) Prove the nonpos-entry terminal directly: u⁻¹-value lies in
      span{S(Cⱼ)·x·T(Rᵢ) : x nonpos}; seek a compiled-adjacent kill
      for this "code-window" class (θ of a code-nonneg class; the
      BlockMoveTailKill induction might generalize code-relatively —
      its moves are already code-flavored!).  Perhaps simplest:
      mimic WindowNonnegReduction's induction with the uniform
      level-1 code replaced by C-children; its engine
      (block move + κ-transport + orthogonality) is code-agnostic.
  NEXT SESSION: settle the inner terminal (try (4) seriously first —
  reread WindowNonnegReduction's proof shape; then (1)); then M5.

## Session 50: INNER TERMINAL FULLY DERIVED
The M5 branch structure is now: (extract) ∨ (mirror-extract) ∨
(col-refine: kerB ≠ 0) ∨ (row-refine: cokerA ≠ 0) ∨ TERMINAL-(a)
[kerB = 0 ∧ cokerA-rows = 0, i.e. BOTH C-less stacks full].
TERMINAL-(a) — complete derivation, all with compiled pieces:
 (a1) ENTRYWISE KILL, both directions: entries y_{ji} :=
      T(Cⱼ)u⁻¹S(Rᵢ); strip equations Σⱼ x_{ij}·y_{ji'} = δᵢᵢ'•1
      (x = pE-entries; insertion of Σ p_{Cⱼ} = 1) and the mirror
      Σᵢ y_{j'i}·x_{ij} = δ_{j'j}•1.  Downward induction at the top
      entry-degree: only B-part·y^{(D)} survives at degree D+1; t_w
      strips give Σⱼ B_wᵢⱼ y^{(D)}_{ji'} = 0; the scalar left
      inverse (G₀,G₁) of the B-stack combines these to
      y^{(D)}_{j₀i'} = 0.  B-full ⟹ entries nonpos.  Mirror: bottom
      equations + s_z-strips + right inverse of (A₀|A₁) ⟹ entries
      nonneg.  Both ⟹ Y-BALANCED.
 (a2) PADDING: balanced entries live in levelSpan(M) for common M;
      u⁻¹ = Σ scalar·S(Cⱼα)T(Rᵢβ) over the M-refinements of C and R
      (uniform under-word refinement keeps codes complete/free —
      have split machinery; M-fold refinement = words ++ level-M).
 (a3) SQUARENESS: the scalar matrix W over the refined code pair is
      invertible over k: a kernel vector v₀ of W gives (after the
      right codeScalar move, compiled) a ZERO COLUMN of a unit:
      0 = u⁻¹·S(word) ⟹ S(word) = 0 ⟹ contradiction (t·s = 1).
      Applied to both W and Wᵀ: |C-ref| = |R-ref| AND det W ≠ 0.
 (a4) DECOMPOSITION: pick a common index equiv; ω := code bijection
      (C-ref → R-ref) ∈ H (codeBijection_mem_stableUnits);
      ω⁻¹·u⁻¹ = codeScalar(R-ref, W′) ∈ H (codeScalar_unit_mem)
      ⟹ u⁻¹ ∈ H ⟹ u ∈ H.
With this, THE ONLY REMAINING OPEN MATH is refine-branch
termination (unchanged; 583/583 machine-verified).  FORMALIZATION
ORDER: EntryStrip.lean (insertion identity + two-sided entry
collapse); EntrywiseKill.lean (a1); BalancedCodePencil.lean
(a2+a3+a4); StackDichotomy.lean (scalar left-inverse-or-kernel);
M5 shell; M6.

## Session 50b: EntryStrip + EntrywiseKill WRITTEN
- EntryStrip.lean: wordT_pencilVal_wordS (two-sided strips recover
  entries, arbitrary E), strip_insert (products strip through a
  complete code's partition of unity).
- EntrywiseKill.lean: t_zero/one_strip_scombo helpers;
  entry_window_nonpos_of_B_full — common window via choose +
  Finset.sup, per-entry graded components via choose, strip
  equations from strip_insert + Units.mul_inv + entry extraction,
  degreewise equations via components_unique (z-function summed over
  Icc(−N−1, N+1) with the three shifted sums per code entry), the
  downward kill with the two t_w-strip relations and the scalar
  left-inverse combination (sum_smul/smul_smul juggling), and entry
  reassembly into span(dM(−N, 0)).
STILL FOR M5: the mirror kill (θ or symmetric: entries nonneg of A
full — likely via thetaHat on this theorem); BalancedCodePencil
(a2–a4: padding to scalar W over refined codes, squareness via
zero-column impossibility, ω·codeScalar decomposition);
StackDichotomy (left-inverse-or-kernel linear algebra); the M5 shell
(strong induction, five branches); refine-branch termination; M6.

## Session 51: StackDichotomy + RefinedCodes + combo independence
- StackDichotomy.lean: stack_left_inverse_or_kernel (via mulVecLin
  kernel cases + LinearMap.exists_leftInverse_of_injective +
  toMatrix'/toLin' transport; entries via Fintype.sum_sum_type) and
  the transposed mirror with mul_comm massage.
- RefinedCodes.lean (user-polished): not_prefix_append_of_
  incomparable/same, cylinder_level_split (induction with consEquiv;
  NOTE user fixes: append_assoc+singleton_append instead of
  append_cons chains; Fintype.sum_prod_type must NOT be applied with
  explicit `_` — higher-order unification times out), refined_free,
  refined_sum, codePair_partition.
- BalancedCodePencil.lean (installment 1): wordS/wordT_combo_eq_zero
  — k-independence of code words via one-sided strips; these are the
  zero-column/row engines for the squareness argument.
REMAINING for BalancedCodePencil (installment 2, next session):
 main theorem balanced_entries_mem_stableUnits following session-50
 notes: common level via choose+sup (EntrywiseKill pattern); W-data
 via exists_balancedEmbed_eq; hval: the four-fold reindex
 u⁻¹ = Σ_pΣ_q S(CM p)·map(W' p q)·T(RM q) (codePair_partition +
 matrixRingEquiv_apply + wordS/T_append + sum_prod_type);
 hinj/hinj' via x₀ := Σ v₀•S(RM q), u⁻¹x₀ = 0 ⟹ x₀ = 0 ⟹ combo
 lemmas; hcard via finrank_le_finrank_of_injective + finrank_pi;
 ω via codePairUnit-δδ (AtomPeel u₁ pattern) along equivOfCardEq;
 u₂ := ω·u⁻¹ = codeScalar(RM, W''); IsUnit W'' via
 injective_iff_surjective + LinearEquiv + toMatrix'-two-sided;
 codeScalar_unit_mem; conclude u⁻¹ = ω⁻¹u₂ ∈ H.
THEN: mirror entrywise kill (θ-transport of entry_window_nonpos —
gives entries nonneg when (A₀|A₁) full); M5 shell; refine
termination; M6.

## Session 52: BalancedCodePencil COMPLETE + StackDichotomy
balanced_entries_mem_stableUnits fully written (no sorries): common
level (choose+sup), scalar data (exists_balancedEmbed_eq per entry),
the four-fold reindex hval (codePair_partition + rfl-embed-expansion
+ append-collapses + sum_prod_type/sum_comm), zero-column hinj
(x₀ := Σ v₀•S(RM q); u⁻¹x₀ = 0 by orthogonality collapse + map_sum;
x₀ = u(u⁻¹x₀) = 0; wordS_combo), zero-row hinj' (p₀-sum FIRST, then
sum_comm and map_sum against hu₀ — note the vanishing only holds
after summing p₀!), hcard via mulVecLin-injectivity + finrank_pi,
ω := codePairUnit-δδ along equivOfCardEq (AtomPeel pattern),
hu₂val via codePair_mul + δ-collapse + sum_equiv-reindex,
hdet via exists_mulVec_eq_zero_iff + hinj, codeScalar_unit_mem,
u⁻¹ = ω⁻¹(ω u⁻¹).
REMAINING for goal (1):
 (i) mirror entrywise kill: entries NONNEG when (A₀|A₁) full — via
     θ-transport of entry_window_nonpos_of_B_full (θ̂ swaps the
     pencil B-data with A-data and reverses entries:
     θ̂(T(Cⱼ)u⁻¹S(Rᵢ)) = T(Rᵢ)θ̂(u)⁻¹-hmm θ̂(u⁻¹)-S(Cⱼ);
     thetaHat_mem_span_degree flips the window sign) — OR prove
     symmetrically with s_z-right-strips (bottom equations).
 (ii) window-intersection lemma: x ∈ span[−N,0] ∩ span[0,N'] ⟹
     x ∈ span[0,0] (components_unique on the two decompositions).
 (iii) M5 shell: strong induction on card ι + card κ; branches via
     stack_left_inverse_or_kernel ×2:
     - both left/right-inverses ⟹ EntrywiseKill + mirror + (ii) ⟹
       balanced entries ⟹ BalancedCodePencil ⟹ H;
     - B-kernel v₀: if also Cm·v₀ = 0-condition (check the C-column
       against v₀!): full_extraction; else refine-branch;
     - A-side mirror likewise (mirror_extraction);
     NOTE the extraction needs ker[B;C] (WITH C); the dichotomy
     gives ker[B] only — the M5 branch logic must test the
     C-inclusive stack for extraction and fall to refine when only
     the C-less kernel exists (the stuck branch).
 (iv) refine termination (open; 583/583 verified; the coker-A
     structural fact from session 45b is the key).
 (v) M6: exists_pencil_form at fullBinaryCode-codes (uniform level)
     feeding M5; conclude NarrowReduction k; rewire; cleanup.

## Session 53: M5 SHELL + M6 DISCHARGE WRITTEN — chain closed mod ONE Prop
- EntrywiseKillMirror.lean: mem_balanced_of_nonpos_nonneg (component
  uniqueness on the two window decompositions),
  entry_window_nonneg_of_A_full (θ-transport of the direct kill:
  entries of (θu)⁻¹ are θ̂ of entries of u⁻¹ with codes swapped;
  thetaHat_mem_span_degree flips the window).
- MasterInduction.lean: def StuckReduction (the isolated refinement
  configuration: pencil unit, no C-inclusive kernel on either side,
  but a C-less kernel exists); pencil_unit_mem — strong induction on
  card ι + card κ: empty-index contradiction, column/row extraction
  branches recursing via full_extraction/mirror_extraction
  (card_subtype_compl arithmetic), both-stacks-full terminal via the
  two kills + intersection + balanced_entries_mem_stableUnits, and
  the two stuck arrivals dispatched to StuckReduction.
- NarrowDischarge.lean: narrowReduction_of_stuckReduction —
  exists_pencil_form at fullBinaryCode(m+1) + pencil_unit_mem +
  stableUnits_le_centralClassGroup.  THE ENTIRE K₁-VANISHING CHAIN
  (NarrowReduction → ScalarReduction → B4 → GL = EL → Theorem C) NOW
  RESTS ON THE SINGLE PROP StuckReduction k.
REMAINING for goal (1): discharge StuckReduction (the refinement
termination argument — 583/583 machine-verified; the batch-refine +
coker-A structural fact from session 45b is the plan); then
retire/derive TriangularFactorization, refresh stale docstrings,
audit, full build.  Then goal (2): manuscript rewrite; goal (3):
novel results.

## Session 54: StuckReduction SOLVED — the two-exit algorithm (no
## extraction, no termination measure)

Numerics first (experiments/pencil_loop.py, case4_probe /
rank_evolution_probe / stall_probe, 3000 trials): every narrow unit
resolves by extraction at uniform starting codes; case 4 (both
C-less stacks deficient) is real (264 events, chains up to 9,
consecutive rank-stalls up to 4); the batch-refine ⟹ row-extract
conjecture from session 45b is FALSE (8/264).  So the extraction
route needs a genuine termination argument.  It turns out none is
needed: the master induction can be BYPASSED entirely.

KEY REALIZATIONS.
(1) `refine_column` needs only a B-free column — no condition on
the C-data.  Any kernel vector of [B₀;B₁] can be normalized into a
B-free column by a codeScalar move (compiled) and split (compiled).
So whenever ker[B₀;B₁] ≠ 0 we may grow κ by one at FIXED ι.
Once κ > 2ι the kernel is automatic (rank ≤ 2ι), so the refinement
loop can always continue to any target κ.
(2) FREE EXIT.  A pencil unit u = Σ S(R_i) E_ij T(C_j) (E narrow,
degrees in [−1,1]) with κ ≥ 2·2^⌈log₂ ι⌉ lies in stableUnits
directly: conjugate by two codeChange units (compiled), replacing R
by a complete code P of size ι with max depth M_ι := ⌈log₂ ι⌉ and C
by a complete code Q of size κ with min depth ≥ M_ι + 1 (exists
since κ ≥ 2^{M_ι+1}: split the full level-(M_ι+1) code).  Value
degrees ≤ max|P| + 1 − min|Q| ≤ 0, so window_nonpos_mem_stableUnits
(compiled) applies.  Kraft bounds show this aspect threshold is
achievable exactly when stated.
(3) STRICT NEGATIVITY.  If [B₀;B₁] has full column rank (scalar
left inverse G, compiled dichotomy), the compiled kill pins
X_ji := T(C_j) u⁻¹ S(R_i) to the window [−N, 0]; then the
degree-(+1) component of the strip Σ_j E_ij X_ji' = δ_ii' reads
Σ_j (B₀ij s₀ + B₁ij s₁) X⁰_ji' = 0 (X⁰ := balanced component; the
A- and C-slots cannot reach degree +1 against a nonpos window).
Stripping with t₀, t₁ gives Σ_j B_zij X⁰_ji' = 0 in L, and the
SCALAR left inverse G applies verbatim to L-valued vectors:
X⁰ = G·(BX⁰) = 0.  Hence X_ji ∈ span dM(−N, −1): strictly negative.
(4) PADDED EXIT.  With entries ≤ −1 the reshaped value needs only
max|Q| ≤ min|P| + 1.  Rounding can obstruct this (e.g. ι=5, κ=9),
but corner padding fixes it: κ_w-insertion at a word w of depth m
(κ_w(u) = s_w u t_w + (1 − p_w), value = S(w)uT(w) + Σ_{comp(w)}
S(v)T(v)) realizes the block sum u ⊕ I_m as a pencil over codes
(wR ∪ comp(w), wC ∪ comp(w)); code changes then redistribute the
words freely.  Choose d := ⌈log₂ ι⌉, m := 2^{d+1} − κ (≥ 0 since
κ ≤ 2ι ≤ 2^{d+1}; rank bound + the loop invariant κ ≥ ι).  Take
Q̃ := full level (d+1) (old block max depth d+1, pads at d+1) and
P̃ := a complete code of size ι+m, all depths ≥ d, with the m pad
words at depth ≥ d+1 — constructed from the full level-d code by
s := ι + 2^d − κ splits of which x := 2^d − ι hit level-d words
(0 ≤ x ≤ s ⟺ ι ≤ 2^d and κ ≤ 2ι ✓; deep-word count s + x =
2^d − ι + s ≥ m ✓).  Old entries: (d+1) − 1 − d ≤ 0 ✓; pad
diagonal: (d+1) − |P̃pad| ≤ 0 ✓.  Value nonpos ⟹ padded unit ∈ H
⟹ κ_w(u) ∈ H (code changes) ⟹ u ∈ H (kappa corner transfer).

THE ALGORITHM (proves: EVERY pencil unit over complete codes with
κ ≥ ι lies in stableUnits; narrow units enter at ι = κ = 2^{m+1}):
  while κ < 2·2^⌈log₂ ι⌉:
    if ker[B₀;B₁] ≠ 0: codeScalar-normalize; refine_column  (κ += 1)
    else: B full ⟹ strict-negativity ⟹ padded exit.  STOP.
  free exit.  STOP.
Termination: the loop counter 2·2^⌈log₂ ι⌉ − κ strictly decreases;
ι never changes.  No extraction, no atom peel, no terminal theorem,
no master induction needed for the main chain (they remain as
standalone structure results).  StuckReduction k follows a fortiori
(the stuck hypotheses are simply unused), which closes
NarrowReduction, ScalarReduction, B4, GL = EL, and Theorem C
unconditionally.

FORMALIZATION PLAN:
 N1 StrictNegativePencil.lean: (3) — balanced component of the
    inverse entries dies under a full B-stack.
 N2 CodeShapeSupply.lean: complete codes of size n with max depth
    ⌈log₂ n⌉; of size n ≥ 2^M with min depth ≥ M; the padded pair
    (P̃, Q̃) with its pad pairing (list-based, split-construction).
 N3 PencilReshape.lean: value window of Σ S(Q_j) X_ji T(P_i) from
    entry windows and depth bounds; the codeChange conjugation
    identity ω₁ u ω₂ = reshaped pencil.
 N4 KappaBlockSum.lean: κ_w(u) as a pencil over the augmented
    codes; κ_w(u) ∈ H ⟺ u ∈ H from the compiled corner machinery.
 N5 RefineLoopDischarge.lean: the κ-growth loop (induction on
    2·2^⌈log₂ ι⌉ − κ) + assembly: pencil_unit_mem_unconditional,
    stuckReduction_holds : StuckReduction k, and NarrowReduction k
    outright via narrowReduction_of_stuckReduction.
