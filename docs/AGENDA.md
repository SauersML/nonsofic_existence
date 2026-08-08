# Research agenda (owned and maintained by the formalization side)

Started 2026-08-08. This is my program for Question 3.4 — is every
hyperlinear group sofic? — maintained across sessions. Doctrine: every
claim is kernel-checked, cited-from-source, or explicitly conjectural.

## 1. The central free-lamp cover  [ACTIVE — skeleton landed]

For a group `K` with central subgroup `Z`, the cover
`H(K) := K *_Z (Z × ℤ) ≅ F_{K/Z} ⋊ K`.  Two cited closure theorems make it
load-bearing for Thom's K (Z = its Prüfer center):

* hyperlinearity is closed under amalgamation over amenable subgroups
  (Brown–Dykema–Jung), so **H(K) is hyperlinear, unconditionally**;
* soficity is closed under the same operation (Elek–Szabó / Păunescu), so
  **H(K) is sofic ⟺ K is sofic** (forward: subgroup monotonicity,
  kernel-checked in `Sofic/CentralFreeLampCover`).

Consequence: proving H(K) nonsofic resolves Q3.4 negatively with the
hyperlinear half pre-banked and no open citations.  The lamps are free of
charge in both categories; a nonsoficity proof must be a central-quotient
mechanism (KT centralizer normalization cannot fire: no escape from a
central base — kernel-checked `no_escape_of_central`).  Next: hunt the
mechanism; every failure is information about the central-quotient
question.

## 2. Defect-localized commutant pinning  [NEXT FORMALIZATION]

The (T)-analog of the kernel-checked f.d. collapse (N20), avoiding the
HS-stability wall.  Two elementary lemmas to formalize: (L1) a subspace
δ-contained in an equal-dimensional subspace is δ′-equal to it (principal
angles); (L2) the Ad-averaging operator moves by O(ε) under ε-perturbation
of the generators, so spectral gaps of exact sub-actions transfer.
Conjecture: for the Kun–Thom pairs, the model defect can be localized off
a relative-(T) core whose exact commutant then pins the almost-commutant;
one pinned compressor conjugate kills the free-lamp witness — T4 on the
family without Gate 1.

## 3. The approximation radicals  [FORMALIZABLE FRAME]

`𝔰(G)` (sofic radical) and `𝔥(G) ⊆ 𝔰(G)` (hyperlinear radical) over the
repo's `UniversalSofic`/hyperlinear ultraproducts.  Q3.4 ⟺ 𝔥 = 𝔰 on f.g.
groups.  Conjecture: `𝔰(H_K)` is the whole lamp kernel.  A strict
intermediate value of `𝔥(H_K)` would be a canonical invariant of the
hyperlinear–sofic gap — bigger than either answer.

## 4. The closure-exactness dichotomy  [ORGANIZING PRINCIPLE]

Four kernel-checked-or-measured instances this session: profinite closure
swallows the normal closure; f.d. commutants are rigid; liftable models
absorb totally; exact-coherence strata absorb totally.  Working thesis:
for compressed pairs, every closure-exact approximation category totally
absorbs, and Q3.4 on these families asks exactly whether HS-with-(T) is
closure-exact.  Dig where closure-exactness breaks: freeness over
amenable bases (item 1), controlled inexactness (item 2's ε-budget).

## Banked (kernel-checked, this repo)

Theorem A (nonsofic groups exist); the norm–trace interface; the free-lamp
reduction to KT 4.1 (verbatim-pinned); the f.d. collapse (H_K not MAP);
the profinite-closure criteria; the scalar-phase obstruction.  External
pins verified from source: KT 4.1 (arXiv:2608.06222v1), Preusser
(arXiv:1912.11386).  Dead, do not re-attempt: the seven phase-story
routes; exact-stratum ansätze on closure-swallowing frame pairs.
