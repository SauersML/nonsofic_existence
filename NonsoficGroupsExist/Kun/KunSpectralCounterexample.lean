import NonsoficGroupsExist.Matching.FiniteGraph
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The Kun `(4) → (1)` counterexample, checked

Version 5 of Kun's *On sofic approximations of Property (T) groups*
(arXiv:1606.04471) states Theorem 3 as a four-way equivalence.  The README's
literature audit argues that its final implication `(4) → (1)` is not valid as
written: the proof invokes the ordinary Cheeger / Dodziuk–Alon–Milman bound to
control `M²`, but ordinary Cheeger expansion bounds the nonconstant spectrum
away from `+1` and says nothing about the bottom of the Markov spectrum near
`-1`.

That argument is prose.  This module makes its graph-theoretic content — one
uniformly expanding, non-bipartite family whose Markov quotient runs to `-1` —
a checked statement, so the part of the critique that is a claim about finite
graphs is verified the same way the rest of the development is.  What the
numbered conditions of Theorem 3 assert about sofic approximations is still
read by hand; see the formalization boundary below.

## What is proved here

A single explicit family `switched m`: the complete bipartite graph `K_{n,n}`
with `n = m + 2`, carrying one degree-preserving two-edge switch.

* `neg_one_le_rayleigh` — the normalized Markov Rayleigh quotient is at least
  `-1` for every test function on every finite multigraph.  So `-1` is the
  floor the family is approaching and not a value it passes, and the family is
  not degenerate.
* `rayleigh_testVector` — one explicit vector, `+1` on the left side and `-1`
  on the right, has Rayleigh quotient exactly `-1 + 4/n²`.  Since the least
  eigenvalue of the normalized Markov operator is at most the Rayleigh quotient
  of any nonzero vector, the bottom of the spectrum is within `4/n²` of `-1`.
* `not_isBipartite` — for `n ≥ 3` the family is not bipartite, exhibited by the
  triangle the switch creates.  This is what defeats the obvious repair of
  adding a non-bipartiteness hypothesis to Theorem 3: the graphs are genuinely
  non-bipartite and the least eigenvalue still runs to `-1`.
* `hasCheegerLowerBound_one` — the load-bearing half.  For `n = m + 2 ≥ 6` the
  family satisfies the development's own expansion predicate,
  `FiniteMultiGraph.HasCheegerLowerBound (switched m) 1`: every nonempty vertex
  set `U` with `2|U| ≤ |V|` has at least `|U|` edge occurrences leaving it.  So
  the expansion is uniform in `m` while the Rayleigh quotient runs to `-1`, and
  the family is not a sequence of ever-worse expanders in disguise.
* `no_uniform_spectral_gap` — the three facts assembled: for every `c > 0` some
  member of the family is a non-bipartite graph with Cheeger constant at least
  `1` whose Markov Rayleigh quotient is below `-1 + c`.  No bound of the form
  "Cheeger constant at least `h` implies least Markov eigenvalue at least
  `-1 + c(h)`" can hold, which is the bound `(4) → (1)` is proved with.

## Formalization boundary

Two steps of the README's audit remain prose.

First, this module does not state Kun's Theorem 3, and so does not literally
refute the implication `(4) → (1)`: the numbered conditions are statements
about sofic approximations of a group, and translating them into hypotheses on
a single finite multigraph is exactly the reading of the paper that the audit
argues about.  What is checked here is the graph-theoretic fact the published
proof needs and does not have — uniform expansion together with least Markov
eigenvalue tending to `-1` — for one explicit family.

Second, the repetition argument is not formalized: forming one sequence from
many copies of each `switched m`, so that repeating the extremal vector across
all copies makes its `L²` norm proportional to the square root of the total
vertex count and the additive `L^∞` error in condition `(1)` cannot absorb the
defect.  It is bookkeeping over the family rather than a spectral fact, and it
is not a disjoint union of the `switched m` — a disjoint union has Cheeger
constant `0`, since a whole copy has empty boundary — so it needs the
approximation setting to state at all.  The spectral fact above is the part the
published proof gets wrong.

No declaration in the proof of the main results depends on this module -- the
proof of Result A uses only the forward implications `(2) → (3) → (4)`.  The
root module imports it so that it is compiled and audited like everything else;
a module outside the import closure is never built and never checked.
-/

namespace NonsoficGroupsExist
namespace KunSpectral

open Finset

/-- Vertices: the two sides of the bipartition.

Indexed by `m` with `n = m + 2` rather than by `n` with a `2 ≤ n` hypothesis:
the switch names the vertices `0` and `1`, and `Fin n` has no `OfNat` instance
without `NeZero n`, so the hypothesis form cannot even state the definition. -/
abbrev Ix (m : ℕ) : Type := Fin (m + 2)

abbrev Side (m : ℕ) : Type := Sum (Ix m) (Ix m)

/-- The vertex model. -/
def vertexModel (m : ℕ) : FiniteModel := ⟨Side m, inferInstance, inferInstance⟩

/-- The edge model: one occurrence per pair, as in `K_{n,n}`.  The switch below
reassigns the endpoints of two occurrences and leaves the index set alone,
which is exactly what makes it degree-preserving. -/
def edgeModel (m : ℕ) : FiniteModel := ⟨Ix m × Ix m, inferInstance, inferInstance⟩

variable {m : ℕ}

/-- The two switched occurrences. -/
def isFirstSwitch (e : Ix m × Ix m) : Prop := e.1 = 0 ∧ e.2 = 0
def isSecondSwitch (e : Ix m × Ix m) : Prop := e.1 = 1 ∧ e.2 = 1

instance (e : Ix m × Ix m) : Decidable (isFirstSwitch e) := by
  unfold isFirstSwitch; infer_instance
instance (e : Ix m × Ix m) : Decidable (isSecondSwitch e) := by
  unfold isSecondSwitch; infer_instance

/-- First endpoint.  The occurrence `(0,0)` is redirected to run inside the
left side and `(1,1)` inside the right side; every other occurrence still
crosses. -/
def firstEnd (m : ℕ) (e : Ix m × Ix m) : Side m :=
  if isFirstSwitch e then Sum.inl 0
  else if isSecondSwitch e then Sum.inr 0
  else Sum.inl e.1

/-- Second endpoint. -/
def secondEnd (m : ℕ) (e : Ix m × Ix m) : Side m :=
  if isFirstSwitch e then Sum.inl 1
  else if isSecondSwitch e then Sum.inr 1
  else Sum.inr e.2

theorem firstEnd_ne_secondEnd (e : Ix m × Ix m) :
    firstEnd m e ≠ secondEnd m e := by
  have h01 : (0 : Ix m) ≠ 1 := Fin.zero_ne_one
  unfold firstEnd secondEnd
  by_cases h1 : isFirstSwitch e
  · simp [h1, h01]
  · by_cases h2 : isSecondSwitch e
    · simp [h1, h2, h01]
    · simp [h1, h2]

/-- `K_{n,n}` with one degree-preserving two-edge switch, `n = m + 2`. -/
def switched (m : ℕ) : FiniteMultiGraph where
  vertex := vertexModel m
  edge := edgeModel m
  first := firstEnd m
  second := secondEnd m
  loopless := firstEnd_ne_secondEnd

theorem isFirstSwitch_iff (e : Ix m × Ix m) : isFirstSwitch e ↔ e = (0, 0) := by
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem isSecondSwitch_iff (e : Ix m × Ix m) : isSecondSwitch e ↔ e = (1, 1) := by
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

/-! ## The normalized Markov quadratic forms

Stated on edge occurrences, so they count multiplicity exactly as
`boundaryCard` does.  `degreeForm` is `∑ᵥ deg(v) f(v)²` written as a sum over
edges, which avoids defining degree at all. -/

/-- `⟨Af, f⟩` for the adjacency operator. -/
def adjacencyForm (X : FiniteMultiGraph) (f : X.vertex → ℝ) : ℝ :=
  2 * ∑ e, f (X.first e) * f (X.second e)

/-- `⟨Df, f⟩` for the degree operator. -/
def degreeForm (X : FiniteMultiGraph) (f : X.vertex → ℝ) : ℝ :=
  ∑ e, ((f (X.first e)) ^ 2 + (f (X.second e)) ^ 2)

/-- The normalized Markov Rayleigh quotient.  The least eigenvalue of the
normalized Markov operator is at most this for every nonzero `f`, which is the
only property of it used in the argument. -/
noncomputable def rayleigh (X : FiniteMultiGraph) (f : X.vertex → ℝ) : ℝ :=
  adjacencyForm X f / degreeForm X f

/-- `-1` really is the boundary being approached: no test function beats it.

`∑ₑ (f(u) + f(v))² ≥ 0` is the whole proof.  The same identity is why the
bound is tight on bipartite graphs, since equality would force `f(u) = -f(v)`
across every edge, but that converse is not stated or proved here. -/
theorem neg_one_le_rayleigh (X : FiniteMultiGraph) (f : X.vertex → ℝ)
    (hpos : 0 < degreeForm X f) : -1 ≤ rayleigh X f := by
  have key : 0 ≤ degreeForm X f + adjacencyForm X f := by
    have expand : degreeForm X f + adjacencyForm X f =
        ∑ e, (f (X.first e) + f (X.second e)) ^ 2 := by
      unfold degreeForm adjacencyForm
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e _ ↦ by ring
    rw [expand]
    exact Finset.sum_nonneg fun e _ ↦ sq_nonneg _
  rw [rayleigh, le_div_iff₀ hpos]
  linarith

/-! ## The test function -/

/-- `+1` on the left side, `-1` on the right.  On unswitched `K_{n,n}` this is
the extremal vector for the least eigenvalue `-1`; the switch is what keeps the
graph from being bipartite, and it costs exactly the two edges it moves. -/
def testVector (m : ℕ) : (switched m).vertex → ℝ :=
  Sum.elim (fun _ ↦ 1) (fun _ ↦ -1)

theorem testVector_sq (m : ℕ) (v : (switched m).vertex) :
    (testVector m v) ^ 2 = 1 := by
  cases v <;> simp [testVector]

/-- Every edge contributes `-1` except the two switched occurrences, which
contribute `+1`: both of their endpoints now lie on one side. -/
theorem edge_contribution (m : ℕ) (e : (switched m).edge) :
    testVector m ((switched m).first e) * testVector m ((switched m).second e)
      = if e = (0, 0) ∨ e = (1, 1) then 1 else -1 := by
  by_cases h1 : e = ((0, 0) : Ix m × Ix m)
  · subst h1
    simp [switched, firstEnd, secondEnd, isFirstSwitch, testVector]
  · by_cases h2 : e = ((1, 1) : Ix m × Ix m)
    · subst h2
      have hne : ¬ isFirstSwitch ((1, 1) : Ix m × Ix m) := by
        rw [isFirstSwitch_iff]
        simp
      simp [switched, firstEnd, secondEnd, hne, isSecondSwitch, testVector]
    · have hf : ¬ isFirstSwitch e := by rw [isFirstSwitch_iff]; exact h1
      have hs : ¬ isSecondSwitch e := by rw [isSecondSwitch_iff]; exact h2
      have hcond : ¬ (e = ((0, 0) : Ix m × Ix m) ∨ e = ((1, 1) : Ix m × Ix m)) := by
        rintro (h | h)
        · exact h1 h
        · exact h2 h
      rw [if_neg hcond]
      simp [switched, firstEnd, secondEnd, hf, hs, testVector]

/-- The edge count, through the `FiniteModel` wrapper.  `show` rather than
`simp [switched]`: the wrapper's `Fintype` instance is definitionally the
product instance but not syntactically one, so `Fintype.card_prod` has nothing
to match on until the coercion is stripped. -/
theorem card_edge (m : ℕ) : Fintype.card (switched m).edge = (m + 2) * (m + 2) := by
  show Fintype.card (Ix m × Ix m) = (m + 2) * (m + 2)
  simp

/-- The switch costs exactly the two occurrences it moves. -/
theorem sum_edge_contribution (m : ℕ) :
    ∑ e : (switched m).edge,
        testVector m ((switched m).first e) * testVector m ((switched m).second e)
      = 4 - ((m : ℝ) + 2) ^ 2 := by
  have hcongr : ∀ e : (switched m).edge,
      testVector m ((switched m).first e) * testVector m ((switched m).second e)
        = 2 * (if e = ((0, 0) : Ix m × Ix m) ∨ e = ((1, 1) : Ix m × Ix m) then (1 : ℝ) else 0)
            - 1 := by
    intro e
    rw [edge_contribution]
    split <;> ring
  rw [Finset.sum_congr rfl fun e _ ↦ hcongr e]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  have hcard : (Finset.univ.filter fun e : (switched m).edge ↦
      e = ((0, 0) : Ix m × Ix m) ∨ e = ((1, 1) : Ix m × Ix m)).card = 2 := by
    classical
    rw [Finset.filter_or, Finset.filter_eq', Finset.filter_eq']
    simp only [Finset.mem_univ, if_pos]
    exact Finset.card_pair
      (show ((0, 0) : Ix m × Ix m) ≠ ((1, 1) : Ix m × Ix m) by simp)
  rw [hcard, Finset.sum_const, Finset.card_univ, card_edge, nsmul_eq_mul]
  push_cast
  ring

theorem degreeForm_testVector (m : ℕ) :
    degreeForm (switched m) (testVector m) = 2 * ((m : ℝ) + 2) ^ 2 := by
  unfold degreeForm
  have hcongr : ∀ e : (switched m).edge,
      (testVector m ((switched m).first e)) ^ 2
        + (testVector m ((switched m).second e)) ^ 2 = 2 := by
    intro e
    rw [testVector_sq, testVector_sq]
    norm_num
  rw [Finset.sum_congr rfl fun e _ ↦ hcongr e, Finset.sum_const, Finset.card_univ,
    card_edge, nsmul_eq_mul]
  push_cast
  ring

/-- **The defect.**  The normalized Markov Rayleigh quotient of a single
explicit vector on the switched family is `-1 + 4/n²`, so the least
eigenvalue, which is at most the Rayleigh quotient of any nonzero vector,
runs to `-1`.  Combined with `hasCheegerLowerBound_one` this is
`no_uniform_spectral_gap` below. -/
theorem rayleigh_testVector (m : ℕ) :
    rayleigh (switched m) (testVector m) = -1 + 4 / ((m : ℝ) + 2) ^ 2 := by
  have hpos : (0 : ℝ) < ((m : ℝ) + 2) ^ 2 := by positivity
  rw [rayleigh, adjacencyForm, sum_edge_contribution, degreeForm_testVector]
  field_simp
  ring

/-! ## Non-bipartiteness

The reason the family survives the obvious repair of Kun's Theorem 3.  Adding a
non-bipartiteness hypothesis does not rescue `(4) → (1)`: this graph contains a
triangle and still has Markov quotient within `4/n²` of `-1`. -/

/-- A proper 2-colouring of the endpoints of every edge. -/
def IsBipartite (X : FiniteMultiGraph) : Prop :=
  ∃ c : X.vertex → Bool, ∀ e, c (X.first e) ≠ c (X.second e)

/-- The third triangle vertex, on the right side. -/
def rightTwo (m : ℕ) : Ix (m + 1) := ⟨2, by omega⟩

theorem rightTwo_ne_zero (m : ℕ) : rightTwo m ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [rightTwo] at this

theorem rightTwo_ne_one (m : ℕ) : rightTwo m ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp [rightTwo] at this

/-- `switched (m+1)` contains the triangle `inl 0 — inl 1 — inr 2 — inl 0`, so
it is not bipartite.  (`switched 0` is a four-cycle and is bipartite, which is
why the statement starts at `n = 3`.) -/
theorem not_isBipartite (m : ℕ) : ¬ IsBipartite (switched (m + 1)) := by
  rintro ⟨c, hc⟩
  have hA := hc ((0, 0) : Ix (m + 1) × Ix (m + 1))
  have hB := hc ((0, rightTwo m) : Ix (m + 1) × Ix (m + 1))
  have hC := hc ((1, rightTwo m) : Ix (m + 1) × Ix (m + 1))
  have hfA : (switched (m + 1)).first ((0, 0) : Ix (m + 1) × Ix (m + 1))
      = Sum.inl 0 := by simp [switched, firstEnd, isFirstSwitch]
  have hsA : (switched (m + 1)).second ((0, 0) : Ix (m + 1) × Ix (m + 1))
      = Sum.inl 1 := by simp [switched, secondEnd, isFirstSwitch]
  have hnotB1 : ¬ isFirstSwitch ((0, rightTwo m) : Ix (m + 1) × Ix (m + 1)) := by
    rintro ⟨-, h⟩
    exact rightTwo_ne_zero m h
  have hnotB2 : ¬ isSecondSwitch ((0, rightTwo m) : Ix (m + 1) × Ix (m + 1)) := by
    rintro ⟨h, -⟩
    exact Fin.zero_ne_one h
  have hnotC1 : ¬ isFirstSwitch ((1, rightTwo m) : Ix (m + 1) × Ix (m + 1)) := by
    rintro ⟨h, -⟩
    exact Fin.zero_ne_one h.symm
  have hnotC2 : ¬ isSecondSwitch ((1, rightTwo m) : Ix (m + 1) × Ix (m + 1)) := by
    rintro ⟨-, h⟩
    exact rightTwo_ne_one m h
  rw [hfA, hsA] at hA
  simp only [switched, firstEnd, secondEnd, hnotB1, hnotB2, hnotC1, hnotC2,
    if_false] at hB hC
  revert hA hB hC
  cases c (Sum.inl (0 : Ix (m + 1))) <;>
    cases c (Sum.inl (1 : Ix (m + 1))) <;>
    cases c (Sum.inr (rightTwo m)) <;> simp

/-! ## The uniform Cheeger lower bound

The load-bearing half.  Without it the family says nothing: EVERY bipartite
graph has a test vector of Rayleigh quotient `-1`, and the content of the
counterexample is precisely that uniform expansion does not prevent the
quotient from running to `-1`.

The notion of expansion is the development's own
`FiniteMultiGraph.HasCheegerLowerBound` from `Matching/FiniteGraph.lean`, the
same predicate the co-area machinery consumes:
`X.HasCheegerLowerBound h` asserts `0 < h` together with
`h * |U| ≤ X.boundaryCard U` for every nonempty `U` with
`2 * |U| ≤ Fintype.card X.vertex`, where `boundaryCard` counts edge
*occurrences* crossing the cut, with multiplicity.

The counting is done against `bipBoundary`, the boundary the same vertex set
would have in the unswitched `K_{n,n}`.  Only two occurrences have different
endpoints in `switched m`, so the switched boundary undercounts `bipBoundary`
by at most `2`. -/

/-- Left-side indices of a vertex set. -/
def leftPart (U : Finset (Side m)) : Finset (Ix m) :=
  Finset.univ.filter fun i ↦ Sum.inl i ∈ U

/-- Right-side indices of a vertex set. -/
def rightPart (U : Finset (Side m)) : Finset (Ix m) :=
  Finset.univ.filter fun i ↦ Sum.inr i ∈ U

theorem mem_leftPart (U : Finset (Side m)) (i : Ix m) :
    i ∈ leftPart U ↔ Sum.inl i ∈ U := by
  simp [leftPart]

theorem mem_rightPart (U : Finset (Side m)) (i : Ix m) :
    i ∈ rightPart U ↔ Sum.inr i ∈ U := by
  simp [rightPart]

/-- The left inclusion, as an embedding, so that `Finset.map` applies. -/
def inlEmb (m : ℕ) : Ix m ↪ Side m := ⟨Sum.inl, Sum.inl_injective⟩

/-- The right inclusion, as an embedding. -/
def inrEmb (m : ℕ) : Ix m ↪ Side m := ⟨Sum.inr, Sum.inr_injective⟩

theorem inlEmb_apply (i : Ix m) : inlEmb m i = Sum.inl i := rfl

theorem inrEmb_apply (i : Ix m) : inrEmb m i = Sum.inr i := rfl

/-- The split of a vertex set across the two sides.  This is the `a + b` of the
counting argument. -/
theorem card_leftPart_add_card_rightPart (U : Finset (Side m)) :
    (leftPart U).card + (rightPart U).card = U.card := by
  have hunion : (leftPart U).map (inlEmb m) ∪ (rightPart U).map (inrEmb m) = U := by
    ext x
    cases x with
    | inl i =>
      simp [Finset.mem_map, inlEmb_apply, inrEmb_apply, mem_leftPart, mem_rightPart]
    | inr j =>
      simp [Finset.mem_map, inlEmb_apply, inrEmb_apply, mem_leftPart, mem_rightPart]
  have hdisj : Disjoint ((leftPart U).map (inlEmb m)) ((rightPart U).map (inrEmb m)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_map] at hx hx'
    obtain ⟨i, -, hi⟩ := hx
    obtain ⟨j, -, hj⟩ := hx'
    rw [inlEmb_apply] at hi
    rw [inrEmb_apply] at hj
    subst hi
    simp at hj
  calc (leftPart U).card + (rightPart U).card
      = ((leftPart U).map (inlEmb m)).card + ((rightPart U).map (inrEmb m)).card := by
        rw [Finset.card_map, Finset.card_map]
    _ = ((leftPart U).map (inlEmb m) ∪ (rightPart U).map (inrEmb m)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ = U.card := by rw [hunion]

theorem card_leftPart_le (U : Finset (Side m)) : (leftPart U).card ≤ m + 2 := by
  calc (leftPart U).card ≤ Fintype.card (Ix m) := Finset.card_le_univ _
    _ = m + 2 := Fintype.card_fin (m + 2)

theorem card_rightPart_le (U : Finset (Side m)) : (rightPart U).card ≤ m + 2 := by
  calc (rightPart U).card ≤ Fintype.card (Ix m) := Finset.card_le_univ _
    _ = m + 2 := Fintype.card_fin (m + 2)

/-- The occurrences that would leave `U` in the unswitched `K_{n,n}`: those
whose unswitched endpoints `inl i` and `inr j` straddle `U`.  This is not the
boundary of `switched m` -- the two switched occurrences are counted here by
their old endpoints -- and the gap is bounded by `card_bipBoundary_le`. -/
def bipBoundary (U : Finset (Side m)) : Finset (Ix m × Ix m) :=
  Finset.univ.filter fun e ↦
    (Sum.inl e.1 ∈ U ∧ Sum.inr e.2 ∉ U) ∨ (Sum.inr e.2 ∈ U ∧ Sum.inl e.1 ∉ U)

theorem mem_bipBoundary (U : Finset (Side m)) (e : Ix m × Ix m) :
    e ∈ bipBoundary U ↔
      (Sum.inl e.1 ∈ U ∧ Sum.inr e.2 ∉ U) ∨ (Sum.inr e.2 ∈ U ∧ Sum.inl e.1 ∉ U) := by
  simp [bipBoundary]

/-! ### Counting the unswitched boundary -/

/-- The crossing occurrences split into the two rectangles `L × Rᶜ` and
`Lᶜ × R`. -/
theorem bipBoundary_eq_union (U : Finset (Side m)) :
    bipBoundary U =
      (leftPart U ×ˢ (rightPart U)ᶜ) ∪ ((leftPart U)ᶜ ×ˢ rightPart U) := by
  ext e
  rw [mem_bipBoundary]
  simp only [Finset.mem_union, Finset.mem_product, Finset.mem_compl,
    mem_leftPart, mem_rightPart]
  tauto

theorem card_bipBoundary (U : Finset (Side m)) :
    (bipBoundary U).card =
      (leftPart U).card * (m + 2 - (rightPart U).card)
        + (m + 2 - (leftPart U).card) * (rightPart U).card := by
  have hIx : Fintype.card (Ix m) = m + 2 := Fintype.card_fin (m + 2)
  have hdisj :
      Disjoint (leftPart U ×ˢ (rightPart U)ᶜ) ((leftPart U)ᶜ ×ˢ rightPart U) := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_product] at he he'
    exact (Finset.mem_compl.mp he'.1) he.1
  rw [bipBoundary_eq_union U, Finset.card_union_of_disjoint hdisj,
    Finset.card_product, Finset.card_product, Finset.card_compl, Finset.card_compl,
    hIx]

/-- The `K_{n,n}` cut identity `a(n-b) + (n-a)b + 2ab = n(a+b)`, kept in added
form so that no truncated subtraction survives into the inequalities. -/
theorem cut_identity {n a b c : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (hc : c = a * (n - b) + (n - a) * b) : c + 2 * (a * b) = n * (a + b) := by
  have h1 : a * (n - b) + a * b = a * n := by
    rw [← mul_add, Nat.sub_add_cancel hb]
  have h2 : (n - a) * b + a * b = n * b := by
    rw [← add_mul, Nat.sub_add_cancel ha]
  subst hc
  calc a * (n - b) + (n - a) * b + 2 * (a * b)
      = (a * (n - b) + a * b) + ((n - a) * b + a * b) := by ring
    _ = a * n + n * b := by rw [h1, h2]
    _ = n * (a + b) := by ring

theorem card_bipBoundary_add (U : Finset (Side m)) :
    (bipBoundary U).card + 2 * ((leftPart U).card * (rightPart U).card)
      = (m + 2) * U.card := by
  rw [← card_leftPart_add_card_rightPart U]
  exact cut_identity (card_leftPart_le U) (card_rightPart_le U) (card_bipBoundary U)

/-- `4ab ≤ (a+b)²`, in `ℕ`, by cases on which of `a`, `b` is larger so that no
subtraction is needed. -/
theorem four_mul_mul_le_sq (a b : ℕ) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  rcases le_total a b with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    calc 4 * (a * (a + k)) ≤ 4 * (a * (a + k)) + k * k := Nat.le_add_right _ _
      _ = (a + (a + k)) * (a + (a + k)) := by ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    calc 4 * ((b + k) * b) ≤ 4 * ((b + k) * b) + k * k := Nat.le_add_right _ _
      _ = (b + k + b) * (b + k + b) := by ring

/-- The arithmetic step: `c + 2p = q` and `4p ≤ q` force `q ≤ 2c`.  Stated over
bare naturals so that `omega` sees only linear atoms. -/
theorem cheeger_halving {c p q : ℕ} (h1 : c + 2 * p = q) (h2 : 4 * p ≤ q) :
    q ≤ 2 * c := by
  omega

/-- Half of the vertices per side is enough: a set of at most `n` vertices has
unswitched boundary at least `n|U|/2`. -/
theorem card_bipBoundary_lower (U : Finset (Side m)) (hUle : U.card ≤ m + 2) :
    (m + 2) * U.card ≤ 2 * (bipBoundary U).card := by
  have hab : (leftPart U).card + (rightPart U).card = U.card :=
    card_leftPart_add_card_rightPart U
  have hsq : 4 * ((leftPart U).card * (rightPart U).card) ≤ U.card * U.card := by
    have h := four_mul_mul_le_sq (leftPart U).card (rightPart U).card
    rw [hab] at h
    exact h
  have h4 : 4 * ((leftPart U).card * (rightPart U).card) ≤ (m + 2) * U.card :=
    hsq.trans (Nat.mul_le_mul hUle (le_refl U.card))
  exact cheeger_halving (card_bipBoundary_add U) h4

/-! ### The switch costs at most two occurrences -/

theorem first_eq_inl {e : Ix m × Ix m} (h0 : e ≠ (0, 0)) (h1 : e ≠ (1, 1)) :
    (switched m).first e = Sum.inl e.1 := by
  have hf : ¬ isFirstSwitch e := by rw [isFirstSwitch_iff]; exact h0
  have hs : ¬ isSecondSwitch e := by rw [isSecondSwitch_iff]; exact h1
  simp [switched, firstEnd, hf, hs]

theorem second_eq_inr {e : Ix m × Ix m} (h0 : e ≠ (0, 0)) (h1 : e ≠ (1, 1)) :
    (switched m).second e = Sum.inr e.2 := by
  have hf : ¬ isFirstSwitch e := by rw [isFirstSwitch_iff]; exact h0
  have hs : ¬ isSecondSwitch e := by rw [isSecondSwitch_iff]; exact h1
  simp [switched, secondEnd, hf, hs]

theorem mem_boundary_of {U : Finset (Side m)} {e : Ix m × Ix m}
    (h : ((switched m).first e ∈ U ∧ (switched m).second e ∉ U) ∨
      ((switched m).second e ∈ U ∧ (switched m).first e ∉ U)) :
    e ∈ (switched m).boundary U := by
  simp only [FiniteMultiGraph.boundary, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

/-- Every unswitched crossing occurrence other than the two moved ones is still
a crossing occurrence of `switched m`. -/
theorem bipBoundary_subset_boundary_union (U : Finset (Side m)) :
    bipBoundary U ⊆
      (switched m).boundary U ∪ ({(0, 0), (1, 1)} : Finset (Ix m × Ix m)) := by
  intro e he
  by_cases h0 : e = ((0, 0) : Ix m × Ix m)
  · exact Finset.mem_union_right _ (by simp [h0])
  · by_cases h1 : e = ((1, 1) : Ix m × Ix m)
    · exact Finset.mem_union_right _ (by simp [h1])
    · refine Finset.mem_union_left _ (mem_boundary_of ?_)
      rw [first_eq_inl h0 h1, second_eq_inr h0 h1]
      exact (mem_bipBoundary U e).mp he

/-- The switch is degree-preserving and moves two occurrences, so it can
destroy at most two boundary occurrences of any vertex set. -/
theorem card_bipBoundary_le (U : Finset (Side m)) :
    (bipBoundary U).card ≤ (switched m).boundaryCard U + 2 := by
  show (bipBoundary U).card ≤ ((switched m).boundary U).card + 2
  have h1 := Finset.card_le_card (bipBoundary_subset_boundary_union U)
  have h2 :
      ((switched m).boundary U ∪ ({(0, 0), (1, 1)} : Finset (Ix m × Ix m))).card
        ≤ ((switched m).boundary U).card
          + ({(0, 0), (1, 1)} : Finset (Ix m × Ix m)).card :=
    Finset.card_union_le _ _
  have h3 : ({(0, 0), (1, 1)} : Finset (Ix m × Ix m)).card ≤ 2 :=
    Finset.card_le_two
  exact h1.trans (h2.trans (Nat.add_le_add_left h3 _))

/-! ### The bound -/

/-- The vertex count, through the `FiniteModel` wrapper, as in `card_edge`. -/
theorem card_vertex (m : ℕ) :
    Fintype.card (switched m).vertex = 2 * (m + 2) := by
  show Fintype.card (Side m) = 2 * (m + 2)
  have hsum : Fintype.card (Side m) = Fintype.card (Ix m) + Fintype.card (Ix m) :=
    Fintype.card_sum
  have hIx : Fintype.card (Ix m) = m + 2 := Fintype.card_fin (m + 2)
  rw [hsum, hIx]
  ring

/-- The arithmetic endgame: `n|U| ≤ 2β`, `β ≤ c + 2` and `6|U| ≤ n|U|` give
`|U| ≤ c` as soon as `U` is nonempty.  Stated over bare naturals so that
`omega` sees only linear atoms. -/
theorem cheeger_endgame {u b c q : ℕ} (h1 : q ≤ 2 * b) (h2 : b ≤ c + 2)
    (h3 : 6 * u ≤ q) (h4 : 0 < u) : u ≤ c := by
  omega

theorem card_le_boundaryCard (m : ℕ) (hm : 4 ≤ m) (U : Finset (Side m))
    (hU : U.Nonempty) (hUle : U.card ≤ m + 2) :
    U.card ≤ (switched m).boundaryCard U := by
  have h1 : (m + 2) * U.card ≤ 2 * (bipBoundary U).card :=
    card_bipBoundary_lower U hUle
  have h2 : (bipBoundary U).card ≤ (switched m).boundaryCard U + 2 :=
    card_bipBoundary_le U
  have h3 : 6 * U.card ≤ (m + 2) * U.card :=
    Nat.mul_le_mul (by omega) (le_refl U.card)
  have h4 : 0 < U.card := Finset.card_pos.mpr hU
  exact cheeger_endgame h1 h2 h3 h4

/-- **The uniform Cheeger lower bound.**  For `n = m + 2 ≥ 6` every nonempty
vertex set of at most half the vertices has at least as many edge occurrences
leaving it as it has vertices, so the whole family expands at the fixed rate
`1`, independent of `m`.

Together with `rayleigh_testVector` this is the counterexample: uniform
expansion is compatible with the least Markov eigenvalue running to `-1`, and
the Cheeger / Dodziuk--Alon--Milman bound the published proof of `(4) → (1)`
invokes controls only the nonconstant spectrum near `+1`. -/
theorem hasCheegerLowerBound_one (m : ℕ) (hm : 4 ≤ m) :
    (switched m).HasCheegerLowerBound 1 := by
  refine ⟨one_pos, ?_⟩
  intro U hU hhalf
  rw [card_vertex] at hhalf
  have hUle : U.card ≤ m + 2 := by omega
  rw [one_mul]
  exact_mod_cast card_le_boundaryCard m hm U hU hUle

/-! ## The aggregate refutation -/

/-- An Archimedean choice of `m`: the defect `4/n²` beats any positive
constant, still with `n = m + 2 ≥ 6`. -/
theorem exists_small_defect (c : ℝ) (hc : 0 < c) :
    ∃ m : ℕ, 4 ≤ m ∧ 4 / ((m : ℝ) + 2) ^ 2 < c := by
  obtain ⟨k, hk⟩ := exists_nat_gt (4 / c)
  refine ⟨k + 4, by omega, ?_⟩
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpos : (0 : ℝ) < ((k : ℝ) + 6) ^ 2 := by positivity
  have hlt : 4 / c < (k : ℝ) + 6 := by linarith
  have h4 : 4 < ((k : ℝ) + 6) * c := (div_lt_iff₀ hc).mp hlt
  have hkey : (0 : ℝ) ≤ c * (((k : ℝ) + 6) * ((k : ℝ) + 5)) :=
    mul_nonneg hc.le (by positivity)
  have hexp : c * ((k : ℝ) + 6) ^ 2
      = ((k : ℝ) + 6) * c + c * (((k : ℝ) + 6) * ((k : ℝ) + 5)) := by ring
  have hfinal : 4 / ((k : ℝ) + 6) ^ 2 < c := by
    rw [div_lt_iff₀ hpos, hexp]
    linarith
  have hcast : ((k + 4 : ℕ) : ℝ) + 2 = (k : ℝ) + 6 := by push_cast; ring
  rw [hcast]
  exact hfinal

/-- **No uniform spectral gap above `-1`.**  For every `c > 0` the family has a
member that expands at rate `1`, is not bipartite, and whose normalized Markov
Rayleigh quotient is already below `-1 + c`.

So no implication of the shape "Cheeger constant at least `h` implies least
Markov eigenvalue at least `-1 + c(h)`" is available, with or without a
non-bipartiteness hypothesis.  That implication is what the published proof of
`(4) → (1)` uses; see the module header for what remains prose. -/
theorem no_uniform_spectral_gap (c : ℝ) (hc : 0 < c) :
    ∃ m : ℕ, 4 ≤ m ∧ (switched m).HasCheegerLowerBound 1 ∧
      ¬ IsBipartite (switched m) ∧
      rayleigh (switched m) (testVector m) < -1 + c := by
  obtain ⟨m, hm, hdef⟩ := exists_small_defect c hc
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine ⟨m' + 1, hm, hasCheegerLowerBound_one (m' + 1) hm, not_isBipartite m', ?_⟩
  rw [rayleigh_testVector]
  linarith

end KunSpectral
end NonsoficGroupsExist
