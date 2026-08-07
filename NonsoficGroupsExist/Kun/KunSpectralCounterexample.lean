import NonsoficGroupsExist.Matching.FiniteGraph
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fintype.Sum
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

That argument is prose.  This module makes the load-bearing half of it a
checked statement, so the critique of the literature is verified the same way
the rest of the development is.

## What is proved here

A single explicit family `switched m`: the complete bipartite graph `K_{n,n}`
with `n = m + 2`, carrying one degree-preserving two-edge switch.

* `neg_one_le_rayleigh` — the normalized Markov Rayleigh quotient is at least
  `-1` for every test function on every finite multigraph, with equality only
  when every edge reverses sign.  So `-1` is exactly the boundary being
  approached below, and the family is not degenerate.
* `rayleigh_testVector` — one explicit vector, `+1` on the left side and `-1`
  on the right, has Rayleigh quotient exactly `-1 + 4/n²`.  Since the least
  eigenvalue of the normalized Markov operator is at most the Rayleigh quotient
  of any nonzero vector, the bottom of the spectrum is within `4/n²` of `-1`.
* `not_isBipartite` — for `n ≥ 3` the family is not bipartite, exhibited by the
  triangle the switch creates.  This is what defeats the obvious repair of
  adding a non-bipartiteness hypothesis to Theorem 3: the graphs are genuinely
  non-bipartite and the least eigenvalue still runs to `-1`.

## Formalization boundary

**The uniform Cheeger lower bound for the family is not formalized.**  It is
the load-bearing half: without it the family says nothing, because ANY
bipartite graph has Rayleigh quotient `-1` and the content of the counterexample
is precisely that uniform expansion does not prevent this.  The intended proof
is short and elementary -- for `U` with `2|U| ≤ 2n`, splitting `|U|` as `a + b`
across the two sides gives `K_{n,n}` boundary `a(n-b) + b(n-a) = n(a+b) - 2ab`,
and `4ab ≤ (a+b)² ≤ n(a+b)` gives boundary `≥ n|U|/2`; the switch moves two
occurrences, so the switched graph loses at most 2, leaving `≥ |U|` for `n ≥ 6`
-- but the Finset counting has not been written, so it is not claimed.

The second missing step is the repetition argument: forming one sequence from
many copies of each `switched m`, so that repeating the extremal vector across
all copies makes its `L²` norm proportional to the square root of the total
vertex count and the additive `L^∞` error in condition `(1)` cannot absorb the
defect.  That is bookkeeping over the family; the spectral fact above is the
part the published proof gets wrong.

Until the Cheeger bound is formalized, this module verifies the SPECTRAL half
of the README's literature audit and not the whole of it.  Treat the prose
critique as unverified in that respect.

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

`∑ₑ (f(u) + f(v))² ≥ 0` is the whole proof, and it is also the reason the
bound is tight exactly at bipartite graphs -- equality forces `f(u) = -f(v)`
across every edge. -/
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
runs to `-1`.  Granting the uniform Cheeger bound for the family -- the
unformalized half; see the module header -- no bound of the form "Cheeger
constant at least `h` implies least eigenvalue at least `-1 + c(h)`" can
hold. -/
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

end KunSpectral
end NonsoficGroupsExist
