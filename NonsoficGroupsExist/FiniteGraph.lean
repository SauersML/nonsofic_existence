import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import NonsoficGroupsExist.Sofic

/-!
# Finite multigraphs and median edge cases

Edges are bundled occurrences rather than endpoint pairs.  Consequently all
boundary cardinalities count parallel edges with their multiplicities.
-/

namespace NonsoficGroupsExist

/-- A finite loopless multigraph.  Distinct elements of `edge` may have the
same endpoints and remain distinct edge occurrences. -/
structure FiniteMultiGraph where
  vertex : FiniteModel
  edge : FiniteModel
  first : edge → vertex
  second : edge → vertex
  loopless : ∀ e, first e ≠ second e

/-- An occurrence-level witness that two finite multigraphs differ by edge
edits.  Kept occurrences are bijected and preserve their unordered endpoint
pair; parallel occurrences therefore remain distinct throughout. -/
structure EdgeEditWitness (X Z : FiniteMultiGraph) (e : X.vertex ≃ Z.vertex) where
  sourceKept : Finset X.edge
  targetKept : Finset Z.edge
  edgeEquiv : sourceKept ≃ targetKept
  preservesEndpoints : ∀ a : sourceKept,
    (e (X.first a.1) = Z.first (edgeEquiv a).1 ∧
      e (X.second a.1) = Z.second (edgeEquiv a).1) ∨
    (e (X.first a.1) = Z.second (edgeEquiv a).1 ∧
      e (X.second a.1) = Z.first (edgeEquiv a).1)

namespace EdgeEditWitness

variable {X Z : FiniteMultiGraph} {e : X.vertex ≃ Z.vertex}

/-- Deleted source occurrences. -/
def sourceUnmatched (W : EdgeEditWitness X Z e) : Finset X.edge :=
  Finset.univ \ W.sourceKept

/-- Inserted target occurrences. -/
def targetUnmatched (W : EdgeEditWitness X Z e) : Finset Z.edge :=
  Finset.univ \ W.targetKept

/-- Total number of occurrence edits represented by the witness. -/
def unmatchedCount (W : EdgeEditWitness X Z e) : ℕ :=
  W.sourceUnmatched.card + W.targetUnmatched.card

end EdgeEditWitness

namespace FiniteMultiGraph

/-- The occurrence-sensitive subgraph induced by a finite vertex set. -/
def induce (X : FiniteMultiGraph) (U : Finset X.vertex) : FiniteMultiGraph where
  vertex :=
    { carrier := ↑U
      fintype := inferInstance
      decidableEq := inferInstance }
  edge :=
    { carrier := {e : X.edge // X.first e ∈ U ∧ X.second e ∈ U}
      fintype := inferInstance
      decidableEq := inferInstance }
  first e := ⟨X.first e.1, e.2.1⟩
  second e := ⟨X.second e.1, e.2.2⟩
  loopless e := by
    intro h
    exact X.loopless e.1 (congrArg Subtype.val h)

/-- Boundary edge occurrences of a vertex finset. -/
def boundary (X : FiniteMultiGraph) (U : Finset X.vertex) : Finset X.edge :=
  Finset.univ.filter fun e ↦
    (X.first e ∈ U ∧ X.second e ∉ U) ∨ (X.second e ∈ U ∧ X.first e ∉ U)

/-- Boundary cardinality, counting edge occurrences and hence multiplicity. -/
def boundaryCard (X : FiniteMultiGraph) (U : Finset X.vertex) : ℕ :=
  (X.boundary U).card

/-- Multiplicity with the stored orientation of an occurrence. -/
def directedMultiplicity (X : FiniteMultiGraph) (x y : X.vertex) : ℕ :=
  (Finset.univ.filter fun a ↦ X.first a = x ∧ X.second a = y).card

/-- Ordered endpoint pairs crossing a vertex cut. -/
def crossingPairs (X : FiniteMultiGraph) (U : Finset X.vertex) :
    Finset (X.vertex × X.vertex) :=
  Finset.univ.filter fun p ↦
    (p.1 ∈ U ∧ p.2 ∉ U) ∨ (p.2 ∈ U ∧ p.1 ∉ U)

theorem sum_directedMultiplicity_crossingPairs
    (X : FiniteMultiGraph) (U : Finset X.vertex) :
    ∑ p ∈ X.crossingPairs U, X.directedMultiplicity p.1 p.2 =
      X.boundaryCard U := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset X.edge) (X.crossingPairs U)
    (fun a ↦ (X.first a, X.second a))
  calc
    ∑ p ∈ X.crossingPairs U, X.directedMultiplicity p.1 p.2 =
        ∑ p ∈ X.crossingPairs U,
          (Finset.univ.filter fun a : X.edge ↦
            (X.first a, X.second a) = p).card := by
      apply Finset.sum_congr rfl
      intro p _
      unfold directedMultiplicity
      congr 1
      ext a
      simp [Prod.ext_iff]
    _ = X.boundaryCard U := by
      simpa [crossingPairs, boundaryCard, boundary] using hfiber

/-- Transport a multigraph along a vertex equivalence.  The edge-occurrence
type is unchanged, so multiplicities are preserved definitionally. -/
abbrev transport (X : FiniteMultiGraph) (Z : FiniteModel) (e : X.vertex ≃ Z) :
    FiniteMultiGraph where
  vertex := Z
  edge := X.edge
  first a := e (X.first a)
  second a := e (X.second a)
  loopless a h := X.loopless a (e.injective h)

@[simp] theorem transport_first (X : FiniteMultiGraph) (Z : FiniteModel)
    (e : X.vertex ≃ Z) (a : X.edge) :
    (X.transport Z e).first a = e (X.first a) := rfl

@[simp] theorem transport_second (X : FiniteMultiGraph) (Z : FiniteModel)
    (e : X.vertex ≃ Z) (a : X.edge) :
    (X.transport Z e).second a = e (X.second a) := rfl

/-- Every edge occurrence belongs to the transported boundary exactly when
the original occurrence belongs to the original boundary. -/
theorem transport_boundary (X : FiniteMultiGraph) (Z : FiniteModel)
    (e : X.vertex ≃ Z) (U : Finset X.vertex) :
    (X.transport Z e).boundary (U.map e.toEmbedding) = X.boundary U := by
  have hmem (x : X.vertex) : e x ∈ U.map e.toEmbedding ↔ x ∈ U := by simp
  unfold boundary transport
  refine Finset.filter_congr fun a _ ↦ ?_
  rw [hmem (X.first a), hmem (X.second a)]

theorem transport_boundaryCard (X : FiniteMultiGraph) (Z : FiniteModel)
    (e : X.vertex ≃ Z) (U : Finset X.vertex) :
    (X.transport Z e).boundaryCard (U.map e.toEmbedding) = X.boundaryCard U := by
  rw [boundaryCard, boundaryCard, transport_boundary]

/-- Multiplicity of the unordered endpoint pair `{x,y}`.  Since graphs are
loopless, every occurrence is counted at exactly its two distinct endpoints. -/
def edgeMultiplicity (X : FiniteMultiGraph) (x y : X.vertex) : ℕ :=
  (Finset.univ.filter fun a ↦
    (X.first a = x ∧ X.second a = y) ∨
      (X.first a = y ∧ X.second a = x)).card

theorem edgeMultiplicity_eq_directed_add_reverse
    (X : FiniteMultiGraph) (x y : X.vertex) :
    X.edgeMultiplicity x y =
      X.directedMultiplicity x y + X.directedMultiplicity y x := by
  classical
  let F := Finset.univ.filter fun a : X.edge ↦
    X.first a = x ∧ X.second a = y
  let R := Finset.univ.filter fun a : X.edge ↦
    X.first a = y ∧ X.second a = x
  have hdisj : Disjoint F R := by
    apply Finset.disjoint_left.mpr
    intro a haF haR
    have hF : X.first a = x ∧ X.second a = y := by simpa [F] using haF
    have hR : X.first a = y ∧ X.second a = x := by simpa [R] using haR
    exact X.loopless a (hF.1.trans hR.2.symm)
  calc
    X.edgeMultiplicity x y = (F ∪ R).card := by
      unfold edgeMultiplicity
      congr 1
      ext a
      simp [F, R]
    _ = F.card + R.card := Finset.card_union_of_disjoint hdisj
    _ = X.directedMultiplicity x y + X.directedMultiplicity y x := by
      rfl

theorem directedMultiplicity_le_edgeMultiplicity
    (X : FiniteMultiGraph) (x y : X.vertex) :
    X.directedMultiplicity x y ≤ X.edgeMultiplicity x y := by
  apply Finset.card_le_card
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inl ha

theorem sum_reverseDirectedMultiplicity_crossingPairs
    (X : FiniteMultiGraph) (U : Finset X.vertex) :
    ∑ p ∈ X.crossingPairs U, X.directedMultiplicity p.2 p.1 =
      X.boundaryCard U := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset X.edge) (X.crossingPairs U)
    (fun a ↦ (X.second a, X.first a))
  calc
    ∑ p ∈ X.crossingPairs U, X.directedMultiplicity p.2 p.1 =
        ∑ p ∈ X.crossingPairs U,
          (Finset.univ.filter fun a : X.edge ↦
            (X.second a, X.first a) = p).card := by
      apply Finset.sum_congr rfl
      intro p _
      unfold directedMultiplicity
      congr 1
      ext a
      simp [Prod.ext_iff, and_comm]
    _ = X.boundaryCard U := by
      simpa [crossingPairs, boundaryCard, boundary, and_comm, or_comm] using hfiber

theorem sum_edgeMultiplicity_crossingPairs
    (X : FiniteMultiGraph) (U : Finset X.vertex) :
    ∑ p ∈ X.crossingPairs U, X.edgeMultiplicity p.1 p.2 =
      2 * X.boundaryCard U := by
  calc
    ∑ p ∈ X.crossingPairs U, X.edgeMultiplicity p.1 p.2 =
        ∑ p ∈ X.crossingPairs U,
          (X.directedMultiplicity p.1 p.2 +
            X.directedMultiplicity p.2 p.1) := by
      apply Finset.sum_congr rfl
      intro p _
      exact X.edgeMultiplicity_eq_directed_add_reverse p.1 p.2
    _ = (∑ p ∈ X.crossingPairs U, X.directedMultiplicity p.1 p.2) +
        ∑ p ∈ X.crossingPairs U, X.directedMultiplicity p.2 p.1 := by
      rw [Finset.sum_add_distrib]
    _ = 2 * X.boundaryCard U := by
      rw [X.sum_directedMultiplicity_crossingPairs,
        X.sum_reverseDirectedMultiplicity_crossingPairs]
      omega

/-- Occurrence-sensitive edit distance after identifying the vertex sets.
Summing over ordered endpoint pairs counts every undirected occurrence twice;
this fixed factor is harmless for all negligible-density statements. -/
def editDistance (X Z : FiniteMultiGraph) (e : X.vertex ≃ Z.vertex) : ℕ :=
  ∑ x, ∑ y,
    ((X.edgeMultiplicity x y - Z.edgeMultiplicity (e x) (e y)) +
      (Z.edgeMultiplicity (e x) (e y) - X.edgeMultiplicity x y))

@[simp] theorem editDistance_self (X : FiniteMultiGraph) :
    X.editDistance X (Equiv.refl X.vertex) = 0 := by
  simp [editDistance]

/-- Strict superlevel set of a function on the vertices. -/
noncomputable def superlevel (X : FiniteMultiGraph) (g : X.vertex → ℝ) (t : ℝ) :
    Finset X.vertex :=
  Finset.univ.filter fun x ↦ t < g x

/-- Total absolute variation over edge occurrences. -/
def edgeVariation (X : FiniteMultiGraph) (g : X.vertex → ℝ) : ℝ :=
  ∑ e, |g (X.first e) - g (X.second e)|

/-- Remove the bottom positive layer of height `m`. -/
def peel (m x : ℝ) : ℝ := max (x - m) 0

theorem peel_nonnegative (m x : ℝ) : 0 ≤ peel m x := by
  exact le_max_right _ _

theorem value_eq_layer_add_peel {m x : ℝ} (hx : 0 ≤ x)
    (hm : 0 ≤ m) (hmin : 0 < x → m ≤ x) :
    x = (if 0 < x then m else 0) + peel m x := by
  by_cases hpos : 0 < x
  · rw [if_pos hpos, peel, max_eq_left (sub_nonneg.mpr (hmin hpos))]
    ring
  · have hx0 : x = 0 := le_antisymm (not_lt.mp hpos) hx
    subst x
    simp [peel, hm]

/-- Peeling a common bottom layer decomposes the variation of one edge into
its boundary contribution and its residual variation. -/
theorem abs_sub_eq_layer_add_peel {m a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : 0 ≤ m) (hma : 0 < a → m ≤ a) (hmb : 0 < b → m ≤ b) :
    |a - b| =
      m * (if (0 < a ∧ ¬ 0 < b) ∨ (0 < b ∧ ¬ 0 < a) then 1 else 0) +
        |peel m a - peel m b| := by
  by_cases hapos : 0 < a <;> by_cases hbpos : 0 < b
  · rw [if_neg (by simp [hapos, hbpos]), peel, peel,
      max_eq_left (sub_nonneg.mpr (hma hapos)),
      max_eq_left (sub_nonneg.mpr (hmb hbpos))]
    simp only [mul_zero, zero_add]
    congr 1
    ring
  · have hb0 : b = 0 := le_antisymm (not_lt.mp hbpos) hb
    subst b
    have hpa : peel m a = a - m := max_eq_left (sub_nonneg.mpr (hma hapos))
    have hp0 : peel m 0 = 0 := by simp [peel, hm]
    rw [hpa, hp0]
    simp [hapos, abs_of_nonneg ha, abs_of_nonneg (sub_nonneg.mpr (hma hapos))]
  · have ha0 : a = 0 := le_antisymm (not_lt.mp hapos) ha
    subst a
    have hp0 : peel m 0 = 0 := by simp [peel, hm]
    have hpb : peel m b = b - m := max_eq_left (sub_nonneg.mpr (hmb hbpos))
    rw [hp0, hpb]
    simp [hbpos, abs_of_nonneg hb, abs_of_nonpos (sub_nonpos.mpr (hmb hbpos))]
  · have ha0 : a = 0 := le_antisymm (not_lt.mp hapos) ha
    have hb0 : b = 0 := le_antisymm (not_lt.mp hbpos) hb
    subst a
    subst b
    simp [peel, hm]

theorem sum_eq_layer_add_peel (X : FiniteMultiGraph) (g : X.vertex → ℝ) (m : ℝ)
    (hg : ∀ x, 0 ≤ g x) (hm : 0 ≤ m) (hmin : ∀ x, 0 < g x → m ≤ g x) :
    ∑ x, g x = m * (X.superlevel g 0).card + ∑ x, peel m (g x) := by
  calc
    ∑ x, g x = ∑ x, ((if 0 < g x then m else 0) + peel m (g x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact value_eq_layer_add_peel (hg x) hm (hmin x)
    _ = (∑ x, if 0 < g x then m else 0) + ∑ x, peel m (g x) :=
      Finset.sum_add_distrib
    _ = m * (X.superlevel g 0).card + ∑ x, peel m (g x) := by
      congr 1
      rw [← Finset.sum_filter]
      simp [superlevel, mul_comm]

theorem edgeVariation_eq_layer_add_peel (X : FiniteMultiGraph) (g : X.vertex → ℝ)
    (m : ℝ) (hg : ∀ x, 0 ≤ g x) (hm : 0 ≤ m)
    (hmin : ∀ x, 0 < g x → m ≤ g x) :
    X.edgeVariation g = m * X.boundaryCard (X.superlevel g 0) +
      X.edgeVariation (fun x ↦ peel m (g x)) := by
  calc
    X.edgeVariation g = ∑ e, (m *
        (if (0 < g (X.first e) ∧ ¬ 0 < g (X.second e)) ∨
          (0 < g (X.second e) ∧ ¬ 0 < g (X.first e)) then 1 else 0) +
        |peel m (g (X.first e)) - peel m (g (X.second e))|) := by
      apply Finset.sum_congr rfl
      intro e _
      exact abs_sub_eq_layer_add_peel (hg _) (hg _) hm (hmin _) (hmin _)
    _ = m * (∑ e, if (0 < g (X.first e) ∧ ¬ 0 < g (X.second e)) ∨
          (0 < g (X.second e) ∧ ¬ 0 < g (X.first e)) then 1 else 0) +
        X.edgeVariation (fun x ↦ peel m (g x)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    _ = m * X.boundaryCard (X.superlevel g 0) +
        X.edgeVariation (fun x ↦ peel m (g x)) := by
      congr 2
      simp [boundaryCard, boundary, superlevel]

/-- The explicit quantitative assertion that every nonempty set of at most
half the vertices has boundary ratio at least `h`. -/
def HasCheegerLowerBound (X : FiniteMultiGraph) (h : ℝ) : Prop :=
  0 < h ∧ ∀ U : Finset X.vertex, U.Nonempty →
    2 * U.card ≤ Fintype.card X.vertex →
      h * U.card ≤ X.boundaryCard U

theorem transport_hasCheegerLowerBound (X : FiniteMultiGraph) (Z : FiniteModel)
    (e : X.vertex ≃ Z) {h : ℝ} (hX : X.HasCheegerLowerBound h) :
    (X.transport Z e).HasCheegerLowerBound h := by
  refine ⟨hX.1, ?_⟩
  intro W hW hhalf
  let U : Finset X.vertex := W.map e.symm.toEmbedding
  have hmap : U.map e.toEmbedding = W := by
    ext z
    simp [U]
  have hU : U.Nonempty := by simpa [U] using hW
  have hhalfU : 2 * U.card ≤ Fintype.card X.vertex := by
    simpa [U, Fintype.card_congr e] using hhalf
  have hb := hX.2 U hU hhalfU
  calc
    h * W.card = h * U.card := by simp [U]
    _ ≤ X.boundaryCard U := hb
    _ = (X.transport Z e).boundaryCard W := by
      rw [← hmap, transport_boundaryCard]

/-- Finite combinatorial layer-cake inequality.  The proof recursively peels
the least positive function value, so it requires no measure theory. -/
theorem nonnegative_coarea (X : FiniteMultiGraph) {h : ℝ}
    (hcheeger : X.HasCheegerLowerBound h) (g : X.vertex → ℝ)
    (hg : ∀ x, 0 ≤ g x)
    (hsmall : ∀ t, 0 ≤ t →
      2 * (X.superlevel g t).card ≤ Fintype.card X.vertex) :
    h * ∑ x, g x ≤ X.edgeVariation g := by
  classical
  let U := X.superlevel g 0
  by_cases hU : U.Nonempty
  · let values := U.image g
    have hvalues : values.Nonempty := hU.image g
    let m := values.min' hvalues
    have hm_mem : m ∈ values := Finset.min'_mem values hvalues
    obtain ⟨x₀, hx₀U, hx₀m⟩ := Finset.mem_image.mp hm_mem
    have hx₀pos : 0 < g x₀ := by simpa [U, superlevel] using hx₀U
    have hmpos : 0 < m := by simpa [hx₀m] using hx₀pos
    have hm : 0 ≤ m := hmpos.le
    have hmin : ∀ x, 0 < g x → m ≤ g x := by
      intro x hx
      apply Finset.min'_le values (g x)
      exact Finset.mem_image.mpr ⟨x, by simpa [U, superlevel] using hx, rfl⟩
    let g' : X.vertex → ℝ := fun x ↦ peel m (g x)
    have hg' : ∀ x, 0 ≤ g' x := fun x ↦ peel_nonnegative _ _
    have hlevels (t : ℝ) (ht : 0 ≤ t) :
        X.superlevel g' t = X.superlevel g (t + m) := by
      ext x
      simp [g', superlevel, peel, ht, lt_sub_iff_add_lt]
    have hsmall' : ∀ t, 0 ≤ t →
        2 * (X.superlevel g' t).card ≤ Fintype.card X.vertex := by
      intro t ht
      rw [hlevels t ht]
      exact hsmall (t + m) (add_nonneg ht hm)
    have hsupport_subset : X.superlevel g' 0 ⊆ U := by
      intro x hx
      have hx' : 0 < g x - m := by
        simpa [g', superlevel, peel] using hx
      have hxpos : 0 < g x := hm.trans_lt ((sub_pos.mp hx'))
      simpa [U, superlevel] using hxpos
    have hx₀_not : x₀ ∉ X.superlevel g' 0 := by
      simp [g', superlevel, peel, hx₀m]
    have hsupport_ne : X.superlevel g' 0 ≠ U := by
      intro heq
      exact hx₀_not (heq.symm ▸ hx₀U)
    have hdecrease : (X.superlevel g' 0).card < U.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hsupport_subset, hsupport_ne⟩)
    have hinduction : h * ∑ x, g' x ≤ X.edgeVariation g' :=
      nonnegative_coarea X hcheeger g' hg' hsmall'
    have hboundary : h * U.card ≤ X.boundaryCard U :=
      hcheeger.2 U hU (by simpa [U] using hsmall 0 le_rfl)
    have hlayer : m * (h * U.card) ≤ m * X.boundaryCard U :=
      mul_le_mul_of_nonneg_left hboundary hm
    rw [sum_eq_layer_add_peel X g m hg hm hmin,
      edgeVariation_eq_layer_add_peel X g m hg hm hmin]
    change h * (m * U.card + ∑ x, g' x) ≤
      m * X.boundaryCard U + X.edgeVariation g'
    calc
      h * (m * U.card + ∑ x, g' x) =
          m * (h * U.card) + h * ∑ x, g' x := by ring
      _ ≤ m * X.boundaryCard U + X.edgeVariation g' :=
        add_le_add hlayer hinduction
  · have hgzero : ∀ x, g x = 0 := by
      intro x
      have hnot : ¬ 0 < g x := by
        intro hx
        exact hU ⟨x, by simpa [U, superlevel] using hx⟩
      exact le_antisymm (not_lt.mp hnot) (hg x)
    simp [hgzero, edgeVariation]
termination_by (X.superlevel g 0).card
decreasing_by simpa [U] using hdecrease

/-- A finite-sample median, stated without division so singleton and empty
edge cases remain explicit. -/
def IsMedian {Y : FiniteModel} (f : Y → ℝ) (c : ℝ) : Prop :=
  2 * (Finset.univ.filter fun y ↦ c < f y).card ≤ Fintype.card Y ∧
    2 * (Finset.univ.filter fun y ↦ f y < c).card ≤ Fintype.card Y

/-- The audited one-vertex endpoint of the co-area argument: the two median
inequalities force the unique value to equal the median. -/
theorem IsMedian.eq_of_subsingleton {Y : FiniteModel} [Nonempty Y] [Subsingleton Y]
    {f : Y → ℝ} {c : ℝ} (hc : IsMedian f c) : ∀ y, f y = c := by
  intro y
  letI : Unique Y :=
    { default := Classical.choice (inferInstance : Nonempty Y)
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  have hcard : Fintype.card Y = 1 := Fintype.card_unique
  have hnotGreater : ¬c < f y := by
    intro hy
    have hfilter : (Finset.univ.filter fun z ↦ c < f z) = Finset.univ := by
      ext z
      simp [Subsingleton.elim z y, hy]
    have h := hc.1
    rw [hfilter, Finset.card_univ, hcard] at h
    norm_num at h
  have hnotLess : ¬f y < c := by
    intro hy
    have hfilter : (Finset.univ.filter fun z ↦ f z < c) = Finset.univ := by
      ext z
      simp [Subsingleton.elim z y, hy]
    have h := hc.2
    rw [hfilter, Finset.card_univ, hcard] at h
    norm_num at h
  exact le_antisymm (not_lt.mp hnotGreater) (not_lt.mp hnotLess)

/-- Positive part of a real number. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- Negative part of a real number, recorded as a nonnegative number. -/
def negativePart (x : ℝ) : ℝ := max (-x) 0

theorem abs_eq_positivePart_add_negativePart (x : ℝ) :
    |x| = positivePart x + negativePart x := by
  rcases le_total 0 x with hx | hx
  · simp [positivePart, negativePart, hx, abs_of_nonneg hx]
  · simp [positivePart, negativePart, hx, abs_of_nonpos hx]

/-- The pointwise edge identity used when the positive and negative co-area
bounds are added. -/
theorem positivePart_edge_add_negativePart_edge (x y : ℝ) :
    |positivePart x - positivePart y| + |negativePart x - negativePart y| = |x - y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · simp [positivePart, negativePart, hx, hy]
  · have hxy : 0 ≤ x - y := sub_nonneg.mpr (hy.trans hx)
    simp [positivePart, negativePart, hx, hy, abs_of_nonneg hx, abs_of_nonpos hy,
      sub_eq_add_neg]
    exact (abs_of_nonneg hxy).symm
  · have hxy : x - y ≤ 0 := sub_nonpos.mpr (hx.trans hy)
    simp [positivePart, negativePart, hx, hy, abs_of_nonpos hx, abs_of_nonneg hy,
      sub_eq_add_neg, add_comm]
    have hxy' : x + -y ≤ 0 := by simpa [sub_eq_add_neg] using hxy
    rw [abs_of_nonpos hxy']
    simp
  · rw [show positivePart x = 0 by simp [positivePart, hx],
      show positivePart y = 0 by simp [positivePart, hy],
      show negativePart x = -x by simp [negativePart, hx],
      show negativePart y = -y by simp [negativePart, hy]]
    simp only [sub_self, abs_zero, zero_add, sub_eq_add_neg, neg_neg]
    have hneg : -x + y = -(x + -y) := by simp [add_comm]
    rw [hneg, abs_neg]

/-- The manuscript's `ℓ1` co-area estimate, in denominator-free form. -/
theorem coarea_mul (X : FiniteMultiGraph) {h : ℝ}
    (hcheeger : X.HasCheegerLowerBound h) (f : X.vertex → ℝ) (c : ℝ)
    (hc : IsMedian f c) :
    h * ∑ x, |f x - c| ≤ X.edgeVariation f := by
  let gp : X.vertex → ℝ := fun x ↦ positivePart (f x - c)
  let gn : X.vertex → ℝ := fun x ↦ negativePart (f x - c)
  have hgp : ∀ x, 0 ≤ gp x := fun x ↦ le_max_right _ _
  have hgn : ∀ x, 0 ≤ gn x := fun x ↦ le_max_right _ _
  have hsmallp : ∀ t, 0 ≤ t →
      2 * (X.superlevel gp t).card ≤ Fintype.card X.vertex := by
    intro t ht
    have hsubset : X.superlevel gp t ⊆
        Finset.univ.filter (fun x ↦ c < f x) := by
      intro x hx
      have htx : t < f x - c := by
        have hx' : t < max (f x - c) 0 := by
          simpa [gp, positivePart, superlevel] using hx
        exact (lt_max_iff.mp hx').resolve_right (not_lt_of_ge ht)
      have hcx : c < f x := by
        have : t + c < f x := (lt_sub_iff_add_lt.mp htx)
        exact (le_add_of_nonneg_left ht).trans_lt (by simpa [add_comm] using this)
      simpa using hcx
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)).trans hc.1
  have hsmalln : ∀ t, 0 ≤ t →
      2 * (X.superlevel gn t).card ≤ Fintype.card X.vertex := by
    intro t ht
    have hsubset : X.superlevel gn t ⊆
        Finset.univ.filter (fun x ↦ f x < c) := by
      intro x hx
      have htx : t < -(f x - c) := by
        have hx' : t < max (-(f x - c)) 0 := by
          simpa [gn, negativePart, superlevel] using hx
        exact (lt_max_iff.mp hx').resolve_right (not_lt_of_ge ht)
      have hxc : f x < c := by
        have : t + f x < c := by
          rw [neg_sub] at htx
          exact lt_sub_iff_add_lt.mp htx
        exact (le_add_of_nonneg_left ht).trans_lt (by simpa [add_comm] using this)
      simpa using hxc
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)).trans hc.2
  have hp := nonnegative_coarea X hcheeger gp hgp hsmallp
  have hn := nonnegative_coarea X hcheeger gn hgn hsmalln
  have hsum : (∑ x, |f x - c|) = (∑ x, gp x) + ∑ x, gn x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact abs_eq_positivePart_add_negativePart (f x - c)
  have hedge : X.edgeVariation gp + X.edgeVariation gn = X.edgeVariation f := by
    rw [edgeVariation, edgeVariation, edgeVariation, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [show gp (X.first e) = positivePart (f (X.first e) - c) by rfl,
      show gp (X.second e) = positivePart (f (X.second e) - c) by rfl,
      show gn (X.first e) = negativePart (f (X.first e) - c) by rfl,
      show gn (X.second e) = negativePart (f (X.second e) - c) by rfl,
      positivePart_edge_add_negativePart_edge]
    congr 1
    ring
  calc
    h * ∑ x, |f x - c| = h * ((∑ x, gp x) + ∑ x, gn x) := by rw [hsum]
    _ = h * ∑ x, gp x + h * ∑ x, gn x := by ring
    _ ≤ X.edgeVariation gp + X.edgeVariation gn := add_le_add hp hn
    _ = X.edgeVariation f := hedge

/-- The displayed co-area inequality from the manuscript. -/
theorem coarea (X : FiniteMultiGraph) {h : ℝ}
    (hcheeger : X.HasCheegerLowerBound h) (f : X.vertex → ℝ) (c : ℝ)
    (hc : IsMedian f c) :
    ∑ x, |f x - c| ≤ (1 / h) * X.edgeVariation f := by
  have hmul := coarea_mul X hcheeger f c hc
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ hcheeger.1).2
  simpa [mul_comm] using hmul

end FiniteMultiGraph
end NonsoficGroupsExist
