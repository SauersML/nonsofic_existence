import NonsoficGroupsExist.KunBoundary

/-!
# Finite propagation of permutation Markov iterates

The support of a `k`-step permutation average lies in the explicit `k`-step
forward neighborhood of the original support.  These elementary facts are the
locality input to Kun's removal argument.
-/

namespace NonsoficGroupsExist
namespace KunSupport

open KazhdanFiniteModel
open KazhdanGNS

variable {G : Type*} [Group G]

/-- Add the images of a vertex set under every labeled permutation. -/
noncomputable def forwardStep (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) : Finset M :=
  U ∪ S.biUnion fun s ↦ U.map (τ s).toEmbedding

/-- Iterated forward neighborhood. -/
noncomputable def forwardNeighborhood (M : FiniteModel)
    (τ : G → Equiv.Perm M) (S : Finset G) : ℕ → Finset M → Finset M
  | 0, U => U
  | k + 1, U => forwardStep M τ S (forwardNeighborhood M τ S k U)

/-- Add the inverse images of a vertex set under every labeled permutation. -/
noncomputable def backwardStep (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) : Finset M :=
  U ∪ S.biUnion fun s ↦ U.map (τ s).symm.toEmbedding

/-- Iterated backward neighborhood. -/
noncomputable def backwardNeighborhood (M : FiniteModel)
    (τ : G → Equiv.Perm M) (S : Finset G) : ℕ → Finset M → Finset M
  | 0, U => U
  | k + 1, U => backwardStep M τ S (backwardNeighborhood M τ S k U)

omit [Group G] in
theorem card_forwardStep_le
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) :
    (forwardStep M τ S U).card ≤ (S.card + 1) * U.card := by
  classical
  unfold forwardStep
  calc
    (U ∪ S.biUnion fun s ↦ U.map (τ s).toEmbedding).card ≤
        U.card + (S.biUnion fun s ↦ U.map (τ s).toEmbedding).card :=
      Finset.card_union_le _ _
    _ ≤ U.card + ∑ s ∈ S, (U.map (τ s).toEmbedding).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ = (S.card + 1) * U.card := by simp; ring

omit [Group G] in
theorem card_forwardNeighborhood_le
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (k : ℕ) (U : Finset M) :
    (forwardNeighborhood M τ S k U).card ≤
      (S.card + 1) ^ k * U.card := by
  induction k with
  | zero => simp [forwardNeighborhood]
  | succ k ih =>
      calc
        (forwardNeighborhood M τ S (k + 1) U).card =
            (forwardStep M τ S (forwardNeighborhood M τ S k U)).card := rfl
        _ ≤ (S.card + 1) *
            (forwardNeighborhood M τ S k U).card :=
          card_forwardStep_le M τ S _
        _ ≤ (S.card + 1) * ((S.card + 1) ^ k * U.card) := by
          gcongr
        _ = (S.card + 1) ^ (k + 1) * U.card := by
          rw [pow_succ]
          ring

omit [Group G] in
theorem card_backwardStep_le
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) :
    (backwardStep M τ S U).card ≤ (S.card + 1) * U.card := by
  classical
  unfold backwardStep
  calc
    (U ∪ S.biUnion fun s ↦ U.map (τ s).symm.toEmbedding).card ≤
        U.card +
          (S.biUnion fun s ↦ U.map (τ s).symm.toEmbedding).card :=
      Finset.card_union_le _ _
    _ ≤ U.card + ∑ s ∈ S, (U.map (τ s).symm.toEmbedding).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ = (S.card + 1) * U.card := by simp; ring

omit [Group G] in
theorem card_backwardNeighborhood_le
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (k : ℕ) (U : Finset M) :
    (backwardNeighborhood M τ S k U).card ≤
      (S.card + 1) ^ k * U.card := by
  induction k with
  | zero => simp [backwardNeighborhood]
  | succ k ih =>
      calc
        (backwardNeighborhood M τ S (k + 1) U).card =
            (backwardStep M τ S
              (backwardNeighborhood M τ S k U)).card := rfl
        _ ≤ (S.card + 1) *
            (backwardNeighborhood M τ S k U).card :=
          card_backwardStep_le M τ S _
        _ ≤ (S.card + 1) * ((S.card + 1) ^ k * U.card) := by
          gcongr
        _ = (S.card + 1) ^ (k + 1) * U.card := by
          rw [pow_succ]
          ring

omit [Group G] in
theorem backwardStep_mono (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) {U V : Finset M} (hUV : U ⊆ V) :
    backwardStep M τ S U ⊆ backwardStep M τ S V := by
  classical
  intro y hy
  simp only [backwardStep, Finset.mem_union,
    Finset.mem_biUnion, Finset.mem_map] at hy ⊢
  rcases hy with hy | ⟨s, hs, x, hx, hxy⟩
  · exact Or.inl (hUV hy)
  · exact Or.inr ⟨s, hs, x, hUV hx, hxy⟩

omit [Group G] in
theorem backwardNeighborhood_mono
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (k : ℕ) {U V : Finset M} (hUV : U ⊆ V) :
    backwardNeighborhood M τ S k U ⊆
      backwardNeighborhood M τ S k V := by
  induction k with
  | zero => exact hUV
  | succ k ih => exact backwardStep_mono M τ S ih

omit [Group G] in
theorem subset_backwardStep (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) : U ⊆ backwardStep M τ S U :=
  Finset.subset_union_left

omit [Group G] in
theorem backwardNeighborhood_subset_succ
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (k : ℕ) (U : Finset M) :
    backwardNeighborhood M τ S k U ⊆
      backwardNeighborhood M τ S (k + 1) U :=
  subset_backwardStep M τ S _

omit [Group G] in
/-- Backward neighborhoods are monotone in their time horizon. -/
theorem backwardNeighborhood_mono_time
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) {k l : ℕ} (hkl : k ≤ l) (U : Finset M) :
    backwardNeighborhood M τ S k U ⊆
      backwardNeighborhood M τ S l U := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction d with
  | zero => exact Finset.Subset.rfl
  | succ d ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using
          backwardNeighborhood_subset_succ M τ S (k + d) U)

omit [Group G] in
/-- Iterating one more backward step commutes with an existing number of
backward steps. -/
theorem backwardNeighborhood_step_commute
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (k : ℕ) (U : Finset M) :
    backwardNeighborhood M τ S k (backwardStep M τ S U) =
      backwardStep M τ S (backwardNeighborhood M τ S k U) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change backwardStep M τ S
          (backwardNeighborhood M τ S k (backwardStep M τ S U)) =
        backwardStep M τ S
          (backwardStep M τ S (backwardNeighborhood M τ S k U))
      rw [ih]

omit [Group G] in
theorem mem_forwardStep_of_mem (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) {s : G} (hs : s ∈ S) {x : M}
    (hx : x ∈ U) : τ s x ∈ forwardStep M τ S U := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨s, hs, Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩

omit [Group G] in
theorem mem_backwardStep_symm_of_mem
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) {s : G} (hs : s ∈ S) {x : M}
    (hx : x ∈ U) :
    (τ s).symm x ∈ backwardStep M τ S U := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨s, hs, Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩

omit [Group G] in
/-- Reversing a finite forward path gives a backward path of the same length. -/
theorem exists_source_mem_backwardNeighborhood
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (k : ℕ) (U : Finset M) {z : M}
    (hz : z ∈ forwardNeighborhood M τ S k U) :
    ∃ x ∈ U, x ∈ backwardNeighborhood M τ S k {z} := by
  induction k generalizing z with
  | zero =>
      exact ⟨z, by simpa [forwardNeighborhood] using hz,
        by simp [backwardNeighborhood]⟩
  | succ k ih =>
      change z ∈ forwardStep M τ S
        (forwardNeighborhood M τ S k U) at hz
      simp only [forwardStep, Finset.mem_union,
        Finset.mem_biUnion, Finset.mem_map] at hz
      rcases hz with hzPrev | ⟨s, hs, w, hw, hzw⟩
      · obtain ⟨x, hxU, hxBack⟩ := ih hzPrev
        exact ⟨x, hxU,
          backwardNeighborhood_subset_succ M τ S k {z} hxBack⟩
      · obtain ⟨x, hxU, hxBack⟩ := ih hw
        have hwBack : w ∈ backwardStep M τ S {z} := by
          have : (τ s).symm z ∈ backwardStep M τ S {z} :=
            mem_backwardStep_symm_of_mem M τ S {z} hs (by simp)
          simpa [← hzw] using this
        have hsingleton : ({w} : Finset M) ⊆ backwardStep M τ S {z} := by
          simpa using hwBack
        have hxLarger := backwardNeighborhood_mono M τ S k hsingleton hxBack
        rw [backwardNeighborhood_step_commute] at hxLarger
        exact ⟨x, hxU, hxLarger⟩

omit [Group G] in
/-- Removing the backward neighborhood of a forward neighborhood separates
all forward supports of the same radius. -/
theorem disjoint_forwardNeighborhood_of_disjoint_backwardForward
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (r : ℕ) (U V : Finset M)
    (hdisj : Disjoint V
      (backwardNeighborhood M τ S r
        (forwardNeighborhood M τ S r U))) :
    Disjoint (forwardNeighborhood M τ S r U)
      (forwardNeighborhood M τ S r V) := by
  rw [Finset.disjoint_left]
  intro z hzU hzV
  obtain ⟨x, hxV, hxBack⟩ :=
    exists_source_mem_backwardNeighborhood M τ S r V hzV
  have hsingleton : ({z} : Finset M) ⊆
      forwardNeighborhood M τ S r U := by
    simpa using hzU
  have hxLarge := backwardNeighborhood_mono M τ S r hsingleton hxBack
  exact Finset.disjoint_left.mp hdisj hxV hxLarge

omit [Group G] in
/-- The backward-forward exclusion set has an explicit degree bound. -/
theorem card_backwardForwardNeighborhood_le
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (r : ℕ) (U : Finset M) :
    (backwardNeighborhood M τ S r
      (forwardNeighborhood M τ S r U)).card ≤
        (S.card + 1) ^ (2 * r) * U.card := by
  calc
    (backwardNeighborhood M τ S r
        (forwardNeighborhood M τ S r U)).card ≤
      (S.card + 1) ^ r *
        (forwardNeighborhood M τ S r U).card :=
      card_backwardNeighborhood_le M τ S r _
    _ ≤ (S.card + 1) ^ r * ((S.card + 1) ^ r * U.card) := by
      gcongr
      exact card_forwardNeighborhood_le M τ S r U
    _ = (S.card + 1) ^ (2 * r) * U.card := by
      rw [two_mul, pow_add]
      ring

omit [Group G] in
theorem subset_forwardStep (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) : U ⊆ forwardStep M τ S U := by
  exact Finset.subset_union_left

omit [Group G] in
theorem forwardNeighborhood_subset_succ
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (k : ℕ) (U : Finset M) :
    forwardNeighborhood M τ S k U ⊆
      forwardNeighborhood M τ S (k + 1) U := by
  exact subset_forwardStep M τ S _

omit [Group G] in
theorem forwardNeighborhood_mono_time
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    {i j : ℕ} (hij : i ≤ j) (U : Finset M) :
    forwardNeighborhood M τ S i U ⊆
      forwardNeighborhood M τ S j U := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => simp
  | succ d ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using
          forwardNeighborhood_subset_succ M τ S (i + d) U)

omit [Group G] in
/-- A finite permutation average is additive. -/
theorem finiteModelAverage_add
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (x z : EuclideanSpace ℝ M) :
    finiteModelAverage M τ S (x + z) =
      finiteModelAverage M τ S x + finiteModelAverage M τ S z := by
  simp [finiteModelAverage, Finset.sum_add_distrib, smul_add]

omit [Group G] in
/-- A permutation average vanishes outside the forward step of the support. -/
theorem finiteModelAverage_eq_zero_of_not_mem_forwardStep
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (x : EuclideanSpace ℝ M) (U : Finset M)
    (hx : ∀ y, y ∉ U → x y = 0) {y : M}
    (hy : y ∉ forwardStep M τ S U) :
    finiteModelAverage M τ S x y = 0 := by
  classical
  have hterm (s : G) (hs : s ∈ S) : x ((τ s).symm y) = 0 := by
    apply hx
    intro hmem
    apply hy
    have himage := mem_forwardStep_of_mem M τ S U hs hmem
    simpa using himage
  have happly : finiteModelAverage M τ S x y =
      (S.card : ℝ)⁻¹ * (∑ s ∈ S, x ((τ s).symm y)) := by
    simp [finiteModelAverage]
  have hsum : ∑ s ∈ S, x ((τ s).symm y) = 0 := by
    exact Finset.sum_eq_zero fun s hs ↦ hterm s hs
  rw [happly, hsum, mul_zero]

/-- Every indicator trajectory has finite propagation in the actual model. -/
theorem finiteModelIndicatorIterate_eq_zero_of_not_mem_forwardNeighborhood
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) {y : A.model n}
    (hy : y ∉ forwardNeighborhood (A.model n) (A.map n) S k U) :
    finiteModelIndicatorIterate A n U S k y = 0 := by
  induction k generalizing y with
  | zero =>
      have hyU : y ∉ U := by simpa [forwardNeighborhood] using hy
      simp [finiteModelIndicatorIterate, indicator_apply, hyU]
  | succ k ih =>
      rw [finiteModelIndicatorIterate_succ]
      exact finiteModelAverage_eq_zero_of_not_mem_forwardStep
        (A.model n) (A.map n) S
        (finiteModelIndicatorIterate A n U S k)
        (forwardNeighborhood (A.model n) (A.map n) S k U)
        (fun z hz ↦ ih hz) hy

/-- The displacement at time `k` is supported in the `(k+1)`-step forward
neighborhood. -/
theorem finiteModelIndicatorDisplacement_eq_zero_of_not_mem
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) {y : A.model n}
    (hy : y ∉ forwardNeighborhood (A.model n) (A.map n) S (k + 1) U) :
    (finiteModelIndicatorIterate A n U S (k + 1) -
      finiteModelIndicatorIterate A n U S k) y = 0 := by
  have hySucc :=
    finiteModelIndicatorIterate_eq_zero_of_not_mem_forwardNeighborhood
      A n U S (k + 1) hy
  have hyPrev : y ∉ forwardNeighborhood (A.model n) (A.map n) S k U := by
    intro hmem
    exact hy (forwardNeighborhood_subset_succ
      (A.model n) (A.map n) S k U hmem)
  have hyZero :=
    finiteModelIndicatorIterate_eq_zero_of_not_mem_forwardNeighborhood
      A n U S k hyPrev
  simp [hySucc, hyZero]

/-- Markov iteration respects a disjoint union of initial sets. -/
theorem finiteModelIndicatorIterate_union
    (A : SoficApproximation G) (n : ℕ) (U V : Finset (A.model n))
    (hUV : Disjoint U V) (S : Finset G) (k : ℕ) :
    finiteModelIndicatorIterate A n (U ∪ V) S k =
      finiteModelIndicatorIterate A n U S k +
        finiteModelIndicatorIterate A n V S k := by
  induction k with
  | zero =>
      ext y
      have hnotBoth : ¬(y ∈ U ∧ y ∈ V) := by
        intro h
        exact Finset.disjoint_left.mp hUV h.1 h.2
      simp only [finiteModelIndicatorIterate, Function.iterate_zero_apply,
        indicator_apply, Finset.mem_union]
      by_cases hyU : y ∈ U <;> by_cases hyV : y ∈ V <;>
        simp [hyU, hyV] at hnotBoth ⊢
  | succ k ih =>
      rw [finiteModelIndicatorIterate_succ,
        finiteModelIndicatorIterate_succ,
        finiteModelIndicatorIterate_succ, ih,
        finiteModelAverage_add]

/-- Consequently Markov displacements are additive across a disjoint union. -/
theorem finiteModelIndicatorDisplacement_union
    (A : SoficApproximation G) (n : ℕ) (U V : Finset (A.model n))
    (hUV : Disjoint U V) (S : Finset G) (k : ℕ) :
    finiteModelIndicatorIterate A n (U ∪ V) S (k + 1) -
        finiteModelIndicatorIterate A n (U ∪ V) S k =
      (finiteModelIndicatorIterate A n U S (k + 1) -
          finiteModelIndicatorIterate A n U S k) +
        (finiteModelIndicatorIterate A n V S (k + 1) -
          finiteModelIndicatorIterate A n V S k) := by
  rw [finiteModelIndicatorIterate_union A n U V hUV,
    finiteModelIndicatorIterate_union A n U V hUV]
  abel

omit [Group G] in
/-- Squared norms add for vectors supported on disjoint finite sets. -/
theorem norm_add_sq_of_disjoint_support
    (M : FiniteModel) (x z : EuclideanSpace ℝ M) (U V : Finset M)
    (hUV : Disjoint U V) (hx : ∀ y, y ∉ U → x y = 0)
    (hz : ∀ y, y ∉ V → z y = 0) :
    ‖x + z‖ ^ 2 = ‖x‖ ^ 2 + ‖z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hyU : y ∈ U
  · have hyV : y ∉ V := fun hy ↦ Finset.disjoint_left.mp hUV hyU hy
    change (x y + z y) ^ 2 = x y ^ 2 + z y ^ 2
    rw [hz y hyV]
    simp
  · change (x y + z y) ^ 2 = x y ^ 2 + z y ^ 2
    rw [hx y hyU]
    simp

end KunSupport
end NonsoficGroupsExist
