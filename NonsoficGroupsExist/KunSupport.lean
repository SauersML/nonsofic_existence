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
theorem mem_forwardStep_of_mem (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) {s : G} (hs : s ∈ S) {x : M}
    (hx : x ∈ U) : τ s x ∈ forwardStep M τ S U := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  exact ⟨s, hs, Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩

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

end KunSupport
end NonsoficGroupsExist
