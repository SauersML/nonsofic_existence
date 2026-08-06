import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The stack dichotomy

Over a field, the stacked matrix `[B₀; B₁]` either admits a scalar
left inverse in the paired form consumed by the fullness transports,
or it has a nontrivial kernel vector — the input to the extraction
step.  Mirror statement for the row stack `(A₀ | A₁)`.  This is the
branching device of the master induction.
-/

namespace NonsoficGroupsExist

theorem stack_left_inverse_or_kernel {k : Type*} [Field k]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (B₀ B₁ : ι → κ → k) :
    (∃ G₀ G₁ : κ → ι → k, ∀ j j' : κ,
      (∑ i, (G₀ j i * B₀ i j' + G₁ j i * B₁ i j')) =
        if j = j' then 1 else 0) ∨
    (∃ v₀ : κ → k, v₀ ≠ 0 ∧ (∀ i, ∑ j, B₀ i j * v₀ j = 0) ∧
      (∀ i, ∑ j, B₁ i j * v₀ j = 0)) := by
  classical
  set M : Matrix (ι ⊕ ι) κ k :=
    Matrix.of (fun p j ↦ Sum.elim (fun i ↦ B₀ i j)
      (fun i ↦ B₁ i j) p) with hM
  by_cases hker : LinearMap.ker M.mulVecLin = ⊥
  · -- injective: a scalar left inverse exists
    left
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      M.mulVecLin hker
    set N : Matrix κ (ι ⊕ ι) k := LinearMap.toMatrix' g with hN
    refine ⟨fun j i ↦ N j (Sum.inl i), fun j i ↦ N j (Sum.inr i),
      fun j j' ↦ ?_⟩
    have hcol : (fun p ↦ M p j') = M.mulVec (Pi.single j' 1) := by
      funext p
      simp [Matrix.mulVec_single]
    calc (∑ i, (N j (Sum.inl i) * B₀ i j' +
          N j (Sum.inr i) * B₁ i j'))
        = ∑ p : ι ⊕ ι, N j p * M p j' := by
          rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
          rfl
      _ = (N.mulVec (fun p ↦ M p j')) j := by
          simp [Matrix.mulVec, dotProduct]
      _ = (N.mulVec (M.mulVec (Pi.single j' 1))) j := by rw [hcol]
      _ = (g.comp M.mulVecLin) (Pi.single j' 1) j := by
          rw [hN]
          have h1 : ∀ x : ι ⊕ ι → k,
              (LinearMap.toMatrix' g).mulVec x = g x := by
            intro x
            rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
          rw [h1]
          have h2 : M.mulVec (Pi.single j' 1) =
              M.mulVecLin (Pi.single j' 1) := rfl
          rw [h2]
          rfl
      _ = if j = j' then 1 else 0 := by
          rw [hg]
          simp [Pi.single_apply]
  · -- a kernel vector exists
    right
    obtain ⟨v₀, hv₀mem, hv₀⟩ := Submodule.ne_bot_iff _ |>.mp hker
    refine ⟨v₀, hv₀, ?_, ?_⟩
    · intro i
      have h := congrFun (LinearMap.mem_ker.mp hv₀mem) (Sum.inl i)
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hM]
        using h
    · intro i
      have h := congrFun (LinearMap.mem_ker.mp hv₀mem) (Sum.inr i)
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hM]
        using h

theorem stack_right_inverse_or_kernel {k : Type*} [Field k]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A₀ A₁ : ι → κ → k) :
    (∃ H₀ H₁ : κ → ι → k, ∀ i i' : ι,
      (∑ j, (A₀ i j * H₀ j i' + A₁ i j * H₁ j i')) =
        if i = i' then 1 else 0) ∨
    (∃ u₀ : ι → k, u₀ ≠ 0 ∧ (∀ j, ∑ i, A₀ i j * u₀ i = 0) ∧
      (∀ j, ∑ i, A₁ i j * u₀ i = 0)) := by
  classical
  rcases stack_left_inverse_or_kernel
    (fun (j : κ) (i : ι) ↦ A₀ i j) (fun (j : κ) (i : ι) ↦ A₁ i j)
    with ⟨G₀, G₁, hG⟩ | ⟨v₀, hv₀, hk₀, hk₁⟩
  · left
    refine ⟨fun j i' ↦ G₀ i' j, fun j i' ↦ G₁ i' j, fun i i' ↦ ?_⟩
    have h := hG i' i
    calc (∑ j, (A₀ i j * G₀ i' j + A₁ i j * G₁ i' j))
        = ∑ j, (G₀ i' j * A₀ i j + G₁ i' j * A₁ i j) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [mul_comm (A₀ i j), mul_comm (A₁ i j)]
      _ = if i' = i then 1 else 0 := h
      _ = if i = i' then 1 else 0 := by
          by_cases hii : i = i'
          · rw [if_pos hii, if_pos hii.symm]
          · rw [if_neg hii, if_neg (Ne.symm hii)]
  · right
    refine ⟨v₀, hv₀, fun j ↦ ?_, fun j ↦ ?_⟩
    · have h := hk₀ j
      calc (∑ i, A₀ i j * v₀ i)
          = ∑ i, (fun (j : κ) (i : ι) ↦ A₀ i j) j i * v₀ i := rfl
        _ = 0 := h
    · have h := hk₁ j
      calc (∑ i, A₁ i j * v₀ i)
          = ∑ i, (fun (j : κ) (i : ι) ↦ A₁ i j) j i * v₀ i := rfl
        _ = 0 := h

end NonsoficGroupsExist
