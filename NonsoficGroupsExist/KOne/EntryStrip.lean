import NonsoficGroupsExist.KOne.CodePairTransport

/-!
# Entry strips of code products

Two facts driving the entrywise analysis of a pencil unit's inverse:
stripping a code pencil on both sides recovers the entry, and a
product strips through the insertion of a complete code's partition
of unity — `T(Rᵢ)·(xy)·S(Rᵢ') = Σⱼ (T(Rᵢ)·x·S(Cⱼ))·(T(Cⱼ)·y·S(Rᵢ'))`.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Two-sided strips of a code pencil recover the entries. -/
theorem wordT_pencilVal_wordS [DecidableEq ι] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (C : BinaryPrefixCode κ)
    (E : ι → κ → A) (i₀ : ι) (j₀ : κ) :
    L.wordT (R.word i₀) *
      (∑ i, ∑ j, L.wordS (R.word i) * E i j * L.wordT (C.word j)) *
      L.wordS (C.word j₀) = E i₀ j₀ := by
  classical
  rw [Finset.mul_sum, Finset.sum_mul]
  calc ∑ i, (L.wordT (R.word i₀) *
        ∑ j, L.wordS (R.word i) * E i j * L.wordT (C.word j)) *
        L.wordS (C.word j₀)
      = ∑ i, (if i₀ = i then
          ∑ j, (if j = j₀ then E i j else 0) else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        calc ∑ j, L.wordT (R.word i₀) *
              (L.wordS (R.word i) * E i j * L.wordT (C.word j)) *
              L.wordS (C.word j₀)
            = ∑ j, (if i₀ = i then
                (if j = j₀ then E i j else 0) else 0) := by
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              rw [show L.wordT (R.word i₀) *
                  (L.wordS (R.word i) * E i j * L.wordT (C.word j)) *
                  L.wordS (C.word j₀) =
                (L.wordT (R.word i₀) * L.wordS (R.word i)) * E i j *
                  (L.wordT (C.word j) * L.wordS (C.word j₀)) from by
                  noncomm_ring,
                L.prefixCode_orthogonal R i₀ i,
                L.prefixCode_orthogonal C j j₀]
              by_cases h1 : i₀ = i <;> by_cases h2 : j = j₀
              · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2,
                  one_mul, mul_one]
              · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2,
                  mul_zero]
              · rw [if_neg h1, if_pos h2, if_neg h1, zero_mul,
                  zero_mul]
              · rw [if_neg h1, if_neg h2, if_neg h1, zero_mul,
                  zero_mul]
            _ = (if i₀ = i then
                ∑ j, (if j = j₀ then E i j else 0) else 0) := by
              split_ifs with h1
              · rfl
              · exact Finset.sum_const_zero
    _ = ∑ j, (if j = j₀ then E i₀ j else 0) := by
        rw [Finset.sum_ite_eq Finset.univ i₀, if_pos (Finset.mem_univ i₀)]
    _ = E i₀ j₀ := by
        rw [Finset.sum_ite_eq' Finset.univ j₀, if_pos (Finset.mem_univ j₀)]

/-- A product strips through the insertion of a complete code. -/
theorem strip_insert (C : BinaryPrefixCode κ) (hC : L.IsComplete C)
    (x y : A) (w w' : List (Fin 2)) :
    L.wordT w * (x * y) * L.wordS w' =
      ∑ j, (L.wordT w * x * L.wordS (C.word j)) *
        (L.wordT (C.word j) * y * L.wordS w') := by
  have hxy : x * y = x * (∑ j, L.wordS (C.word j) *
      L.wordT (C.word j)) * y := by
    rw [show (∑ j, L.wordS (C.word j) * L.wordT (C.word j)) = 1 from
      hC, mul_one]
  rw [hxy, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  noncomm_ring

end LeavittFamily
end NonsoficGroupsExist
