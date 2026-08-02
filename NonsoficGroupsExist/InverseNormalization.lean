import NonsoficGroupsExist.SoficErrors
import NonsoficGroupsExist.PermutationConservation

/-!
# Approximate inverse normalization

The manuscript normalizes a sofic approximation so that inverse generators are
represented by exact inverse permutations.  The matching argument only needs
the resulting variation estimate.  This file proves it directly: approximate
multiplicativity and the identity estimate imply that `σ(g⁻¹)` differs from
`σ(g)⁻¹` on a negligible set.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

namespace SoficApproximation

variable {G : Type*} [Group G] (S : SoficApproximation G)

/-- Vertices where the assigned inverse is not the inverse of the assigned
permutation. -/
noncomputable def inverseError (n : ℕ) (g : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ S.map n g⁻¹ x ≠ (S.map n g)⁻¹ x

theorem inverseError_subset (n : ℕ) (g : G) :
    S.inverseError n g ⊆
      S.multiplicationError n g g⁻¹ ∪ S.identityError n := by
  classical
  intro x hx
  simp only [inverseError, multiplicationError, identityError, movedVertices,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_cases hmul : S.map n (g * g⁻¹) x ≠ S.map n g (S.map n g⁻¹ x)
  · exact Or.inl hmul
  by_cases hone : S.map n 1 x ≠ x
  · exact Or.inr hone
  exfalso
  apply hx
  apply (S.map n g).injective
  calc
    S.map n g (S.map n g⁻¹ x) = S.map n (g * g⁻¹) x := (not_ne_iff.mp hmul).symm
    _ = S.map n 1 x := by simp
    _ = x := not_ne_iff.mp hone
    _ = S.map n g ((S.map n g)⁻¹ x) := by simp

theorem inverseError_card_le (n : ℕ) (g : G) :
    (S.inverseError n g).card ≤
      (S.multiplicationError n g g⁻¹).card + (S.identityError n).card := by
  exact (Finset.card_le_card (S.inverseError_subset n g)).trans
    (Finset.card_union_le _ _)

theorem inverseError_negligible (g : G) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.inverseError n g).card : ℝ) := by
  have hsum := Negligible.add
    (S.multiplicationError_negligible g g⁻¹) S.identityError_negligible
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  apply div_le_div_of_nonneg_right
  · have hcast : ((S.inverseError n g).card : ℝ) ≤
        ((S.multiplicationError n g g⁻¹).card : ℝ) +
          ((S.identityError n).card : ℝ) := by
      exact_mod_cast S.inverseError_card_le n g
    exact hcast
  · positivity

end SoficApproximation

section PermutationVariation

variable {Y : FiniteModel}

/-- Total variation is unchanged when a permutation is replaced by its
inverse. -/
theorem inverse_variation_eq (p : Equiv.Perm Y) (f : Y → ℝ) :
    (∑ x : Y, |f (p⁻¹ x) - f x|) = ∑ x : Y, |f (p x) - f x| := by
  calc
    (∑ x : Y, |f (p⁻¹ x) - f x|) =
        ∑ x : Y, |f (p⁻¹ (p x)) - f (p x)| := by
          symm
          exact Fintype.sum_equiv p _ _ (fun _ ↦ rfl)
    _ = ∑ x : Y, |f (p x) - f x| := by
      apply Finset.sum_congr rfl
      intro x _
      simp [abs_sub_comm]

/-- Replacing a permutation on `E` changes the variation by at most `|E|`
when the observable lies in `[0,1]`. -/
theorem variation_le_of_disagreement (p q : Equiv.Perm Y) (f : Y → ℝ)
    (hnonneg : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1)
    (E : Finset Y) (hE : ∀ x, p x ≠ q x → x ∈ E) :
    (∑ x : Y, |f (p x) - f x|) ≤
      (∑ x : Y, |f (q x) - f x|) + E.card := by
  calc
    (∑ x : Y, |f (p x) - f x|) ≤
        ∑ x : Y, (|f (q x) - f x| + if x ∈ E then 1 else 0) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hpq : p x = q x
      · simp only [hpq, sub_self, abs_zero, zero_le_add_iff_nonneg_left]
        split_ifs <;> positivity
      · have hdiff : |f (p x) - f x| ≤ 1 := by
          rw [abs_sub_le_iff]
          constructor <;> linarith [hnonneg (p x), hnonneg x, hone (p x), hone x]
        simp only [if_pos (hE x hpq)]
        linarith [abs_nonneg (f (q x) - f x)]
    _ = (∑ x : Y, |f (q x) - f x|) + E.card := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [Finset.sum_boole]
      norm_cast

end PermutationVariation

end NonsoficGroupsExist
