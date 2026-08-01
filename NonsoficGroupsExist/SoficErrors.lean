import NonsoficGroupsExist.Asymptotics
import NonsoficGroupsExist.Sofic

/-!
# Global error arrays of a sofic approximation

The diagonal component selection counts all failures on each candidate block.
This file turns the two global failures supplied by the definition of a sofic
approximation into the `Negligible` form used by `Selection`.
-/

namespace NonsoficGroupsExist
namespace SoficApproximation

variable {G : Type} [Group G] (S : SoficApproximation G)

/-- Vertices where the assigned product law fails. -/
noncomputable def multiplicationError (n : ℕ) (g h : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ S.map n (g * h) x ≠ S.map n g (S.map n h x)

/-- Fixed vertices of a nonidentity group element. -/
noncomputable def fixedError (n : ℕ) (g : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ S.map n g x = x

/-- Moved vertices, complementary to `fixedError`. -/
noncomputable def movedVertices (n : ℕ) (g : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ S.map n g x ≠ x

private theorem hammingDistance_mul (n : ℕ) (g h : G) :
    hammingDistance (S.model n) (S.map n (g * h)) (S.map n g * S.map n h) =
      ((S.multiplicationError n g h).card : ℝ) / Fintype.card (S.model n) := by
  unfold hammingDistance
  congr 2

private theorem hammingDistance_one (n : ℕ) (g : G) :
    hammingDistance (S.model n) (S.map n g) 1 =
      ((S.movedVertices n g).card : ℝ) / Fintype.card (S.model n) := by
  unfold hammingDistance
  congr 2

theorem multiplicationError_negligible (g h : G) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.multiplicationError n g h).card : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative g h ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  change |((S.multiplicationError n g h).card : ℝ) /
    Fintype.card (S.model n)| < ε
  rw [← S.hammingDistance_mul]
  rw [abs_of_nonneg (hammingDistance_nonnegative _ _ _)]
  exact hN n hn

private theorem moved_add_fixed (n : ℕ) (g : G) :
    (S.movedVertices n g).card + (S.fixedError n g).card =
      Fintype.card (S.model n) := by
  simpa [movedVertices, fixedError] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : S.model n ↦ S.map n g x ≠ x))

private theorem fixed_ratio_eq (n : ℕ) (g : G)
    (hcard : 0 < Fintype.card (S.model n)) :
    ((S.fixedError n g).card : ℝ) / Fintype.card (S.model n) =
      1 - hammingDistance (S.model n) (S.map n g) 1 := by
  rw [S.hammingDistance_one]
  have hcast :
      ((S.movedVertices n g).card : ℝ) + ((S.fixedError n g).card : ℝ) =
        Fintype.card (S.model n) := by
    exact_mod_cast S.moved_add_fixed n g
  have hcardR : (0 : ℝ) < Fintype.card (S.model n) := by exact_mod_cast hcard
  field_simp
  linarith

theorem fixedError_negligible (g : G) (hg : g ≠ 1) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.fixedError n g).card : ℝ) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := S.asymptoticallyFaithful g hg ε hε
  obtain ⟨N₂, hN₂⟩ := S.card_tendsToInfinity 1
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  have hcard : 0 < Fintype.card (S.model n) :=
    lt_of_lt_of_le Nat.zero_lt_one (hN₂ n hn₂)
  have hratio :
      ((S.fixedError n g).card : ℝ) / Fintype.card (S.model n) < ε := by
    rw [S.fixed_ratio_eq n g hcard]
    linarith [hN₁ n hn₁]
  change |((S.fixedError n g).card : ℝ) / Fintype.card (S.model n)| < ε
  rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  exact hratio

end SoficApproximation
end NonsoficGroupsExist
