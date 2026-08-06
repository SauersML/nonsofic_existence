import NonsoficGroupsExist.Sofic.Asymptotics
import NonsoficGroupsExist.Sofic.Sofic

/-!
# Global error arrays of a sofic approximation

The diagonal component selection counts all failures on each tested block.
This file turns the two global failures supplied by the definition of a sofic
approximation into the `Negligible` form used by `Selection`.
-/

namespace NonsoficGroupsExist
namespace SoficApproximation

variable {G : Type*} [Group G] (S : SoficApproximation G)

/-- Vertices where the assigned product law fails. -/
noncomputable def multiplicationError (n : ℕ) (g h : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ S.map n (g * h) x ≠ S.map n g (S.map n h x)

/-- Fixed vertices of a nonidentity group element. -/
noncomputable def fixedError (n : ℕ) (g : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ S.map n g x = x

/-- Moved vertices, complementary to `fixedError`. -/
noncomputable def movedVertices (n : ℕ) (g : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ S.map n g x ≠ x

/-- Vertices where the permutation assigned to the identity is not the actual
identity permutation. -/
noncomputable def identityError (n : ℕ) : Finset (S.model n) :=
  S.movedVertices n 1

/-- Vertices where two assigned group elements collide. -/
noncomputable def collisionError (n : ℕ) (g h : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ S.map n g x = S.map n h x

/-- Failures of the approximate conjugacy identity used on compressor arcs. -/
noncomputable def conjugacyError (n : ℕ) (q g : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦
    S.map n q (S.map n g x) ≠ S.map n (q * g * q⁻¹) (S.map n q x)

/-- Vertices where the assigned permutations of two commuting group elements
fail to commute. -/
noncomputable def commutationError (n : ℕ) (g h : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦
    S.map n g (S.map n h x) ≠ S.map n h (S.map n g x)

private theorem hammingDistance_mul (n : ℕ) (g h : G) :
    hammingDistance (S.model n) (S.map n (g * h)) (S.map n g * S.map n h) =
      ((S.multiplicationError n g h).card : ℝ) / Fintype.card (S.model n) := by
  unfold hammingDistance
  unfold hammingDisagreement
  congr 2

private theorem hammingDistance_one (n : ℕ) (g : G) :
    hammingDistance (S.model n) (S.map n g) 1 =
      ((S.movedVertices n g).card : ℝ) / Fintype.card (S.model n) := by
  unfold hammingDistance
  unfold hammingDisagreement
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

private theorem commutationError_subset (n : ℕ) (g h : G)
    (hcomm : Commute g h) :
    S.commutationError n g h ⊆
      S.multiplicationError n g h ∪ S.multiplicationError n h g := by
  classical
  intro x hx
  simp only [commutationError, multiplicationError, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_cases hgh : S.map n (g * h) x ≠ S.map n g (S.map n h x)
  · exact Or.inl hgh
  by_cases hhg : S.map n (h * g) x ≠ S.map n h (S.map n g x)
  · exact Or.inr hhg
  exfalso
  apply hx
  rw [← not_ne_iff.mp hgh, ← not_ne_iff.mp hhg, hcomm.eq]

/-- Approximate multiplicativity makes the assigned permutations of any fixed
commuting pair commute away from a negligible set of vertices. -/
theorem commutationError_negligible (g h : G) (hcomm : Commute g h) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.commutationError n g h).card : ℝ) := by
  have hsum := Negligible.add
    (S.multiplicationError_negligible g h)
    (S.multiplicationError_negligible h g)
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  have hs := Finset.card_le_card (S.commutationError_subset n g h hcomm)
  have hu := Finset.card_union_le
    (S.multiplicationError n g h) (S.multiplicationError n h g)
  have hcast : ((S.commutationError n g h).card : ℝ) ≤
      ((S.multiplicationError n g h).card : ℝ) +
        (S.multiplicationError n h g).card := by
    exact_mod_cast hs.trans hu
  apply div_le_div_of_nonneg_right hcast
  positivity

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

theorem identityError_negligible :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.identityError n).card : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := S.map_one_close ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  change |((S.identityError n).card : ℝ) / Fintype.card (S.model n)| < ε
  rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  simpa only [identityError, ← S.hammingDistance_one] using hN n hn

private theorem collision_subset (n : ℕ) (g h : G) :
    S.collisionError n g h ⊆
      S.multiplicationError n (h⁻¹) g ∪
        S.multiplicationError n (h⁻¹) h ∪ S.identityError n ∪
          S.fixedError n (h⁻¹ * g) := by
  classical
  intro x hx
  simp only [collisionError, multiplicationError, identityError, movedVertices,
    fixedError, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_cases hg : S.map n (h⁻¹ * g) x ≠ S.map n h⁻¹ (S.map n g x)
  · exact Or.inl (Or.inl (Or.inl hg))
  by_cases hh : S.map n (h⁻¹ * h) x ≠ S.map n h⁻¹ (S.map n h x)
  · exact Or.inl (Or.inl (Or.inr hh))
  by_cases h1 : S.map n 1 x ≠ x
  · exact Or.inl (Or.inr h1)
  right
  calc
    S.map n (h⁻¹ * g) x = S.map n h⁻¹ (S.map n g x) := not_ne_iff.mp hg
    _ = S.map n h⁻¹ (S.map n h x) := congrArg (S.map n h⁻¹) hx
    _ = S.map n (h⁻¹ * h) x := (not_ne_iff.mp hh).symm
    _ = S.map n 1 x := by simp
    _ = x := not_ne_iff.mp h1

private theorem collision_card_le (n : ℕ) (g h : G) :
    (S.collisionError n g h).card ≤
      (S.multiplicationError n (h⁻¹) g).card +
        (S.multiplicationError n (h⁻¹) h).card + (S.identityError n).card +
          (S.fixedError n (h⁻¹ * g)).card := by
  classical
  have hs := Finset.card_le_card (S.collision_subset n g h)
  have h1 := Finset.card_union_le (S.multiplicationError n (h⁻¹) g)
    (S.multiplicationError n (h⁻¹) h)
  have h2 := Finset.card_union_le
    (S.multiplicationError n (h⁻¹) g ∪ S.multiplicationError n (h⁻¹) h)
    (S.identityError n)
  have h3 := Finset.card_union_le
    (S.multiplicationError n (h⁻¹) g ∪ S.multiplicationError n (h⁻¹) h ∪
      S.identityError n) (S.fixedError n (h⁻¹ * g))
  omega

theorem collisionError_negligible (g h : G) (hgh : g ≠ h) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.collisionError n g h).card : ℝ) := by
  have hne : h⁻¹ * g ≠ 1 := by
    intro heq
    apply hgh
    exact (inv_mul_eq_one.mp heq).symm
  have hsum := Negligible.add
    (Negligible.add
      (S.multiplicationError_negligible (h⁻¹) g)
      (S.multiplicationError_negligible (h⁻¹) h))
    (Negligible.add S.identityError_negligible
      (S.fixedError_negligible (h⁻¹ * g) hne))
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  calc
    ((S.collisionError n g h).card : ℝ) / Fintype.card (S.model n) ≤
        (((S.multiplicationError n (h⁻¹) g).card +
          (S.multiplicationError n (h⁻¹) h).card + (S.identityError n).card +
          (S.fixedError n (h⁻¹ * g)).card : ℕ) : ℝ) /
            Fintype.card (S.model n) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast S.collision_card_le n g h
    _ =
        (((S.multiplicationError n (h⁻¹) g).card : ℝ) +
          (S.multiplicationError n (h⁻¹) h).card +
          (((S.identityError n).card : ℝ) + (S.fixedError n (h⁻¹ * g)).card)) /
            Fintype.card (S.model n) := by
      push_cast
      ring

/-- Hamming separation is the complement of the collision density. -/
theorem hammingDistance_eq_one_sub_collision (n : ℕ) (g h : G)
    (hcard : 0 < Fintype.card (S.model n)) :
    hammingDistance (S.model n) (S.map n g) (S.map n h) =
      1 - ((S.collisionError n g h).card : ℝ) /
        Fintype.card (S.model n) := by
  classical
  unfold hammingDistance collisionError
  unfold hammingDisagreement
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (S.model n)))
    (fun x : S.model n ↦ S.map n g x = S.map n h x)
  have hcast :
      ((Finset.univ.filter fun x : S.model n ↦ S.map n g x = S.map n h x).card : ℝ) +
        ((Finset.univ.filter fun x : S.model n ↦ S.map n g x ≠ S.map n h x).card : ℝ) =
          Fintype.card (S.model n) := by
    exact_mod_cast hpartition
  have hcardR : (0 : ℝ) < Fintype.card (S.model n) := by exact_mod_cast hcard
  field_simp
  linarith

/-- Assigned permutations of any two distinct fixed group elements are
eventually separated by more than nine tenths in normalized Hamming distance. -/
theorem map_pair_separated_eventually {g h : G} (hgh : g ≠ h) :
    ∃ N : ℕ, ∀ n ≥ N,
      9 / 10 < hammingDistance (S.model n) (S.map n g) (S.map n h) := by
  have hcollision := S.collisionError_negligible g h hgh
  obtain ⟨Ne, hNe⟩ := hcollision (1 / 10) (by norm_num)
  obtain ⟨Nc, hNc⟩ := S.card_tendsToInfinity 1
  refine ⟨max Ne Nc, fun n hn ↦ ?_⟩
  have hne := hNe n ((le_max_left _ _).trans hn)
  have hcard := hNc n ((le_max_right _ _).trans hn)
  have hratio : ((S.collisionError n g h).card : ℝ) /
      Fintype.card (S.model n) < 1 / 10 :=
    lt_of_le_of_lt (le_abs_self _) hne
  rw [S.hammingDistance_eq_one_sub_collision n g h
    (lt_of_lt_of_le Nat.zero_lt_one hcard)]
  linarith

private theorem conjugacyError_subset (n : ℕ) (q g : G) :
    S.conjugacyError n q g ⊆
      S.multiplicationError n q g ∪
        S.multiplicationError n (q * g * q⁻¹) q := by
  classical
  intro x hx
  simp only [conjugacyError, multiplicationError, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_cases hleft : S.map n (q * g) x ≠ S.map n q (S.map n g x)
  · exact Or.inl hleft
  by_cases hright : S.map n ((q * g * q⁻¹) * q) x ≠
      S.map n (q * g * q⁻¹) (S.map n q x)
  · exact Or.inr hright
  exfalso
  apply hx
  rw [← not_ne_iff.mp hleft, ← not_ne_iff.mp hright]
  congr 2
  group

theorem conjugacyError_negligible (q g : G) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.conjugacyError n q g).card : ℝ) := by
  have hsum := Negligible.add (S.multiplicationError_negligible q g)
    (S.multiplicationError_negligible (q * g * q⁻¹) q)
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  have hs := Finset.card_le_card (S.conjugacyError_subset n q g)
  have hu := Finset.card_union_le (S.multiplicationError n q g)
    (S.multiplicationError n (q * g * q⁻¹) q)
  have hcast : ((S.conjugacyError n q g).card : ℝ) ≤
      ((S.multiplicationError n q g).card : ℝ) +
        (S.multiplicationError n (q * g * q⁻¹) q).card := by
    exact_mod_cast hs.trans hu
  apply div_le_div_of_nonneg_right hcast
  positivity

end SoficApproximation
end NonsoficGroupsExist
