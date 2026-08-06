import NonsoficGroupsExist.PrefixCode

/-!
# Transport along a pair of complete prefix codes

Matrix data indexed by *two different* complete prefix codes — of
possibly different sizes — multiplies like matrices: in the product

`(Σᵢⱼ s_{rᵢ}·Eᵢⱼ·t_{cⱼ}) · (Σⱼₗ s_{cⱼ}·Fⱼₗ·t_{wₗ})`

the middle words collapse by the code orthogonality `t_c s_{c'} = δ`,
leaving `Σᵢₗ s_{rᵢ}·(Σⱼ EᵢⱼFⱼₗ)·t_{wₗ}`.  Consequently a rectangular
`L`-matrix with a two-sided inverse transports to a unit of `L` along
any pair of complete codes matching its two index sets — the Leavitt
`L^p ≅ L^q` phenomenon that lets the elimination recurse on honest
ring elements with no squaring-up.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

/-- **Code-pair product collapse**: only the middle code's
orthogonality is used; the outer word assignments are arbitrary. -/
theorem codePair_mul [DecidableEq κ] (C : BinaryPrefixCode κ)
    (R : ι → List (Fin 2)) (W : μ → List (Fin 2))
    (E : ι → κ → A) (F : κ → μ → A) :
    (∑ i, ∑ j, L.wordS (R i) * E i j * L.wordT (C.word j)) *
      (∑ j, ∑ l, L.wordS (C.word j) * F j l * L.wordT (W l)) =
    ∑ i, ∑ l, L.wordS (R i) * (∑ j, E i j * F j l) * L.wordT (W l) := by
  classical
  have hterm : ∀ (i : ι) (j j' : κ) (l : μ),
      L.wordS (R i) * E i j * L.wordT (C.word j) *
        (L.wordS (C.word j') * F j' l * L.wordT (W l)) =
      if j = j' then L.wordS (R i) * (E i j * F j' l) * L.wordT (W l)
        else 0 := by
    intro i j j' l
    by_cases hjj : j = j'
    · subst hjj
      rw [if_pos rfl,
        show L.wordS (R i) * E i j * L.wordT (C.word j) *
            (L.wordS (C.word j) * F j l * L.wordT (W l)) =
          L.wordS (R i) * E i j *
            (L.wordT (C.word j) * L.wordS (C.word j)) *
            (F j l * L.wordT (W l)) from by noncomm_ring,
        L.wordT_mul_wordS_self, mul_one]
      noncomm_ring
    · rw [if_neg hjj,
        show L.wordS (R i) * E i j * L.wordT (C.word j) *
            (L.wordS (C.word j') * F j' l * L.wordT (W l)) =
          L.wordS (R i) * E i j *
            (L.wordT (C.word j) * L.wordS (C.word j')) *
            (F j' l * L.wordT (W l)) from by noncomm_ring,
        L.wordT_mul_wordS_of_incomparable _ _ (C.prefix_free hjj)
          (C.prefix_free (Ne.symm hjj)), mul_zero, zero_mul]
  calc (∑ i, ∑ j, L.wordS (R i) * E i j * L.wordT (C.word j)) *
        (∑ j, ∑ l, L.wordS (C.word j) * F j l * L.wordT (W l))
      = ∑ i, ∑ j, ∑ j', ∑ l,
          L.wordS (R i) * E i j * L.wordT (C.word j) *
            (L.wordS (C.word j') * F j' l * L.wordT (W l)) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ j', ∑ l,
          (if j = j' then
            L.wordS (R i) * (E i j * F j' l) * L.wordT (W l) else 0) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl
          fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦
          Finset.sum_congr rfl fun l _ ↦ hterm i j j' l
    _ = ∑ i, ∑ j, ∑ l,
          L.wordS (R i) * (E i j * F j l) * L.wordT (W l) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
    _ = ∑ i, ∑ l, L.wordS (R i) * (∑ j, E i j * F j l) *
          L.wordT (W l) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]

/-- **Rectangular inverse pairs transport to `1`** along complete
codes on both sides. -/
theorem codePair_mul_eq_one [DecidableEq ι] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (C : BinaryPrefixCode κ)
    (E : ι → κ → A) (F : κ → ι → A)
    (hEF : ∀ i i', ∑ j, E i j * F j i' =
      if i = i' then (1 : A) else 0) :
    (∑ i, ∑ j, L.wordS (R.word i) * E i j * L.wordT (C.word j)) *
      (∑ j, ∑ i, L.wordS (C.word j) * F j i * L.wordT (R.word i)) =
      1 := by
  classical
  rw [L.codePair_mul C R.word R.word E F]
  calc ∑ i, ∑ i', L.wordS (R.word i) * (∑ j, E i j * F j i') *
        L.wordT (R.word i')
      = ∑ i, ∑ i', (if i = i' then
          L.wordS (R.word i) * L.wordT (R.word i') else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun i' _ ↦ ?_
        rw [hEF i i']
        simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    _ = ∑ i, L.wordS (R.word i) * L.wordT (R.word i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
    _ = 1 := hR

/-- The transported unit of a rectangular two-sided-invertible
`L`-matrix along a pair of complete codes. -/
noncomputable def codePairUnit [DecidableEq ι] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (C : BinaryPrefixCode κ) (hC : L.IsComplete C)
    (E : ι → κ → A) (F : κ → ι → A)
    (hEF : ∀ i i', ∑ j, E i j * F j i' =
      if i = i' then (1 : A) else 0)
    (hFE : ∀ j j', ∑ i, F j i * E i j' =
      if j = j' then (1 : A) else 0) : Aˣ where
  val := ∑ i, ∑ j, L.wordS (R.word i) * E i j * L.wordT (C.word j)
  inv := ∑ j, ∑ i, L.wordS (C.word j) * F j i * L.wordT (R.word i)
  val_inv := L.codePair_mul_eq_one R hR C E F hEF
  inv_val := L.codePair_mul_eq_one C hC R F E hFE

@[simp] theorem codePairUnit_val [DecidableEq ι] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (C : BinaryPrefixCode κ) (hC : L.IsComplete C)
    (E : ι → κ → A) (F : κ → ι → A) (hEF) (hFE) :
    ((L.codePairUnit R hR C hC E F hEF hFE : Aˣ) : A) =
      ∑ i, ∑ j, L.wordS (R.word i) * E i j * L.wordT (C.word j) := rfl

end LeavittFamily
end NonsoficGroupsExist
