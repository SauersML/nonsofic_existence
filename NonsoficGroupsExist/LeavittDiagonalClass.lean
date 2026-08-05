import NonsoficGroupsExist.DiagonalClassGroup
import NonsoficGroupsExist.LeavittWords

/-!
# Corner insertions and the diagonal class of a Leavitt ring

Checkpoint `B4`, Leavitt side.  For a binary word `w` the corner
insertion `κ_w(u) = s_w u t_w + (1 - s_w t_w)` is a unit, conjugate to
`diag(u, 1)` inside `GL₂` by the explicit intertwiner
`X_w = [[s_w, 1 - s_w t_w], [0, t_w]]`.  Consequently
`diag(κ_w(u), 1) · diag(u, 1)⁻¹ = ⁅X_w, diag(u, 1)⁆`, so under strong
division `κ_w(u) ≡ u` modulo the diagonal class group by the abelianity
of `GL₂/EL₂`.  The two length-one insertions multiply to the canonical
corner sum `s₀ u t₀ + s₁ u t₁`, which fixes central units; hence every
central unit lies in the diagonal class group, and `B4` reduces to the
single statement that every unit is a central scalar modulo the
diagonal class (`stableUnits_eq_top` below) — the rose-graph `K₁`
computation.
-/

open scoped commutatorElement

namespace NonsoficGroupsExist
namespace LeavittFamily

set_option linter.unusedSimpArgs false

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

section Word

variable (w : List (Fin 2))

theorem wordT_mul_range (x : A) :
    L.wordT w * (L.wordS w * x) = x := by
  rw [← mul_assoc, wordT_mul_wordS_self, one_mul]

theorem range_mul_wordS (x : A) :
    (x * L.wordT w) * L.wordS w = x := by
  rw [mul_assoc, wordT_mul_wordS_self, mul_one]

theorem wordT_mul_one_sub_range :
    L.wordT w * (1 - L.wordS w * L.wordT w) = 0 := by
  rw [mul_sub, mul_one, wordT_mul_range]
  exact sub_self _

theorem one_sub_range_mul_wordS :
    (1 - L.wordS w * L.wordT w) * L.wordS w = 0 := by
  rw [sub_mul, one_mul, mul_assoc, wordT_mul_wordS_self, mul_one]
  exact sub_self _

theorem one_sub_range_idem :
    (1 - L.wordS w * L.wordT w) * (1 - L.wordS w * L.wordT w) =
      1 - L.wordS w * L.wordT w := by
  have hp : (L.wordS w * L.wordT w) * (L.wordS w * L.wordT w) =
      L.wordS w * L.wordT w := by
    rw [mul_assoc, wordT_mul_range]
  rw [mul_sub, mul_one, sub_mul, one_mul, hp]
  abel

theorem corner_mul_corner (x y : A) :
    (L.wordS w * x * L.wordT w) * (L.wordS w * y * L.wordT w) =
      L.wordS w * (x * y) * L.wordT w := by
  rw [show (L.wordS w * x * L.wordT w) * (L.wordS w * y * L.wordT w) =
    L.wordS w * x * (L.wordT w * L.wordS w) * y * L.wordT w from by
      noncomm_ring, wordT_mul_wordS_self]
  noncomm_ring

theorem corner_mul_one_sub_range (x : A) :
    (L.wordS w * x * L.wordT w) * (1 - L.wordS w * L.wordT w) = 0 := by
  rw [show (L.wordS w * x * L.wordT w) *
    (1 - L.wordS w * L.wordT w) =
    L.wordS w * x * (L.wordT w * (1 - L.wordS w * L.wordT w)) from by
      noncomm_ring, wordT_mul_one_sub_range]
  noncomm_ring

theorem one_sub_range_mul_corner (x : A) :
    (1 - L.wordS w * L.wordT w) * (L.wordS w * x * L.wordT w) = 0 := by
  rw [show (1 - L.wordS w * L.wordT w) *
    (L.wordS w * x * L.wordT w) =
    ((1 - L.wordS w * L.wordT w) * L.wordS w) * x * L.wordT w from by
      noncomm_ring, one_sub_range_mul_wordS]
  noncomm_ring

/-- The corner insertion of a unit is a unit. -/
def kappaUnit (u : Aˣ) : Aˣ where
  val := L.wordS w * (u : A) * L.wordT w + (1 - L.wordS w * L.wordT w)
  inv := L.wordS w * ((u⁻¹ : Aˣ) : A) * L.wordT w +
    (1 - L.wordS w * L.wordT w)
  val_inv := by
    rw [add_mul, mul_add, mul_add, corner_mul_corner,
      corner_mul_one_sub_range, one_sub_range_mul_corner,
      one_sub_range_idem]
    rw [show ((u : A) * ((u⁻¹ : Aˣ) : A)) = 1 from u.mul_inv, mul_one]
    rw [add_zero, zero_add]
    abel
  inv_val := by
    rw [add_mul, mul_add, mul_add, corner_mul_corner,
      corner_mul_one_sub_range, one_sub_range_mul_corner,
      one_sub_range_idem]
    rw [show (((u⁻¹ : Aˣ) : A) * (u : A)) = 1 from u.inv_mul, mul_one]
    rw [add_zero, zero_add]
    abel

@[simp] theorem kappaUnit_val (u : Aˣ) :
    (L.kappaUnit w u : A) =
      L.wordS w * (u : A) * L.wordT w +
        (1 - L.wordS w * L.wordT w) := rfl

/-- The explicit intertwiner `X_w` with its inverse. -/
def cornerIntertwiner : (Matrix (Fin 2) (Fin 2) A)ˣ where
  val := !![L.wordS w, 1 - L.wordS w * L.wordT w; 0, L.wordT w]
  inv := !![L.wordT w, 0; 1 - L.wordS w * L.wordT w, L.wordS w]
  val_inv := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [one_sub_range_idem, one_sub_range_mul_wordS,
        wordT_mul_one_sub_range, wordT_mul_wordS_self]
  inv_val := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [one_sub_range_idem, one_sub_range_mul_wordS,
        wordT_mul_one_sub_range, wordT_mul_wordS_self]

/-- The intertwining identity
`X_w · diag(u, 1) · X_w⁻¹ = diag(κ_w(u), 1)`. -/
theorem cornerIntertwiner_conj_diagUnit (u : Aˣ) :
    L.cornerIntertwiner w * diagUnit u * (L.cornerIntertwiner w)⁻¹ =
      diagUnit (L.kappaUnit w u) := by
  apply Units.ext
  show !![L.wordS w, 1 - L.wordS w * L.wordT w; 0, L.wordT w] *
    !![(u : A), 0; 0, 1] *
    !![L.wordT w, 0; 1 - L.wordS w * L.wordT w, L.wordS w] = _
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagUnit, kappaUnit_val, one_sub_range_idem,
      one_sub_range_mul_wordS, wordT_mul_one_sub_range,
      wordT_mul_wordS_self]

/-- **The `κ_w`-coset identity**: under strong division the corner
insertion does not move the diagonal class. -/
theorem kappaUnit_mul_inv_mem_stableUnits [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) (u : Aˣ) :
    L.kappaUnit w u * u⁻¹ ∈ stableUnits A := by
  rw [mem_stableUnits_iff]
  have hcomm := commutator_mem_elementaryGroup_of_division hdiv
    (L.cornerIntertwiner w) (diagUnit u)
  have hval : ⁅L.cornerIntertwiner w, diagUnit u⁆ =
      diagUnit (L.kappaUnit w u * u⁻¹) := by
    have hinv : (diagUnit u)⁻¹ = diagUnit u⁻¹ :=
      (map_inv diagUnitHom u).symm
    rw [commutatorElement_def, cornerIntertwiner_conj_diagUnit, hinv,
      ← diagUnit_mul]
  rwa [hval] at hcomm

end Word

section Scalar

theorem cross_mul_cross (x y : A) :
    (L.s 0 * x * L.t 0 + L.s 1 * x * L.t 1) *
      (L.s 0 * y * L.t 0 + L.s 1 * y * L.t 1) =
      L.s 0 * (x * y) * L.t 0 + L.s 1 * (x * y) * L.t 1 := by
  have h00 : (L.s 0 * x * L.t 0) * (L.s 0 * y * L.t 0) =
      L.s 0 * (x * y) * L.t 0 := by
    rw [show (L.s 0 * x * L.t 0) * (L.s 0 * y * L.t 0) =
      L.s 0 * x * (L.t 0 * L.s 0) * y * L.t 0 from by noncomm_ring]
    rw [t_mul_s, if_pos rfl]
    noncomm_ring
  have h01 : (L.s 0 * x * L.t 0) * (L.s 1 * y * L.t 1) = 0 := by
    rw [show (L.s 0 * x * L.t 0) * (L.s 1 * y * L.t 1) =
      L.s 0 * x * (L.t 0 * L.s 1) * y * L.t 1 from by noncomm_ring]
    rw [t_mul_s, if_neg (by decide)]
    noncomm_ring
  have h10 : (L.s 1 * x * L.t 1) * (L.s 0 * y * L.t 0) = 0 := by
    rw [show (L.s 1 * x * L.t 1) * (L.s 0 * y * L.t 0) =
      L.s 1 * x * (L.t 1 * L.s 0) * y * L.t 0 from by noncomm_ring]
    rw [t_mul_s, if_neg (by decide)]
    noncomm_ring
  have h11 : (L.s 1 * x * L.t 1) * (L.s 1 * y * L.t 1) =
      L.s 1 * (x * y) * L.t 1 := by
    rw [show (L.s 1 * x * L.t 1) * (L.s 1 * y * L.t 1) =
      L.s 1 * x * (L.t 1 * L.s 1) * y * L.t 1 from by noncomm_ring]
    rw [t_mul_s, if_pos rfl]
    noncomm_ring
  rw [add_mul, mul_add, mul_add, h00, h01, h10, h11]
  abel

/-- The canonical corner sum of a unit. -/
def crossUnit (u : Aˣ) : Aˣ where
  val := L.s 0 * (u : A) * L.t 0 + L.s 1 * (u : A) * L.t 1
  inv := L.s 0 * ((u⁻¹ : Aˣ) : A) * L.t 0 +
    L.s 1 * ((u⁻¹ : Aˣ) : A) * L.t 1
  val_inv := by
    rw [cross_mul_cross, show ((u : A) * ((u⁻¹ : Aˣ) : A)) = 1 from
      u.mul_inv]
    rw [mul_one, mul_one]
    exact L.sum_s_mul_t
  inv_val := by
    rw [cross_mul_cross, show (((u⁻¹ : Aˣ) : A) * (u : A)) = 1 from
      u.inv_mul]
    rw [mul_one, mul_one]
    exact L.sum_s_mul_t

/-- The two length-one corner insertions multiply to the corner sum. -/
theorem kappa_zero_mul_kappa_one (u : Aˣ) :
    L.kappaUnit [0] u * L.kappaUnit [1] u = L.crossUnit u := by
  apply Units.ext
  show (L.kappaUnit [0] u : A) * (L.kappaUnit [1] u : A) = _
  rw [kappaUnit_val, kappaUnit_val]
  have hS0 : L.wordS [0] = L.s 0 := by simp [wordS]
  have hS1 : L.wordS [1] = L.s 1 := by simp [wordS]
  have hT0 : L.wordT [0] = L.t 0 := by simp [wordT]
  have hT1 : L.wordT [1] = L.t 1 := by simp [wordT]
  rw [hS0, hS1, hT0, hT1]
  have h00 : (L.s 0 * (u : A) * L.t 0) * (L.s 1 * (u : A) * L.t 1) =
      0 := by
    rw [show (L.s 0 * (u : A) * L.t 0) * (L.s 1 * (u : A) * L.t 1) =
      L.s 0 * (u : A) * (L.t 0 * L.s 1) * (u : A) * L.t 1 from by
        noncomm_ring]
    rw [t_mul_s, if_neg (by decide)]
    noncomm_ring
  have h0p : (L.s 0 * (u : A) * L.t 0) * (1 - L.s 1 * L.t 1) =
      L.s 0 * (u : A) * L.t 0 := by
    rw [mul_sub, mul_one, show (L.s 0 * (u : A) * L.t 0) *
      (L.s 1 * L.t 1) =
      L.s 0 * (u : A) * (L.t 0 * L.s 1) * L.t 1 from by noncomm_ring,
      t_mul_s, if_neg (by decide)]
    noncomm_ring
  have hp1 : (1 - L.s 0 * L.t 0) * (L.s 1 * (u : A) * L.t 1) =
      L.s 1 * (u : A) * L.t 1 := by
    rw [sub_mul, one_mul, show (L.s 0 * L.t 0) *
      (L.s 1 * (u : A) * L.t 1) =
      L.s 0 * (L.t 0 * L.s 1) * (u : A) * L.t 1 from by noncomm_ring,
      t_mul_s, if_neg (by decide)]
    noncomm_ring
  have hpp : (1 - L.s 0 * L.t 0) * (1 - L.s 1 * L.t 1) = 0 := by
    have hcross0 : (L.s 0 * L.t 0) * (L.s 1 * L.t 1) = 0 := by
      rw [show (L.s 0 * L.t 0) * (L.s 1 * L.t 1) =
        L.s 0 * (L.t 0 * L.s 1) * L.t 1 from by noncomm_ring,
        t_mul_s, if_neg (by decide)]
      noncomm_ring
    have hsum := L.sum_s_mul_t
    calc (1 - L.s 0 * L.t 0) * (1 - L.s 1 * L.t 1) =
        1 - L.s 1 * L.t 1 - L.s 0 * L.t 0 +
          (L.s 0 * L.t 0) * (L.s 1 * L.t 1) := by noncomm_ring
      _ = 1 - (L.s 0 * L.t 0 + L.s 1 * L.t 1) := by
          rw [hcross0]
          abel
      _ = 0 := by
          rw [hsum]
          exact sub_self 1
  rw [add_mul, mul_add, mul_add, h00, h0p, hp1, hpp]
  show 0 + L.s 0 * (u : A) * L.t 0 +
      (L.s 1 * (u : A) * L.t 1 + 0) =
    L.s 0 * (u : A) * L.t 0 + L.s 1 * (u : A) * L.t 1
  abel

include L in
/-- **Central units lie in the diagonal class group**: they are fixed by
the corner sum, which is the product of the two corner insertions, each
congruent to the unit itself. -/
theorem central_mem_stableUnits [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) (c : Aˣ)
    (hc : ∀ x : A, (c : A) * x = x * (c : A)) :
    c ∈ stableUnits A := by
  have hcross : L.crossUnit c = c := by
    apply Units.ext
    show L.s 0 * (c : A) * L.t 0 + L.s 1 * (c : A) * L.t 1 = (c : A)
    rw [show L.s 0 * (c : A) = (c : A) * L.s 0 from (hc (L.s 0)).symm,
      show L.s 1 * (c : A) = (c : A) * L.s 1 from (hc (L.s 1)).symm]
    rw [mul_assoc, mul_assoc, ← mul_add, L.sum_s_mul_t, mul_one]
  have hprod : L.kappaUnit [0] c * L.kappaUnit [1] c = c := by
    rw [kappa_zero_mul_kappa_one, hcross]
  have h0 := L.kappaUnit_mul_inv_mem_stableUnits [0] hdiv c
  have h1 := L.kappaUnit_mul_inv_mem_stableUnits [1] hdiv c
  -- In the quotient by the diagonal class, `c = c * c`.
  have hmk : ∀ u : Aˣ, u * c⁻¹ ∈ stableUnits A →
      ((u : Aˣ ⧸ stableUnits A)) = ((c : Aˣ ⧸ stableUnits A)) := by
    intro u hu
    apply QuotientGroup.eq.mpr
    have hconj := (stableUnits_normal (R := A)).conj_mem _ hu u⁻¹
    rw [show u⁻¹ * (u * c⁻¹) * u⁻¹⁻¹ = c⁻¹ * u from by group] at hconj
    rw [show u⁻¹ * c = (c⁻¹ * u)⁻¹ from by group]
    exact inv_mem hconj
  have hq : ((c : Aˣ ⧸ stableUnits A)) =
      ((c : Aˣ ⧸ stableUnits A)) * ((c : Aˣ ⧸ stableUnits A)) := by
    calc ((c : Aˣ ⧸ stableUnits A)) =
        ((L.kappaUnit [0] c * L.kappaUnit [1] c : Aˣ) :
          Aˣ ⧸ stableUnits A) := by rw [hprod]
      _ = ((L.kappaUnit [0] c : Aˣ) : Aˣ ⧸ stableUnits A) *
          ((L.kappaUnit [1] c : Aˣ) : Aˣ ⧸ stableUnits A) :=
        QuotientGroup.mk_mul _ _ _
      _ = ((c : Aˣ ⧸ stableUnits A)) * ((c : Aˣ ⧸ stableUnits A)) := by
        rw [hmk _ h0, hmk _ h1]
  have hone : ((c : Aˣ ⧸ stableUnits A)) = 1 := by
    have hcancel : ((c : Aˣ ⧸ stableUnits A)) * 1 =
        ((c : Aˣ ⧸ stableUnits A)) * ((c : Aˣ ⧸ stableUnits A)) := by
      rw [mul_one]
      exact hq
    exact (mul_left_cancel hcancel).symm
  exact (QuotientGroup.eq_one_iff _).mp hone

include L in
/-- **Checkpoint `B4`, reduced form**: if every unit is a central unit
modulo the diagonal class — the rose-graph `K₁` computation — then the
diagonal class group is everything. -/
theorem stableUnits_eq_top [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (hscalar : ∀ u : Aˣ, ∃ c : Aˣ,
      (∀ x : A, (c : A) * x = x * (c : A)) ∧
        c⁻¹ * u ∈ stableUnits A) :
    ∀ u : Aˣ, u ∈ stableUnits A := by
  intro u
  obtain ⟨c, hc, hcu⟩ := hscalar u
  have hcmem := L.central_mem_stableUnits hdiv c hc
  have := mul_mem hcmem hcu
  rwa [show c * (c⁻¹ * u) = u from by group] at this

end Scalar

end LeavittFamily
end NonsoficGroupsExist
