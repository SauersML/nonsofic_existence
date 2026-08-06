import NonsoficGroupsExist.KOne.StableUnitsGenerators
import NonsoficGroupsExist.Leavitt.LeavittWords

/-!
# Incomparable unipotents and mixed cylinder swaps

For prefix-incomparable words `a, b` the element `t_b s_a` vanishes,
so `1 + x·(s_a y t_b)` is unipotent for every `x, y` and the
Whitehead unipotent lemma places any unit with that value in the
diagonal class group — regardless of the degree `|a| - |b|`.  Chaining
three such unipotents yields the signed swap
`1 - p_a - p_b + s_a t_b - s_b t_a` of two incomparable cylinders, the
elementary "tree rebalancing" move of the Higman–Thompson groupoid.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- **Incomparable unipotents die**: for prefix-incomparable `a, b`,
any unit of value `1 + s_a·y·t_b` lies in the diagonal class group. -/
theorem incomparable_unipotent_mem_stableUnits
    {a b : List (Fin 2)} (hab : ¬a <+: b) (hba : ¬b <+: a) (y : A)
    (u : Aˣ) (hu : (u : A) = 1 + L.wordS a * y * L.wordT b) :
    u ∈ stableUnits A := by
  refine mem_stableUnits_of_val_unipotent (L.wordS a * y) (L.wordT b)
    ?_ (by rw [hu])
  rw [show L.wordT b * (L.wordS a * y) = (L.wordT b * L.wordS a) * y
    from by noncomm_ring, L.wordT_mul_wordS_of_incomparable b a hba hab,
    zero_mul]

/-- The unipotent `1 + s_a y t_b` is a genuine unit: its inverse is
`1 - s_a y t_b`. -/
def incomparableUnit {a b : List (Fin 2)} (hab : ¬a <+: b)
    (hba : ¬b <+: a) (y : A) : Aˣ where
  val := 1 + L.wordS a * y * L.wordT b
  inv := 1 - L.wordS a * y * L.wordT b
  val_inv := by
    have hz : L.wordS a * y * L.wordT b * (L.wordS a * y * L.wordT b) =
        0 := by
      rw [show L.wordS a * y * L.wordT b * (L.wordS a * y * L.wordT b) =
        L.wordS a * y * (L.wordT b * L.wordS a) * (y * L.wordT b)
        from by noncomm_ring,
        L.wordT_mul_wordS_of_incomparable b a hba hab]
      noncomm_ring
    calc (1 + L.wordS a * y * L.wordT b) *
          (1 - L.wordS a * y * L.wordT b)
        = 1 - L.wordS a * y * L.wordT b * (L.wordS a * y * L.wordT b) :=
          by noncomm_ring
      _ = 1 := by rw [hz, sub_zero]
  inv_val := by
    have hz : L.wordS a * y * L.wordT b * (L.wordS a * y * L.wordT b) =
        0 := by
      rw [show L.wordS a * y * L.wordT b * (L.wordS a * y * L.wordT b) =
        L.wordS a * y * (L.wordT b * L.wordS a) * (y * L.wordT b)
        from by noncomm_ring,
        L.wordT_mul_wordS_of_incomparable b a hba hab]
      noncomm_ring
    calc (1 - L.wordS a * y * L.wordT b) *
          (1 + L.wordS a * y * L.wordT b)
        = 1 - L.wordS a * y * L.wordT b * (L.wordS a * y * L.wordT b) :=
          by noncomm_ring
      _ = 1 := by rw [hz, sub_zero]

theorem incomparableUnit_mem {a b : List (Fin 2)} (hab : ¬a <+: b)
    (hba : ¬b <+: a) (y : A) :
    L.incomparableUnit hab hba y ∈ stableUnits A :=
  L.incomparable_unipotent_mem_stableUnits hab hba y _ rfl

/-- The signed swap of two incomparable cylinders, as the `SL₂`-style
product of three incomparable unipotents. -/
def signedSwap {a b : List (Fin 2)} (hab : ¬a <+: b) (hba : ¬b <+: a) :
    Aˣ :=
  L.incomparableUnit hab hba 1 * (L.incomparableUnit hba hab (-1)) *
    L.incomparableUnit hab hba 1

theorem signedSwap_mem {a b : List (Fin 2)} (hab : ¬a <+: b)
    (hba : ¬b <+: a) : L.signedSwap hab hba ∈ stableUnits A :=
  mul_mem (mul_mem (L.incomparableUnit_mem hab hba 1)
    (L.incomparableUnit_mem hba hab (-1)))
    (L.incomparableUnit_mem hab hba 1)

/-- The signed swap has the expected value
`1 - p_a - p_b + s_a t_b - s_b t_a`. -/
theorem signedSwap_val {a b : List (Fin 2)} (hab : ¬a <+: b)
    (hba : ¬b <+: a) :
    (L.signedSwap hab hba : A) =
      1 - L.cylinder a - L.cylinder b +
        L.wordS a * L.wordT b - L.wordS b * L.wordT a := by
  set X : A := L.wordS a * L.wordT b with hX
  set Y : A := L.wordS b * L.wordT a with hY
  have hXX : X * X = 0 := by
    rw [hX, show L.wordS a * L.wordT b * (L.wordS a * L.wordT b) =
      L.wordS a * (L.wordT b * L.wordS a) * L.wordT b from by
        noncomm_ring,
      L.wordT_mul_wordS_of_incomparable b a hba hab]
    noncomm_ring
  have hXY : X * Y = L.cylinder a := by
    rw [hX, hY, show L.wordS a * L.wordT b * (L.wordS b * L.wordT a) =
      L.wordS a * (L.wordT b * L.wordS b) * L.wordT a from by
        noncomm_ring,
      L.wordT_mul_wordS_self b, cylinder]
    noncomm_ring
  have hYX : Y * X = L.cylinder b := by
    rw [hX, hY, show L.wordS b * L.wordT a * (L.wordS a * L.wordT b) =
      L.wordS b * (L.wordT a * L.wordS a) * L.wordT b from by
        noncomm_ring,
      L.wordT_mul_wordS_self a, cylinder]
    noncomm_ring
  have hXYX : X * Y * X = X := by
    rw [hXY, hX, cylinder, show L.wordS a * L.wordT a *
      (L.wordS a * L.wordT b) =
      L.wordS a * (L.wordT a * L.wordS a) * L.wordT b from by
        noncomm_ring,
      L.wordT_mul_wordS_self a]
    noncomm_ring
  have hval : (L.signedSwap hab hba : A) = (1 + X) * (1 - Y) * (1 + X) := by
    show (1 + L.wordS a * 1 * L.wordT b) * (1 + L.wordS b * (-1) *
      L.wordT a) * (1 + L.wordS a * 1 * L.wordT b) = _
    rw [hX, hY]
    noncomm_ring
  rw [hval]
  calc (1 + X) * (1 - Y) * (1 + X)
      = 1 + X + X - Y + X * X - X * Y - Y * X - X * Y * X := by
        noncomm_ring
    _ = 1 + X + X - Y + 0 - L.cylinder a - L.cylinder b - X := by
        rw [hXYX, hXX, hXY, hYX]
    _ = 1 - L.cylinder a - L.cylinder b + X - Y := by noncomm_ring

end LeavittFamily
end NonsoficGroupsExist
