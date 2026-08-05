import NonsoficGroupsExist.UniversalLeavittOver
import NonsoficGroupsExist.LeavittWindowReduction

/-!
# Scaled stream representations

The gauge-scaled family of stream representations: for a unit `c` of
the ground field, the operators `c•Pᵢ`, `c⁻¹•Dᵢ` again satisfy the
Leavitt relations, and the induced representation multiplies a
degree-`d` element by `c^d` relative to the unscaled representation.
Together with faithfulness of the stream representation — immediate
from simplicity — this is the engine of graded independence for the
Laurent half of the rose-graph `K₁` computation.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

variable (K : Type) [Field K]

/-- The stream family scaled by a unit of the ground field. -/
def scaledStreamFamily (c : Kˣ) :
    LeavittFamily (Module.End K (StreamSpace K)) where
  s0 := (c : K) • prefixOperator K 0
  s1 := (c : K) • prefixOperator K 1
  t0 := ((c⁻¹ : Kˣ) : K) • deleteOperator K 0
  t1 := ((c⁻¹ : Kˣ) : K) • deleteOperator K 1
  t0_s0 := by
    rw [smul_mul_smul_comm, Units.inv_mul, delete_mul_prefix_same,
      one_smul]
  t0_s1 := by
    rw [smul_mul_smul_comm,
      delete_mul_prefix_ne K (by decide : (0 : Fin 2) ≠ 1), smul_zero]
  t1_s0 := by
    rw [smul_mul_smul_comm,
      delete_mul_prefix_ne K (by decide : (1 : Fin 2) ≠ 0), smul_zero]
  t1_s1 := by
    rw [smul_mul_smul_comm, Units.inv_mul, delete_mul_prefix_same,
      one_smul]
  sum_range := by
    rw [smul_mul_smul_comm, smul_mul_smul_comm, Units.mul_inv, one_smul,
      one_smul, prefix_delete_sum]

/-- The scaled stream representation. -/
noncomputable def scaledStreamRepresentation (c : Kˣ) :
    BinaryLeavittAlgebra K →ₐ[K] Module.End K (StreamSpace K) :=
  lift (scaledStreamFamily K c)

theorem scaledStreamRepresentation_s (c : Kˣ) (i : Fin 2) :
    scaledStreamRepresentation K c ((family K).s i) =
      (c : K) • streamRepresentation K ((family K).s i) := by
  fin_cases i <;>
    simp [scaledStreamRepresentation, streamRepresentation, family,
      LeavittFamily.s, scaledStreamFamily, streamFamily, s0, s1, t0, t1]

theorem scaledStreamRepresentation_t (c : Kˣ) (i : Fin 2) :
    scaledStreamRepresentation K c ((family K).t i) =
      ((c⁻¹ : Kˣ) : K) • streamRepresentation K ((family K).t i) := by
  fin_cases i <;>
    simp [scaledStreamRepresentation, streamRepresentation, family,
      LeavittFamily.t, scaledStreamFamily, streamFamily, s0, s1, t0, t1]

theorem scaledStreamRepresentation_wordS (c : Kˣ) (a : List (Fin 2)) :
    scaledStreamRepresentation K c ((family K).wordS a) =
      (c : K) ^ a.length •
        streamRepresentation K ((family K).wordS a) := by
  induction a with
  | nil => simp
  | cons i a ih =>
      rw [LeavittFamily.wordS_cons, map_mul, map_mul, ih,
        scaledStreamRepresentation_s, smul_mul_smul_comm,
        List.length_cons, pow_succ]
      ring_nf

theorem scaledStreamRepresentation_wordT (c : Kˣ) (b : List (Fin 2)) :
    scaledStreamRepresentation K c ((family K).wordT b) =
      ((c⁻¹ : Kˣ) : K) ^ b.length •
        streamRepresentation K ((family K).wordT b) := by
  induction b with
  | nil => simp
  | cons i b ih =>
      rw [LeavittFamily.wordT_cons, map_mul, map_mul, ih,
        scaledStreamRepresentation_t, smul_mul_smul_comm,
        List.length_cons, pow_succ]

/-- **Degree scaling**: on the span of degree-`d` monomials the scaled
representation is `c^d` times the unscaled one. -/
theorem scaledStreamRepresentation_degree (c : Kˣ) (d : ℤ) {x : BinaryLeavittAlgebra K}
    (hx : x ∈ Submodule.span K ((family K).degreeMonomials d d)) :
    scaledStreamRepresentation K c x =
      ((c ^ d : Kˣ) : K) • streamRepresentation K x := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      have hd : (a.length : ℤ) - b.length = d := le_antisymm hh hl
      rw [map_mul, map_mul, scaledStreamRepresentation_wordS,
        scaledStreamRepresentation_wordT, smul_mul_smul_comm]
      congr 1
      have hzpow : ((c ^ d : Kˣ) : K) =
          (c : K) ^ a.length * ((c⁻¹ : Kˣ) : K) ^ b.length := by
        have h1 : (c ^ d : Kˣ) = c ^ ((a.length : ℤ) - b.length) := by
          rw [hd]
        rw [h1, zpow_sub, zpow_natCast, zpow_natCast]
        push_cast
        rw [inv_pow]
      rw [hzpow]
  | zero => rw [map_zero, map_zero, smul_zero]
  | add x y _ _ hx hy =>
      rw [map_add, map_add, hx, hy, smul_add]
  | smul r x _ hx =>
      rw [map_smul, map_smul, hx, smul_comm]

/-- **Faithfulness by simplicity**: the stream representation is
injective. -/
theorem streamRepresentation_injective :
    Function.Injective (streamRepresentation K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  obtain ⟨p, q, hpq⟩ := exists_mul_mul_eq_one K hne
  have h1 := congrArg (streamRepresentation K) hpq
  rw [map_mul, map_mul, hx, mul_zero, zero_mul, map_one] at h1
  have h2 := congrArg (fun F : Module.End K (StreamSpace K) ↦
    F (fun _ ↦ (1 : K)) (fun _ ↦ 0)) h1
  simp at h2

end BinaryLeavitt
end NonsoficGroupsExist
