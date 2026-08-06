import NonsoficGroupsExist.Leavitt.UniversalLeavittOver
import NonsoficGroupsExist.Leavitt.LeavittWindowReduction
import Mathlib.Algebra.Algebra.Opposite

/-!
# The transpose anti-automorphism of the binary Leavitt algebra

The opposite ring of any ring carrying a binary Leavitt family
carries one as well, with the roles of `s` and `t` exchanged; the
universal property therefore produces an algebra map
`θ : L_k(1,2) →ₐ (L_k(1,2))ᵐᵒᵖ`, whose unopped form `θ̂` is the
classical transpose anti-automorphism `s_i ↔ t_i`.  It is an
involution, sends `s_a t_b` to `s_b t_a`, and hence flips degree
windows: the span of `[lo, hi]` maps into the span of `[-hi, -lo]`.
This transports every one-sided window theorem to its mirror.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MulOpposite

/-- Any binary Leavitt family induces one on the opposite ring with
`s` and `t` exchanged. -/
def oppositeFamily {A : Type*} [Ring A] (L : LeavittFamily A) :
    LeavittFamily Aᵐᵒᵖ where
  s0 := op L.t0
  s1 := op L.t1
  t0 := op L.s0
  t1 := op L.s1
  t0_s0 := by rw [← op_mul, L.t0_s0, op_one]
  t0_s1 := by rw [← op_mul, L.t1_s0, op_zero]
  t1_s0 := by rw [← op_mul, L.t0_s1, op_zero]
  t1_s1 := by rw [← op_mul, L.t1_s1, op_one]
  sum_range := by rw [← op_mul, ← op_mul, ← op_add, L.sum_range, op_one]

variable (k : Type) [Field k]

/-- The universal map to the opposite algebra. -/
noncomputable def theta :
    BinaryLeavittAlgebra k →ₐ[k] (BinaryLeavittAlgebra k)ᵐᵒᵖ :=
  lift (oppositeFamily (family k))

/-- The transpose anti-automorphism (unopped form). -/
noncomputable def thetaHat (x : BinaryLeavittAlgebra k) :
    BinaryLeavittAlgebra k :=
  unop (theta k x)

theorem thetaHat_add (x y : BinaryLeavittAlgebra k) :
    thetaHat k (x + y) = thetaHat k x + thetaHat k y := by
  unfold thetaHat
  rw [map_add, unop_add]

theorem thetaHat_mul (x y : BinaryLeavittAlgebra k) :
    thetaHat k (x * y) = thetaHat k y * thetaHat k x := by
  unfold thetaHat
  rw [map_mul, unop_mul]

theorem thetaHat_one : thetaHat k 1 = 1 := by
  unfold thetaHat
  rw [map_one, unop_one]

theorem thetaHat_zero : thetaHat k 0 = 0 := by
  unfold thetaHat
  rw [map_zero, unop_zero]

theorem thetaHat_smul (c : k) (x : BinaryLeavittAlgebra k) :
    thetaHat k (c • x) = c • thetaHat k x := by
  unfold thetaHat
  rw [map_smul]
  rfl

theorem thetaHat_sub (x y : BinaryLeavittAlgebra k) :
    thetaHat k (x - y) = thetaHat k x - thetaHat k y := by
  unfold thetaHat
  rw [map_sub, unop_sub]

/-- `θ̂` exchanges the generators. -/
theorem thetaHat_s0 : thetaHat k ((family k).s0) = (family k).t0 := by
  unfold thetaHat theta
  show unop (lift (oppositeFamily (family k)) (generator k s0)) = _
  rw [lift_generator]
  rfl

theorem thetaHat_s1 : thetaHat k ((family k).s1) = (family k).t1 := by
  unfold thetaHat theta
  show unop (lift (oppositeFamily (family k)) (generator k s1)) = _
  rw [lift_generator]
  rfl

theorem thetaHat_t0 : thetaHat k ((family k).t0) = (family k).s0 := by
  unfold thetaHat theta
  show unop (lift (oppositeFamily (family k)) (generator k t0)) = _
  rw [lift_generator]
  rfl

theorem thetaHat_t1 : thetaHat k ((family k).t1) = (family k).s1 := by
  unfold thetaHat theta
  show unop (lift (oppositeFamily (family k)) (generator k t1)) = _
  rw [lift_generator]
  rfl

theorem thetaHat_s (i : Fin 2) :
    thetaHat k ((family k).s i) = (family k).t i := by
  fin_cases i
  · exact thetaHat_s0 k
  · exact thetaHat_s1 k

theorem thetaHat_t (i : Fin 2) :
    thetaHat k ((family k).t i) = (family k).s i := by
  fin_cases i
  · exact thetaHat_t0 k
  · exact thetaHat_t1 k

/-- `θ̂` reverses words: `s_a ↦ t_a`. -/
theorem thetaHat_wordS (a : List (Fin 2)) :
    thetaHat k ((family k).wordS a) = (family k).wordT a := by
  induction a with
  | nil =>
      rw [wordS_nil, wordT_nil]
      exact thetaHat_one k
  | cons i a ih =>
      rw [wordS_cons, wordT_cons, thetaHat_mul, ih, thetaHat_s]

theorem thetaHat_wordT (b : List (Fin 2)) :
    thetaHat k ((family k).wordT b) = (family k).wordS b := by
  induction b with
  | nil =>
      rw [wordS_nil, wordT_nil]
      exact thetaHat_one k
  | cons i b ih =>
      rw [wordS_cons, wordT_cons, thetaHat_mul, ih, thetaHat_t]

/-- The generators generate. -/
theorem adjoin_generators_eq_top :
    Algebra.adjoin k (Set.range (generator k)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (Relation k) x
  have hp : p ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k)) := by
    rw [FreeAlgebra.adjoin_range_ι]
    exact Algebra.mem_top
  have h1 : RingQuot.mkAlgHom k (Relation k) p ∈
      Algebra.adjoin k ((RingQuot.mkAlgHom k (Relation k)) ''
        Set.range (FreeAlgebra.ι k)) := by
    rw [← AlgHom.map_adjoin]
    exact Set.mem_image_of_mem _ hp
  refine Algebra.adjoin_mono ?_ h1
  rintro y ⟨z, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, rfl⟩

/-- `θ̂` is an involution. -/
theorem thetaHat_thetaHat (x : BinaryLeavittAlgebra k) :
    thetaHat k (thetaHat k x) = x := by
  have hx : x ∈ Algebra.adjoin k (Set.range (generator k)) := by
    rw [adjoin_generators_eq_top]
    exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      fin_cases g
      -- Spell out the right-hand side too.  With `= _` it stays the raw
      -- `generator k ⟨0, _⟩` that `fin_cases` produced, and the residual
      -- `(family k).s0 = generator k ⟨0, _⟩` is defeq only at a transparency
      -- `rw`'s trailing `rfl` will not use.
      · show thetaHat k (thetaHat k ((family k).s0)) = (family k).s0
        rw [thetaHat_s0, thetaHat_t0]
      · show thetaHat k (thetaHat k ((family k).s1)) = (family k).s1
        rw [thetaHat_s1, thetaHat_t1]
      · show thetaHat k (thetaHat k ((family k).t0)) = (family k).t0
        rw [thetaHat_t0, thetaHat_s0]
      · show thetaHat k (thetaHat k ((family k).t1)) = (family k).t1
        rw [thetaHat_t1, thetaHat_s1]
  | algebraMap c =>
      have h1 : (algebraMap k (BinaryLeavittAlgebra k)) c =
          c • (1 : BinaryLeavittAlgebra k) := by
        rw [Algebra.smul_def, mul_one]
      rw [h1, thetaHat_smul, thetaHat_one, thetaHat_smul, thetaHat_one]
  | add y z _ _ hy hz =>
      rw [thetaHat_add, thetaHat_add, hy, hz]
  | mul y z _ _ hy hz =>
      rw [thetaHat_mul, thetaHat_mul, hy, hz]

/-- `θ̂` flips degree windows. -/
theorem thetaHat_mem_span_degree {lo hi : ℤ}
    {x : BinaryLeavittAlgebra k}
    (hx : x ∈ Submodule.span k ((family k).degreeMonomials lo hi)) :
    thetaHat k x ∈
      Submodule.span k ((family k).degreeMonomials (-hi) (-lo)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hy
      rw [thetaHat_mul, thetaHat_wordS, thetaHat_wordT]
      exact Submodule.subset_span ⟨b, a, by omega, by omega, rfl⟩
  | zero =>
      rw [thetaHat_zero]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [thetaHat_add]
      exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
      rw [thetaHat_smul]
      exact Submodule.smul_mem _ c hy

/-- The unit induced by `θ̂`. -/
noncomputable def thetaUnit (u : (BinaryLeavittAlgebra k)ˣ) :
    (BinaryLeavittAlgebra k)ˣ where
  val := thetaHat k (u : BinaryLeavittAlgebra k)
  inv := thetaHat k ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
    BinaryLeavittAlgebra k)
  val_inv := by
    rw [← thetaHat_mul, Units.inv_mul, thetaHat_one]
  inv_val := by
    rw [← thetaHat_mul, Units.mul_inv, thetaHat_one]

@[simp] theorem thetaUnit_val (u : (BinaryLeavittAlgebra k)ˣ) :
    ((thetaUnit k u : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) =
    thetaHat k (u : BinaryLeavittAlgebra k) := rfl

end BinaryLeavitt
end NonsoficGroupsExist
