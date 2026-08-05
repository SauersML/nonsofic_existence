import NonsoficGroupsExist.MatrixDiagonalization

/-!
# The diagonal class group of a ring

Checkpoint `B4` infrastructure: the subgroup of units `u` with
`diag(u, 1)` elementary, as the comap of `EL₂` along the diagonal
embedding.  It is normal in `Rˣ` because diagonal conjugates of
transvections are transvections, and under the strong division property
the whole of `EL₂` is normal in `GL₂` because the proved rank-two
Gaussian elimination decomposes any invertible matrix into elementaries
and a diagonal.  The remaining `B4` content — that for the binary
Leavitt algebra this subgroup is everything — reduces modulo this file
to the rose-graph `K₁` computation.
-/

namespace NonsoficGroupsExist
namespace MatrixDiagonalization

variable {R : Type*} [Ring R]

theorem diagUnit_one : diagUnit (1 : Rˣ) = 1 := by
  apply Units.ext
  show !![((1 : Rˣ) : R), 0; 0, 1] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnit_mul (u v : Rˣ) :
    diagUnit (u * v) = diagUnit u * diagUnit v := by
  apply Units.ext
  show !![((u * v : Rˣ) : R), 0; 0, 1] =
    !![(u : R), 0; 0, 1] * !![(v : R), 0; 0, 1]
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The diagonal embedding `u ↦ diag(u, 1)` as a homomorphism. -/
def diagUnitHom : Rˣ →* (Matrix (Fin 2) (Fin 2) R)ˣ where
  toFun := diagUnit
  map_one' := diagUnit_one
  map_mul' := diagUnit_mul

@[simp] theorem diagUnitHom_apply (u : Rˣ) :
    diagUnitHom u = diagUnit u := rfl

theorem diagUnit_conj_elementary01 (u : Rˣ) (a : R) :
    diagUnit u * elementaryUnit (0 : Fin 2) 1 (by decide) a *
      (diagUnit u)⁻¹ =
      elementaryUnit (0 : Fin 2) 1 (by decide) ((u : R) * a) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, elementaryUnit01_val,
    elementaryUnit01_val]
  show !![(u : R), 0; 0, 1] * !![1, a; 0, 1] *
    !![((u⁻¹ : Rˣ) : R), 0; 0, 1] = _
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnit_conj_elementary10 (u : Rˣ) (a : R) :
    diagUnit u * elementaryUnit (1 : Fin 2) 0 (by decide) a *
      (diagUnit u)⁻¹ =
      elementaryUnit (1 : Fin 2) 0 (by decide)
        (a * ((u⁻¹ : Rˣ) : R)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, elementaryUnit10_val,
    elementaryUnit10_val]
  show !![(u : R), 0; 0, 1] * !![1, 0; a, 1] *
    !![((u⁻¹ : Rˣ) : R), 0; 0, 1] = _
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Diagonal conjugates of rank-two elementaries are elementary. -/
theorem diagUnit_conj_mem {E : (Matrix (Fin 2) (Fin 2) R)ˣ}
    (hE : E ∈ elementaryGroup (Fin 2) R) (u : Rˣ) :
    diagUnit u * E * (diagUnit u)⁻¹ ∈ elementaryGroup (Fin 2) R := by
  induction hE using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨i, j, hij, a, rfl⟩ := hz
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · rw [show elementaryUnit (0 : Fin 2) 1 hij a =
        elementaryUnit (0 : Fin 2) 1 (by decide) a from rfl,
        diagUnit_conj_elementary01]
      exact elementaryUnit_mem _ _ _ _
    · rw [show elementaryUnit (1 : Fin 2) 0 hij a =
        elementaryUnit (1 : Fin 2) 0 (by decide) a from rfl,
        diagUnit_conj_elementary10]
      exact elementaryUnit_mem _ _ _ _
    · exact absurd rfl hij
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    rw [show diagUnit u * (x * y) * (diagUnit u)⁻¹ =
      (diagUnit u * x * (diagUnit u)⁻¹) *
        (diagUnit u * y * (diagUnit u)⁻¹) from by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show diagUnit u * x⁻¹ * (diagUnit u)⁻¹ =
      (diagUnit u * x * (diagUnit u)⁻¹)⁻¹ from by group]
    exact inv_mem hx

/-- The units whose diagonal stabilization is elementary. -/
def stableUnits (R : Type*) [Ring R] : Subgroup Rˣ :=
  (elementaryGroup (Fin 2) R).comap diagUnitHom

theorem mem_stableUnits_iff (u : Rˣ) :
    u ∈ stableUnits R ↔ diagUnit u ∈ elementaryGroup (Fin 2) R :=
  Iff.rfl

/-- The diagonal class subgroup is normal in the unit group. -/
instance stableUnits_normal : (stableUnits R).Normal := by
  constructor
  intro u hu g
  rw [mem_stableUnits_iff] at hu ⊢
  rw [show diagUnit (g * u * g⁻¹) =
    diagUnit g * diagUnit u * (diagUnit g)⁻¹ from by
      rw [diagUnit_mul, diagUnit_mul]
      congr 1
      exact map_inv diagUnitHom g]
  exact diagUnit_conj_mem hu g

/-- Under strong division, every invertible two-by-two matrix normalizes
the elementary group: Gaussian elimination writes it as elementaries
around a diagonal, and both factors normalize. -/
theorem conj_mem_elementaryGroup_of_division [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (X : (Matrix (Fin 2) (Fin 2) R)ˣ)
    {E : (Matrix (Fin 2) (Fin 2) R)ˣ}
    (hE : E ∈ elementaryGroup (Fin 2) R) :
    X * E * X⁻¹ ∈ elementaryGroup (Fin 2) R := by
  obtain ⟨E', F', u, hE', hF', hEAF⟩ := exists_elementary_mul_diag hdiv X
  have hX : X = E'⁻¹ * diagUnit u * F'⁻¹ := by
    rw [← hEAF]
    group
  have hinner : F'⁻¹ * E * F' ∈ elementaryGroup (Fin 2) R :=
    mul_mem (mul_mem (inv_mem hF') hE) hF'
  have hmid := diagUnit_conj_mem hinner u
  have hout : E'⁻¹ * (diagUnit u * (F'⁻¹ * E * F') * (diagUnit u)⁻¹) *
      E' ∈ elementaryGroup (Fin 2) R :=
    mul_mem (mul_mem (inv_mem hE') hmid) hE'
  rw [show X * E * X⁻¹ =
    E'⁻¹ * (diagUnit u * (F'⁻¹ * E * F') * (diagUnit u)⁻¹) * E' from by
      rw [hX]
      group]
  exact hout

/-- Under strong division, `EL₂` is normal in `GL₂`. -/
theorem elementaryGroup_normal_of_division [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1) :
    (elementaryGroup (Fin 2) R).Normal := by
  constructor
  intro E hE X
  exact conj_mem_elementaryGroup_of_division hdiv X hE

end MatrixDiagonalization
end NonsoficGroupsExist
