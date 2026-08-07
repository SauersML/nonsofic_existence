import NonsoficGroupsExist.Leavitt.FamilyDiagonalClass
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Field-coefficient matrices reduce to central scalars

The Gaussian-elimination endgame of the degree-zero rose-graph `K₁`
computation.  A unit of `A` that a complete matrix family identifies
with a matrix of central field coefficients factors, by Mathlib's
transvection decomposition over the field, into transvections and an
invertible central diagonal.  Transvections pull back to unipotents in
the diagonal class group and the diagonal pulls back to a central
scalar modulo it, so the whole unit lies in `centralClassGroup A`.
-/

-- Scoped to this file only: several `simp only` lists here carry lemmas that
-- fire on some goals of a case split and not others; splitting every list
-- per-branch was tried and read worse than the uniform list.  The linter has
-- no per-branch view, so it flags the branch that did not need a lemma.
set_option linter.unusedSimpArgs false

namespace NonsoficGroupsExist
namespace MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A transvection over an arbitrary ring, as a unit of the matrix
ring. -/
def transvectionUnit (i j : ι) (hij : i ≠ j) (c : A) : (Matrix ι ι A)ˣ where
  val := 1 + Matrix.single i j c
  inv := 1 - Matrix.single i j c
  val_inv := by
    have hz : Matrix.single i j c * Matrix.single i j c =
        (0 : Matrix ι ι A) :=
      Matrix.single_mul_single_of_ne c i j i (Ne.symm hij) c
    calc (1 + Matrix.single i j c) * (1 - Matrix.single i j c)
        = 1 - Matrix.single i j c * Matrix.single i j c := by noncomm_ring
      _ = 1 := by rw [hz, sub_zero]
  inv_val := by
    have hz : Matrix.single i j c * Matrix.single i j c =
        (0 : Matrix ι ι A) :=
      Matrix.single_mul_single_of_ne c i j i (Ne.symm hij) c
    calc (1 - Matrix.single i j c) * (1 + Matrix.single i j c)
        = 1 - Matrix.single i j c * Matrix.single i j c := by noncomm_ring
      _ = 1 := by rw [hz, sub_zero]

@[simp] theorem transvectionUnit_val (i j : ι) (hij : i ≠ j) (c : A) :
    ((transvectionUnit i j hij c : (Matrix ι ι A)ˣ) : Matrix ι ι A) =
      1 + Matrix.single i j c :=
  rfl

/-- Entrywise ring maps carry matrix units to matrix units. -/
theorem mapMatrix_single {B : Type*} [Ring B] (φ : B →+* A) (i j : ι)
    (c : B) :
    φ.mapMatrix (Matrix.single i j c) = Matrix.single i j (φ c) := by
  have hmap : φ.mapMatrix (Matrix.single i j c) =
      (Matrix.single i j c).map φ := rfl
  rw [hmap]
  ext a b
  rw [Matrix.map_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [Matrix.single_apply_same i j c, Matrix.single_apply_same i j (φ c)]
  · rw [Matrix.single_apply_of_ne i j c a b h,
      Matrix.single_apply_of_ne i j (φ c) a b h, map_zero]

/-- Entrywise ring maps carry diagonal matrices to diagonal
matrices. -/
theorem mapMatrix_diagonal {B : Type*} [Ring B] (φ : B →+* A)
    (v : ι → B) :
    φ.mapMatrix (Matrix.diagonal v) = Matrix.diagonal fun i ↦ φ (v i) := by
  have hmap : φ.mapMatrix (Matrix.diagonal v) =
      (Matrix.diagonal v).map φ := rfl
  rw [hmap, Matrix.diagonal_map (map_zero φ)]

end MatrixDiagonalization

namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- **Field-coefficient reduction**: a unit of `A` identified by the
family with a matrix of central field coefficients is a central scalar
modulo the diagonal class group. -/
theorem unitsEquiv_field_matrix_mem_centralClassGroup [Nontrivial A]
    {𝕜 : Type*} [Field 𝕜]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (φ : 𝕜 →+* A) (hφ : ∀ r : 𝕜, ∀ x : A, φ r * x = x * φ r)
    (C : Matrix ι ι 𝕜) (U : (Matrix ι ι A)ˣ)
    (hU : (U : Matrix ι ι A) = φ.mapMatrix C) :
    F.unitsEquiv U ∈ centralClassGroup A := by
  classical
  obtain ⟨L, L', D, hC⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec C
  let TU : Matrix.TransvectionStruct ι 𝕜 → (Matrix ι ι A)ˣ := fun τ ↦
    transvectionUnit τ.i τ.j τ.hij (φ τ.c)
  have hTUval : ∀ τ : Matrix.TransvectionStruct ι 𝕜,
      ((TU τ : (Matrix ι ι A)ˣ) : Matrix ι ι A) =
        φ.mapMatrix τ.toMatrix := by
    intro τ
    show 1 + Matrix.single τ.i τ.j (φ τ.c) = φ.mapMatrix τ.toMatrix
    rw [show Matrix.TransvectionStruct.toMatrix τ =
      1 + Matrix.single τ.i τ.j τ.c from rfl, map_add, map_one,
      mapMatrix_single]
  have hprodval : ∀ M : List (Matrix.TransvectionStruct ι 𝕜),
      (((M.map TU).prod : (Matrix ι ι A)ˣ) : Matrix ι ι A) =
        φ.mapMatrix (M.map Matrix.TransvectionStruct.toMatrix).prod := by
    intro M
    calc (((M.map TU).prod : (Matrix ι ι A)ˣ) : Matrix ι ι A)
        = ((M.map TU).map (Units.coeHom (Matrix ι ι A))).prod :=
          map_list_prod (Units.coeHom (Matrix ι ι A)) (M.map TU)
      _ = (M.map fun τ ↦ φ.mapMatrix τ.toMatrix).prod := by
          rw [List.map_map]
          exact congrArg List.prod
            (List.map_congr_left fun τ _ ↦ hTUval τ)
      _ = ((M.map Matrix.TransvectionStruct.toMatrix).map
            φ.mapMatrix).prod := by
          rw [List.map_map]
          rfl
      _ = φ.mapMatrix (M.map Matrix.TransvectionStruct.toMatrix).prod :=
          (map_list_prod φ.mapMatrix
            (M.map Matrix.TransvectionStruct.toMatrix)).symm
  set TP : (Matrix ι ι A)ˣ := (L.map TU).prod with hTPdef
  set TP' : (Matrix ι ι A)ˣ := (L'.map TU).prod with hTP'def
  set DU : (Matrix ι ι A)ˣ := TP⁻¹ * U * TP'⁻¹ with hDUdef
  have hDUval : (DU : Matrix ι ι A) =
      Matrix.diagonal fun i ↦ φ (D i) := by
    have hmid : (U : Matrix ι ι A) = (TP : Matrix ι ι A) *
        ((Matrix.diagonal fun i ↦ φ (D i)) * (TP' : Matrix ι ι A)) := by
      rw [hTPdef, hTP'def, hU, hC, map_mul, map_mul, ← hprodval L,
        ← hprodval L', mapMatrix_diagonal, mul_assoc]
    calc (DU : Matrix ι ι A)
        = ((TP⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) * (U : Matrix ι ι A) *
            ((TP'⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) := rfl
      _ = Matrix.diagonal fun i ↦ φ (D i) := by
          rw [hmid, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul,
            mul_assoc, Units.mul_inv, mul_one]
  have hDentry : ∀ i : ι,
      φ (D i) * ((DU⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) i i = 1 ∧
      ((DU⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) i i * φ (D i) = 1 := by
    intro i
    have h1 := congrFun (congrFun (Units.mul_inv DU) i) i
    rw [hDUval] at h1
    simp only [Matrix.diagonal_mul, Matrix.one_apply_eq] at h1
    have h2 := congrFun (congrFun (Units.inv_mul DU) i) i
    rw [hDUval] at h2
    simp only [Matrix.mul_diagonal, Matrix.one_apply_eq] at h2
    exact ⟨h1, h2⟩
  let d : ι → Aˣ := fun i ↦
    ⟨φ (D i), ((DU⁻¹ : (Matrix ι ι A)ˣ) : Matrix ι ι A) i i,
      (hDentry i).1, (hDentry i).2⟩
  have hDUmem : F.unitsEquiv DU ∈ centralClassGroup A := by
    refine F.unitsEquiv_diagonal_mem_centralClassGroup hdiv d
      (fun i x ↦ hφ (D i) x) DU ?_
    rw [hDUval]
  have hTmem : ∀ M : List (Matrix.TransvectionStruct ι 𝕜),
      F.unitsEquiv (M.map TU).prod ∈ stableUnits A := by
    intro M
    rw [map_list_prod F.unitsEquiv (M.map TU)]
    refine list_prod_mem fun x hx ↦ ?_
    rw [List.map_map, List.mem_map] at hx
    obtain ⟨τ, _, rfl⟩ := hx
    exact F.unitsEquiv_unipotent_mem_stableUnits τ.hij (φ τ.c) (TU τ) rfl
  have hUfact : U = TP * DU * TP' := by
    rw [hDUdef]
    group
  rw [hUfact, map_mul, map_mul]
  exact mul_mem
    (mul_mem (stableUnits_le_centralClassGroup (hTmem L)) hDUmem)
    (stableUnits_le_centralClassGroup (hTmem L'))

end CompleteMatrixFamily
end NonsoficGroupsExist
