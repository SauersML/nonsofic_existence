import NonsoficGroupsExist.CodePairTransport
import NonsoficGroupsExist.StableUnitsGenerators
import NonsoficGroupsExist.LeavittDiagonalClass
import NonsoficGroupsExist.IncomparableUnipotents
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Scalar matrix moves along an arbitrary complete prefix code

The transport `G ↦ Σᵢⱼ s_{dᵢ}·(algebraMap G i j)·t_{dⱼ}` of scalar
matrices along a complete prefix code `D` — of arbitrary, mixed-depth
shape — is multiplicative, and the image of every invertible scalar
matrix is a unit of the diagonal class group: transvections transport
to incomparable unipotents, and diagonal matrices to products of
`κ`-corner insertions of central scalars.  This provides the
`GL(k)`-normalization moves of the pencil elimination at every stage
of the code refinement, where the codes are no longer of uniform
depth and the balanced-span argument does not apply.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar-matrix transport along a complete prefix code. -/
noncomputable def codeScalar (D : BinaryPrefixCode ι)
    (G : Matrix ι ι k) : A :=
  ∑ i, ∑ j, L.wordS (D.word i) * algebraMap k A (G i j) *
    L.wordT (D.word j)

theorem codeScalar_one (D : BinaryPrefixCode ι)
    (hD : L.IsComplete D) : L.codeScalar (k := k) D 1 = 1 := by
  classical
  unfold codeScalar
  calc ∑ i, ∑ j, L.wordS (D.word i) *
        algebraMap k A ((1 : Matrix ι ι k) i j) * L.wordT (D.word j)
      = ∑ i, ∑ j, (if i = j then
          L.wordS (D.word i) * L.wordT (D.word j) else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Matrix.one_apply, apply_ite (algebraMap k A), map_one,
          map_zero]
        simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    _ = ∑ i, L.wordS (D.word i) * L.wordT (D.word i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
    _ = 1 := hD

theorem codeScalar_mul (D : BinaryPrefixCode ι) (G G' : Matrix ι ι k) :
    L.codeScalar (k := k) D G * L.codeScalar (k := k) D G' =
      L.codeScalar (k := k) D (G * G') := by
  classical
  have h := L.codePair_mul D D.word D.word
    (fun i j ↦ algebraMap k A (G i j))
    (fun j l ↦ algebraMap k A (G' j l))
  beta_reduce at h
  unfold codeScalar
  rw [h]
  refine Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  congr 1
  rw [Matrix.mul_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (map_mul _ _ _).symm

/-- Transvections transport to incomparable unipotents. -/
theorem codeScalar_transvection (D : BinaryPrefixCode ι)
    (hD : L.IsComplete D) {i j : ι} (hij : i ≠ j) (c : k) :
    L.codeScalar (k := k) D (Matrix.transvection i j c) =
      1 + L.wordS (D.word i) * algebraMap k A c *
        L.wordT (D.word j) := by
  classical
  have hbasis : L.codeScalar (k := k) D
      (Matrix.stdBasisMatrix i j c) =
      L.wordS (D.word i) * algebraMap k A c * L.wordT (D.word j) := by
    unfold codeScalar
    calc ∑ i', ∑ j', L.wordS (D.word i') *
          algebraMap k A (Matrix.stdBasisMatrix i j c i' j') *
          L.wordT (D.word j')
        = ∑ i', ∑ j', (if i = i' then (if j = j' then
            L.wordS (D.word i') * algebraMap k A c *
              L.wordT (D.word j') else 0) else 0) := by
          refine Finset.sum_congr rfl fun i' _ ↦
            Finset.sum_congr rfl fun j' _ ↦ ?_
          rw [show Matrix.stdBasisMatrix i j c i' j' =
              (if i = i' ∧ j = j' then c else 0) from rfl, ite_and,
            apply_ite (algebraMap k A), apply_ite (algebraMap k A),
            map_zero]
          simp only [mul_ite, mul_zero, ite_mul, zero_mul]
      _ = ∑ j', (if j = j' then
            L.wordS (D.word i) * algebraMap k A c *
              L.wordT (D.word j') else 0) := by
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
      _ = L.wordS (D.word i) * algebraMap k A c *
            L.wordT (D.word j) := by
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
  have hadd : L.codeScalar (k := k) D
      (1 + Matrix.stdBasisMatrix i j c) =
      L.codeScalar (k := k) D 1 +
        L.codeScalar (k := k) D (Matrix.stdBasisMatrix i j c) := by
    unfold codeScalar
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i' _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [Matrix.add_apply, map_add]
    noncomm_ring
  rw [show Matrix.transvection i j c =
      1 + Matrix.stdBasisMatrix i j c from rfl, hadd, hbasis,
    L.codeScalar_one D hD]

/-- The unit of `A` transporting a scalar diagonal matrix with
nonvanishing entries: the product of `κ`-corner insertions of the
central scalars over the code. -/
theorem codeScalar_diagonal_unit_mem [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (D : BinaryPrefixCode ι) (hD : L.IsComplete D)
    (d : ι → k) (hd : ∀ i, d i ≠ 0) (u : Aˣ)
    (hu : (u : A) = L.codeScalar (k := k) D (Matrix.diagonal d)) :
    u ∈ stableUnits A := by
  classical
  -- the κ-corner unit at each code word
  have hts : ∀ i : ι, L.wordT (D.word i) * L.wordS (D.word i) = 1 :=
    fun i ↦ L.wordT_mul_wordS_self _
  set cunit : ι → Aˣ := fun i ↦
    Units.map (algebraMap k A).toMonoidHom (Units.mk0 (d i) (hd i))
    with hcunit
  set κu : ι → Aˣ := fun i ↦
    pairKappaUnit (L.wordS (D.word i)) (L.wordT (D.word i)) (hts i)
      (cunit i) with hκu
  have hκval : ∀ i : ι, ((κu i : Aˣ) : A) =
      L.wordS (D.word i) * algebraMap k A (d i) * L.wordT (D.word i) +
      (1 - L.wordS (D.word i) * L.wordT (D.word i)) := fun i ↦ rfl
  have hκmem : ∀ i : ι, κu i ∈ stableUnits A := by
    intro i
    have h1 := pairKappaUnit_mul_inv_mem_stableUnits
      (L.wordS (D.word i)) (L.wordT (D.word i)) (hts i) hdiv (cunit i)
    have h2 : cunit i ∈ stableUnits A := by
      refine L.central_mem_stableUnits hdiv (cunit i) fun x ↦ ?_
      exact Algebra.commutes (d i) x
    have h3 : κu i = (κu i * (cunit i)⁻¹) * cunit i := by group
    rw [h3]
    exact mul_mem h1 h2
  -- the product identity over any finset
  have hprod : ∀ s : Finset ι, ((∏ i ∈ s, κu i : Aˣ) : A) =
      (∑ i ∈ s, L.wordS (D.word i) * algebraMap k A (d i) *
        L.wordT (D.word i)) +
      (1 - ∑ i ∈ s, L.wordS (D.word i) * L.wordT (D.word i)) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
        rw [Finset.prod_cons, Units.val_mul, ih, hκval a,
          Finset.sum_cons, Finset.sum_cons]
        have horthTS : ∀ i ∈ s, L.wordT (D.word a) *
            L.wordS (D.word i) = 0 := by
          intro i hi
          have hne : a ≠ i := fun h ↦ ha (h ▸ hi)
          have h := L.prefixCode_orthogonal D a i
          rw [if_neg hne] at h
          exact h
        have horthTS' : ∀ i ∈ s, L.wordT (D.word i) *
            L.wordS (D.word a) = 0 := by
          intro i hi
          have hne : i ≠ a := fun h ↦ ha (h ▸ hi)
          have h := L.prefixCode_orthogonal D i a
          rw [if_neg hne] at h
          exact h
        -- expand the product and kill the cross terms
        set Sa := L.wordS (D.word a) with hSa
        set Ta := L.wordT (D.word a) with hTa
        set da := algebraMap k A (d a) with hda
        set Σd := ∑ i ∈ s, L.wordS (D.word i) * algebraMap k A (d i) *
          L.wordT (D.word i) with hΣd
        set Σp := ∑ i ∈ s, L.wordS (D.word i) * L.wordT (D.word i)
          with hΣp
        have hx1 : (Sa * da * Ta) * Σd = 0 := by
          rw [hΣd, Finset.mul_sum]
          refine Finset.sum_eq_zero fun i hi ↦ ?_
          rw [show Sa * da * Ta * (L.wordS (D.word i) *
              algebraMap k A (d i) * L.wordT (D.word i)) =
            Sa * da * (Ta * L.wordS (D.word i)) *
              (algebraMap k A (d i) * L.wordT (D.word i)) from
              by noncomm_ring, horthTS i hi, mul_zero, zero_mul]
        have hx2 : (Sa * da * Ta) * Σp = 0 := by
          rw [hΣp, Finset.mul_sum]
          refine Finset.sum_eq_zero fun i hi ↦ ?_
          rw [show Sa * da * Ta * (L.wordS (D.word i) *
              L.wordT (D.word i)) =
            Sa * da * (Ta * L.wordS (D.word i)) * L.wordT (D.word i)
              from by noncomm_ring, horthTS i hi, mul_zero, zero_mul]
        have hx3 : (Sa * Ta) * Σd = 0 := by
          rw [hΣd, Finset.mul_sum]
          refine Finset.sum_eq_zero fun i hi ↦ ?_
          rw [show Sa * Ta * (L.wordS (D.word i) *
              algebraMap k A (d i) * L.wordT (D.word i)) =
            Sa * (Ta * L.wordS (D.word i)) *
              (algebraMap k A (d i) * L.wordT (D.word i)) from
              by noncomm_ring, horthTS i hi, mul_zero, zero_mul]
        have hx4 : (Sa * Ta) * Σp = 0 := by
          rw [hΣp, Finset.mul_sum]
          refine Finset.sum_eq_zero fun i hi ↦ ?_
          rw [show Sa * Ta * (L.wordS (D.word i) *
              L.wordT (D.word i)) =
            Sa * (Ta * L.wordS (D.word i)) * L.wordT (D.word i) from
              by noncomm_ring, horthTS i hi, mul_zero, zero_mul]
        calc (Sa * da * Ta + (1 - Sa * Ta)) * (Σd + (1 - Σp))
            = (Sa * da * Ta) * Σd + (Sa * da * Ta) +
              (- ((Sa * da * Ta) * Σp)) + Σd + (1 - Σp) -
              ((Sa * Ta) * Σd) - Sa * Ta +
              (Sa * Ta) * Σp := by noncomm_ring
          _ = Sa * da * Ta + Σd + (1 - (Sa * Ta + Σp)) := by
              rw [hx1, hx2, hx3, hx4]
              noncomm_ring
  -- assemble at the full index set
  have hval : ((∏ i, κu i : Aˣ) : A) = (u : A) := by
    rw [hprod Finset.univ, hu]
    have hcyl : ∑ i, L.wordS (D.word i) * L.wordT (D.word i) = 1 := hD
    rw [hcyl, sub_self, add_zero]
    unfold codeScalar
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).symm
    calc ∑ j, L.wordS (D.word i) *
          algebraMap k A (Matrix.diagonal d i j) * L.wordT (D.word j)
        = ∑ j, (if i = j then L.wordS (D.word i) *
            algebraMap k A (d i) * L.wordT (D.word j) else 0) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Matrix.diagonal_apply, apply_ite (algebraMap k A),
            map_zero]
          simp only [mul_ite, mul_zero, ite_mul, zero_mul]
      _ = L.wordS (D.word i) * algebraMap k A (d i) *
            L.wordT (D.word i) := by
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  have huprod : u = ∏ i, κu i := Units.ext hval.symm
  rw [huprod]
  exact prod_mem fun i _ ↦ hκmem i

/-- Transvection-list transports are units of the class group. -/
theorem codeScalar_transvecList_unit_mem
    (D : BinaryPrefixCode ι) (hD : L.IsComplete D) :
    ∀ Lt : List (Matrix.TransvectionStruct ι k), ∃ u : Aˣ,
      (u : A) = L.codeScalar (k := k) D
        ((Lt.map Matrix.TransvectionStruct.toMatrix).prod) ∧
      u ∈ stableUnits A := by
  intro Lt
  induction Lt with
  | nil =>
      refine ⟨1, ?_, one_mem _⟩
      rw [Units.val_one, List.map_nil, List.prod_nil,
        L.codeScalar_one D hD]
  | cons t ts ih =>
      obtain ⟨u', hu'val, hu'mem⟩ := ih
      have hinc : ¬D.word t.i <+: D.word t.j := D.prefix_free t.hij
      have hinc' : ¬D.word t.j <+: D.word t.i :=
        D.prefix_free (Ne.symm t.hij)
      refine ⟨L.incomparableUnit hinc hinc' (algebraMap k A t.c) * u',
        ?_, mul_mem (L.incomparableUnit_mem hinc hinc' _) hu'mem⟩
      rw [Units.val_mul, hu'val, List.map_cons, List.prod_cons,
        ← L.codeScalar_mul D,
        show Matrix.TransvectionStruct.toMatrix t =
          Matrix.transvection t.i t.j t.c from rfl]
      congr 1
      exact (L.codeScalar_transvection D hD t.hij t.c).symm

/-- **Invertible scalar matrices transport into `H` along every
complete prefix code.** -/
theorem codeScalar_unit_mem [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (D : BinaryPrefixCode ι) (hD : L.IsComplete D)
    (G : Matrix ι ι k) (hG : IsUnit G) (u : Aˣ)
    (hu : (u : A) = L.codeScalar (k := k) D G) :
    u ∈ stableUnits A := by
  classical
  obtain ⟨Lt, Lt', dvec, hdec⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec G
  -- the diagonal entries are nonzero
  have hPunit : IsUnit ((Lt.map
      Matrix.TransvectionStruct.toMatrix).prod) := by
    have h := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod Lt
    have hdet := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hdet))
  have hQunit : IsUnit ((Lt'.map
      Matrix.TransvectionStruct.toMatrix).prod) := by
    have h := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod Lt'
    have hdet := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hdet))
  have hdiagunit : IsUnit (Matrix.diagonal dvec) := by
    obtain ⟨P, hP⟩ := hPunit
    obtain ⟨Q, hQ⟩ := hQunit
    obtain ⟨Gu, hGu⟩ := hG
    refine ⟨P⁻¹ * Gu * Q⁻¹, ?_⟩
    rw [Units.val_mul, Units.val_mul, hGu, hdec, ← hP, ← hQ]
    calc ((P⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k) *
          ((P : Matrix ι ι k) * Matrix.diagonal dvec *
            (Q : Matrix ι ι k)) *
          ((Q⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k)
        = (((P⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k) *
            (P : Matrix ι ι k)) * Matrix.diagonal dvec *
          ((Q : Matrix ι ι k) *
            ((Q⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k)) := by
          noncomm_ring
      _ = Matrix.diagonal dvec := by
          rw [Units.inv_mul, Units.mul_inv, one_mul, mul_one]
  have hdvec : ∀ i, dvec i ≠ 0 := by
    intro i hzero
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hdiagunit
    rw [Matrix.det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ i) hzero] at hdet
    exact not_isUnit_zero hdet
  obtain ⟨uP, hPval, hPmem⟩ := L.codeScalar_transvecList_unit_mem
    (k := k) D hD Lt
  obtain ⟨uQ, hQval, hQmem⟩ := L.codeScalar_transvecList_unit_mem
    (k := k) D hD Lt'
  have hGval : (u : A) = (uP : A) *
      L.codeScalar (k := k) D (Matrix.diagonal dvec) * (uQ : A) := by
    rw [hu, hdec, ← L.codeScalar_mul D, ← L.codeScalar_mul D, hPval,
      hQval]
  have hDval : ((uP⁻¹ * u * uQ⁻¹ : Aˣ) : A) =
      L.codeScalar (k := k) D (Matrix.diagonal dvec) := by
    rw [Units.val_mul, Units.val_mul, hGval]
    calc ((uP⁻¹ : Aˣ) : A) * ((uP : A) *
          L.codeScalar (k := k) D (Matrix.diagonal dvec) * (uQ : A)) *
          ((uQ⁻¹ : Aˣ) : A)
        = (((uP⁻¹ : Aˣ) : A) * (uP : A)) *
          L.codeScalar (k := k) D (Matrix.diagonal dvec) *
          ((uQ : A) * ((uQ⁻¹ : Aˣ) : A)) := by noncomm_ring
      _ = L.codeScalar (k := k) D (Matrix.diagonal dvec) := by
          rw [Units.inv_mul, Units.mul_inv, one_mul, mul_one]
  have hDmem := L.codeScalar_diagonal_unit_mem hdiv D hD dvec hdvec
    (uP⁻¹ * u * uQ⁻¹) hDval
  have hufact : u = uP * (uP⁻¹ * u * uQ⁻¹) * uQ := by group
  rw [hufact]
  exact mul_mem (mul_mem hPmem hDmem) hQmem

end LeavittFamily
end NonsoficGroupsExist
