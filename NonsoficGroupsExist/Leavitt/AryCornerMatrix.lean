import NonsoficGroupsExist.Leavitt.AryCorner
import NonsoficGroupsExist.Leavitt.ElementaryGroup

/-!
# Corner matrices, corner algebras, and elementary transport

Three transport devices for the corner route of `AryCorner`.

* An `Algebra k` structure on the corner ring `eAe` of an idempotent in a
  `k`-algebra: scalars act by `c ↦ (algebraMap k A c) * e`, which is central
  in the corner.
* The matrix ring over a corner is the corner of the matrix ring, at the
  diagonal idempotent `diag(e,…,e)`; consequently the unit-extension
  `u ↦ u + (1 - e)` of `AryCorner` extends to matrices,
  `M ↦ M + (1 - e)·1`.
* The matrix extension carries elementary transvections over the corner to
  elementary transvections over the ambient ring — `x_{ij}(a) ↦ x_{ij}(a)`
  literally, since the corner unit `e` on the diagonal is completed to `1` —
  so every elementary group over the corner embeds into the corresponding
  elementary group over the ambient ring.

This is how nonsoficity of the elementary groups over the corner subalgebra
reaches the elementary groups of the `d`-ary ring itself, in every rank at
least two.
-/

namespace NonsoficGroupsExist

/-! ### The corner of a `k`-algebra is a `k`-algebra -/

section CornerAlgebra

variable {k : Type*} [CommSemiring k] {A : Type*} [Ring A] [Algebra k A]
variable {e : A} (idem : IsIdempotentElem e)

include idem in
theorem corner_algebraMap_absorb_left (c : k) :
    e * (algebraMap k A c * e) = algebraMap k A c * e := by
  rw [← mul_assoc, ← Algebra.commutes c e, mul_assoc, idem.eq]

include idem in
theorem corner_algebraMap_absorb_right (c : k) :
    algebraMap k A c * e * e = algebraMap k A c * e := by
  rw [mul_assoc, idem.eq]

/-- The scalar embedding `c ↦ (algebraMap k A c)·e` into the corner. -/
def cornerAlgebraMap : k →+* idem.Corner where
  toFun c := ⟨algebraMap k A c * e,
    mem_corner_of idem (corner_algebraMap_absorb_left idem c)
      (corner_algebraMap_absorb_right idem c)⟩
  map_one' := by
    apply Subtype.ext
    show algebraMap k A 1 * e = e
    rw [map_one, one_mul]
  map_mul' c c' := by
    apply Subtype.ext
    show algebraMap k A (c * c') * e =
      algebraMap k A c * e * (algebraMap k A c' * e)
    rw [mul_assoc, corner_algebraMap_absorb_left idem c', ← mul_assoc,
      ← map_mul]
  map_zero' := by
    apply Subtype.ext
    show algebraMap k A 0 * e = 0
    rw [map_zero, zero_mul]
  map_add' c c' := by
    apply Subtype.ext
    show algebraMap k A (c + c') * e =
      algebraMap k A c * e + algebraMap k A c' * e
    rw [map_add, add_mul]

/-- The corner of an idempotent in a `k`-algebra is a `k`-algebra. -/
instance cornerAlgebra : Algebra k idem.Corner :=
  (cornerAlgebraMap idem).toAlgebra' (by
    intro c x
    apply Subtype.ext
    show algebraMap k A c * e * x.val = x.val * (algebraMap k A c * e)
    rw [mul_assoc, corner_one_mul_val idem x, ← mul_assoc,
      ← Algebra.commutes c x.val, mul_assoc, corner_val_mul_one idem x])

@[simp] theorem corner_algebraMap_val (c : k) :
    (algebraMap k idem.Corner c).val = algebraMap k A c * e := rfl

end CornerAlgebra

/-! ### The matrix ring over a corner is a corner of the matrix ring -/

section MatrixCorner

variable {A : Type*} [Ring A] {e : A} (idem : IsIdempotentElem e)
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

include idem in
/-- `diag(e,…,e)` is idempotent. -/
theorem isIdempotentElem_diagonal :
    IsIdempotentElem (Matrix.diagonal (fun _ : ι => e)) := by
  show _ * _ = _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext _
  exact idem.eq

/-- The entry map of the corner, as an additive homomorphism. -/
def cornerValAddHom : idem.Corner →+ A where
  toFun := Subtype.val
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Matrices over the corner of `e` form the corner of `diag(e,…,e)` in the
matrix ring. -/
def matrixCornerEquiv :
    Matrix ι ι idem.Corner ≃+* (isIdempotentElem_diagonal idem ι).Corner where
  toFun M := ⟨M.map Subtype.val,
    mem_corner_of (isIdempotentElem_diagonal idem ι)
      (by
        ext i j
        rw [Matrix.diagonal_mul]
        exact corner_one_mul_val idem (M i j))
      (by
        ext i j
        rw [Matrix.mul_diagonal]
        exact corner_val_mul_one idem (M i j))⟩
  invFun X := Matrix.of fun i j =>
    (⟨X.val i j,
      mem_corner_of idem
        (by
          have h : (Matrix.diagonal (fun _ : ι => e) * X.val) i j =
              X.val i j := by
            rw [corner_one_mul_val (isIdempotentElem_diagonal idem ι) X]
          rwa [Matrix.diagonal_mul] at h)
        (by
          have h : (X.val * Matrix.diagonal (fun _ : ι => e)) i j =
              X.val i j := by
            rw [corner_val_mul_one (isIdempotentElem_diagonal idem ι) X]
          rwa [Matrix.mul_diagonal] at h)⟩ : idem.Corner)
  left_inv M := by
    ext i j
    exact Subtype.ext rfl
  right_inv X := by
    apply Subtype.ext
    ext i j
    rfl
  map_mul' M N := by
    apply Subtype.ext
    show (M * N).map Subtype.val = M.map Subtype.val * N.map Subtype.val
    ext i j
    rw [Matrix.map_apply, Matrix.mul_apply, Matrix.mul_apply]
    rw [show (∑ l, M i l * N l j : idem.Corner).val =
        ∑ l, (M i l * N l j : idem.Corner).val from
      map_sum (cornerValAddHom idem) _ Finset.univ]
    exact Finset.sum_congr rfl fun l _ => rfl
  map_add' M N := by
    apply Subtype.ext
    ext i j
    rfl

/-- Corner matrices extend to ambient matrices: `M ↦ M + (1 - e)·1`, on unit
groups. -/
noncomputable def cornerMatrixUnitsExtend :
    (Matrix ι ι idem.Corner)ˣ →* (Matrix ι ι A)ˣ :=
  (cornerUnitsExtend (isIdempotentElem_diagonal idem ι)).comp
    (Units.map (matrixCornerEquiv idem ι).toRingHom.toMonoidHom)

theorem cornerMatrixUnitsExtend_injective :
    Function.Injective (cornerMatrixUnitsExtend idem ι) := by
  intro x y h
  have h' := cornerUnitsExtend_injective (isIdempotentElem_diagonal idem ι) h
  exact Units.map_injective
    (fun a b hab => (matrixCornerEquiv idem ι).injective hab) h'

/-- The matrix extension carries corner transvections to ambient
transvections. -/
theorem cornerMatrixUnitsExtend_elementaryUnit (i j : ι) (hij : i ≠ j)
    (a : idem.Corner) :
    cornerMatrixUnitsExtend idem ι (elementaryUnit i j hij a) =
      elementaryUnit i j hij a.val := by
  apply Units.ext
  show (matrixCornerEquiv idem ι
        ((elementaryUnit i j hij a : (Matrix ι ι idem.Corner)ˣ) :
          Matrix ι ι idem.Corner)).val +
      (1 - Matrix.diagonal (fun _ : ι => e)) =
    (elementaryUnit i j hij a.val : (Matrix ι ι A)ˣ)
  show ((1 + Matrix.single i j a : Matrix ι ι idem.Corner).map
        Subtype.val) + (1 - Matrix.diagonal (fun _ : ι => e)) =
    (1 + Matrix.single i j a.val : Matrix ι ι A)
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply,
    Matrix.one_apply, Matrix.diagonal_apply, Matrix.single_apply,
    apply_ite (fun x : idem.Corner => x.val), corner_val_add,
    corner_val_one, corner_val_zero]
  abel

/-- The matrix extension maps the elementary group over the corner into the
elementary group over the ambient ring. -/
theorem cornerMatrixUnitsExtend_mem_elementaryGroup
    {u : (Matrix ι ι idem.Corner)ˣ} (hu : u ∈ elementaryGroup ι idem.Corner) :
    cornerMatrixUnitsExtend idem ι u ∈ elementaryGroup ι A := by
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [cornerMatrixUnitsExtend_elementaryUnit]
      exact elementaryUnit_mem i j hij a.val
  | one =>
      rw [map_one]
      exact (elementaryGroup ι A).one_mem
  | mul x y _ _ ihx ihy =>
      rw [map_mul]
      exact (elementaryGroup ι A).mul_mem ihx ihy
  | inv x _ ih =>
      rw [map_inv]
      exact (elementaryGroup ι A).inv_mem ih

/-- The elementary group over a corner embeds into the elementary group over
the ambient ring: transvections go to transvections, and the corner diagonal
is completed by the complementary idempotent. -/
noncomputable def cornerElementaryExtend :
    elementaryGroup ι idem.Corner →* elementaryGroup ι A :=
  ((cornerMatrixUnitsExtend idem ι).comp
      (elementaryGroup ι idem.Corner).subtype).codRestrict
    (elementaryGroup ι A) fun g =>
      cornerMatrixUnitsExtend_mem_elementaryGroup idem ι g.property

theorem cornerElementaryExtend_injective :
    Function.Injective (cornerElementaryExtend idem ι) := by
  intro x y h
  apply Subtype.ext
  apply cornerMatrixUnitsExtend_injective idem ι
  exact congrArg (fun z : elementaryGroup ι A => (z : (Matrix ι ι A)ˣ)) h

end MatrixCorner
end NonsoficGroupsExist
