import NonsoficGroupsExist.Leavitt.Leavitt
import NonsoficGroupsExist.Leavitt.MatrixSelfSimilarity
import Mathlib.RingTheory.Idempotents

/-!
# A unital binary Leavitt family in a corner of every `d`-ary Leavitt ring

Section 9 of the compression dossier: if a ring `A` carries a `d`-ary Leavitt
family `(sᵢ, tᵢ)`, `i < d`, with `d ≥ 2` — packaged here as a
`CompleteMatrixFamily A (Fin (n + 2))` with `d = n + 2` — then the idempotent

  `e = p₀ + ⋯ + p_{d-2}`,   `pᵢ = sᵢtᵢ`,

is nonzero whenever `A` is, and its corner `eAe` contains a **unital binary
Leavitt family**.  The dossier's leaf calculus collapses to closed forms: with
`f = e - p₀` the four corner elements are

  `S₀ = s₀e`,   `T₀ = et₀`,
  `S₁ = s₀·s_{d-1}·t₀ + f`,   `T₁ = s₀·t_{d-1}·t₀ + f`,

and the five binary relations follow from the orthogonality relations, the
completeness relation `e + p_{d-1} = 1`, and nothing else.  For `d > 2` no
unital binary family can exist in `A` itself (it would force `[1] = 0` in
`K₀`), so passing to the corner is not a convenience but the sharp form of
the statement.

The corner is `Mathlib`'s `IsIdempotentElem.Corner`, a ring with unit `e`.
The file also provides the unit-group extension `u ↦ u + (1 - e)` embedding
the corner units into the ambient units, which later transports the nonsofic
subgroup of the corner construction into `Aˣ`.
-/

namespace NonsoficGroupsExist

section CornerRing

variable {A : Type*} [Ring A] {e : A} (idem : IsIdempotentElem e)

include idem in
/-- Build a corner element from the two absorption equations. -/
theorem mem_corner_of {x : A} (hl : e * x = x) (hr : x * e = x) :
    x ∈ Subsemigroup.corner e :=
  (Subsemigroup.mem_corner_iff idem).mpr ⟨hl, hr⟩

@[simp] theorem corner_val_mul (x y : idem.Corner) :
    (x * y).val = x.val * y.val := rfl

@[simp] theorem corner_val_add (x y : idem.Corner) :
    (x + y).val = x.val + y.val := rfl

@[simp] theorem corner_val_one : (1 : idem.Corner).val = e := rfl

@[simp] theorem corner_val_zero : (0 : idem.Corner).val = 0 := rfl

/-- The unit of the corner absorbs on the left. -/
theorem corner_one_mul_val (x : idem.Corner) : e * x.val = x.val :=
  ((Subsemigroup.mem_corner_iff idem).mp x.property).1

/-- The unit of the corner absorbs on the right. -/
theorem corner_val_mul_one (x : idem.Corner) : x.val * e = x.val :=
  ((Subsemigroup.mem_corner_iff idem).mp x.property).2

/-- The corner of a nonzero idempotent is a nontrivial ring. -/
theorem corner_nontrivial (he : e ≠ 0) : Nontrivial idem.Corner :=
  ⟨⟨1, 0, fun h => he (by simpa using congrArg Subtype.val h)⟩⟩

/-- Multiplication rule for the corner extension `x ↦ x + (1 - e)`. -/
theorem corner_extend_mul (x y : idem.Corner) :
    (x.val + (1 - e)) * (y.val + (1 - e)) = (x * y).val + (1 - e) := by
  have h1 : x.val * (1 - e) = 0 := by
    rw [mul_sub, mul_one, corner_val_mul_one, sub_self]
  have h2 : (1 - e) * y.val = 0 := by
    rw [sub_mul, one_mul, corner_one_mul_val, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [mul_sub, mul_one, sub_mul, one_mul, idem.eq]
    abel
  calc (x.val + (1 - e)) * (y.val + (1 - e))
      = x.val * y.val + x.val * (1 - e) +
          ((1 - e) * y.val + (1 - e) * (1 - e)) := by
        rw [add_mul, mul_add, mul_add]
    _ = (x * y).val + (1 - e) := by
        rw [h1, h2, h3, corner_val_mul, add_zero, zero_add]

/-- Corner units extend to ambient units by adding the complementary
idempotent: `u ↦ u + (1 - e)`. -/
def cornerUnitsExtend : (idem.Corner)ˣ →* Aˣ where
  toFun u :=
    { val := u.val.val + (1 - e)
      inv := u.inv.val + (1 - e)
      val_inv := by
        rw [corner_extend_mul, u.val_inv, corner_val_one]
        abel
      inv_val := by
        rw [corner_extend_mul, u.inv_val, corner_val_one]
        abel }
  map_one' := by
    ext
    show (1 : idem.Corner).val + (1 - e) = 1
    rw [corner_val_one]
    abel
  map_mul' u v := by
    ext
    exact (corner_extend_mul idem u.val v.val).symm

@[simp] theorem cornerUnitsExtend_apply_val (u : (idem.Corner)ˣ) :
    (cornerUnitsExtend idem u).val = u.val.val + (1 - e) := rfl

theorem cornerUnitsExtend_injective :
    Function.Injective (cornerUnitsExtend idem) := by
  intro u v h
  have hval : u.val.val + (1 - e) = v.val.val + (1 - e) := by
    simpa using congrArg Units.val h
  exact Units.ext (Subtype.ext (add_right_cancel hval))

end CornerRing

namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {n : ℕ} (F : CompleteMatrixFamily A (Fin (n + 2)))

/-- The dossier §9 corner idempotent `e = p₀ + ⋯ + p_{d-2}`: the sum of the
range projections of all branches except the last. -/
def cornerIdem : A := ∑ j : Fin (n + 1), F.left j.castSucc * F.right j.castSucc

@[simp] theorem cornerIdem_def :
    F.cornerIdem = ∑ j : Fin (n + 1), F.left j.castSucc * F.right j.castSucc :=
  rfl

/-- `e` absorbs every non-last branch on the left. -/
theorem cornerIdem_mul_left (j : Fin (n + 1)) :
    F.cornerIdem * F.left j.castSucc = F.left j.castSucc := by
  rw [cornerIdem_def, Finset.sum_mul]
  have h : ∀ k : Fin (n + 1),
      F.left k.castSucc * F.right k.castSucc * F.left j.castSucc
        = if k = j then F.left j.castSucc else 0 := by
    intro k
    rw [mul_assoc, F.orthogonal]
    simp only [Fin.castSucc_inj, mul_ite, mul_one, mul_zero]
    split_ifs with hkj
    · rw [hkj]
    · rfl
  simp [h]

/-- Every non-last branch absorbs `e` on the right. -/
theorem right_mul_cornerIdem (j : Fin (n + 1)) :
    F.right j.castSucc * F.cornerIdem = F.right j.castSucc := by
  rw [cornerIdem_def, Finset.mul_sum]
  have h : ∀ k : Fin (n + 1),
      F.right j.castSucc * (F.left k.castSucc * F.right k.castSucc)
        = if j = k then F.right j.castSucc else 0 := by
    intro k
    rw [← mul_assoc, F.orthogonal]
    simp only [Fin.castSucc_inj, ite_mul, one_mul, zero_mul]
    split_ifs with hjk
    · rw [hjk]
    · rfl
  simp [h]

/-- `e` kills the last branch on the left. -/
theorem cornerIdem_mul_left_last :
    F.cornerIdem * F.left (Fin.last (n + 1)) = 0 := by
  rw [cornerIdem_def, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [mul_assoc, F.orthogonal, if_neg (Fin.castSucc_lt_last k).ne, mul_zero]

/-- The last branch kills `e` on the right. -/
theorem right_last_mul_cornerIdem :
    F.right (Fin.last (n + 1)) * F.cornerIdem = 0 := by
  rw [cornerIdem_def, Finset.mul_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [← mul_assoc, F.orthogonal, if_neg (Fin.castSucc_lt_last k).ne', zero_mul]

theorem isIdempotentElem_cornerIdem : IsIdempotentElem F.cornerIdem := by
  show F.cornerIdem * F.cornerIdem = F.cornerIdem
  nth_rewrite 2 [cornerIdem_def]
  rw [Finset.mul_sum]
  calc ∑ j : Fin (n + 1),
        F.cornerIdem * (F.left j.castSucc * F.right j.castSucc)
      = ∑ j : Fin (n + 1), F.left j.castSucc * F.right j.castSucc :=
        Finset.sum_congr rfl fun j _ => by
          rw [← mul_assoc, cornerIdem_mul_left]
    _ = F.cornerIdem := (F.cornerIdem_def).symm

/-- The completeness relation split at the last branch: `e + p_{d-1} = 1`. -/
theorem cornerIdem_add_last :
    F.cornerIdem + F.left (Fin.last (n + 1)) * F.right (Fin.last (n + 1)) = 1 := by
  rw [cornerIdem_def,
    ← Fin.sum_univ_castSucc (f := fun i : Fin (n + 2) => F.left i * F.right i)]
  exact F.complete

theorem right_left_zero : F.right 0 * F.left 0 = 1 := by
  simpa using F.orthogonal 0 0

theorem right_left_last :
    F.right (Fin.last (n + 1)) * F.left (Fin.last (n + 1)) = 1 := by
  simpa using F.orthogonal (Fin.last (n + 1)) (Fin.last (n + 1))

theorem cornerIdem_mul_left_zero : F.cornerIdem * F.left 0 = F.left 0 := by
  simpa using F.cornerIdem_mul_left 0

theorem right_zero_mul_cornerIdem : F.right 0 * F.cornerIdem = F.right 0 := by
  simpa using F.right_mul_cornerIdem 0

/-- In a nontrivial ring the §9 corner idempotent is nonzero: `t₀es₀ = 1`. -/
theorem cornerIdem_ne_zero [Nontrivial A] : F.cornerIdem ≠ 0 := by
  intro h
  have h0 : F.cornerIdem * F.left 0 = F.left 0 := F.cornerIdem_mul_left_zero
  rw [h, zero_mul] at h0
  have horth : F.right 0 * F.left 0 = 1 := F.right_left_zero
  rw [← h0, mul_zero] at horth
  exact one_ne_zero horth.symm

/-- The tail `f = e - p₀` of the corner idempotent. -/
def cornerTail : A := F.cornerIdem - F.left 0 * F.right 0

@[simp] theorem cornerTail_def : F.cornerTail = F.cornerIdem - F.left 0 * F.right 0 :=
  rfl

theorem cornerTail_mul_left_zero : F.cornerTail * F.left 0 = 0 := by
  rw [cornerTail_def, sub_mul, cornerIdem_mul_left_zero, mul_assoc,
    right_left_zero, mul_one, sub_self]

theorem right_zero_mul_cornerTail : F.right 0 * F.cornerTail = 0 := by
  rw [cornerTail_def, mul_sub, right_zero_mul_cornerIdem, ← mul_assoc,
    right_left_zero, one_mul, sub_self]

theorem cornerIdem_mul_cornerTail :
    F.cornerIdem * F.cornerTail = F.cornerTail := by
  rw [cornerTail_def, mul_sub, F.isIdempotentElem_cornerIdem.eq, ← mul_assoc,
    cornerIdem_mul_left_zero]

theorem cornerTail_mul_cornerIdem :
    F.cornerTail * F.cornerIdem = F.cornerTail := by
  rw [cornerTail_def, sub_mul, F.isIdempotentElem_cornerIdem.eq, mul_assoc,
    right_zero_mul_cornerIdem]

theorem cornerTail_mul_cornerTail :
    F.cornerTail * F.cornerTail = F.cornerTail := by
  nth_rewrite 1 [cornerTail_def]
  rw [sub_mul, cornerIdem_mul_cornerTail, mul_assoc, right_zero_mul_cornerTail,
    mul_zero, sub_zero]

/-! ### The four corner elements (dossier equation (9.2), closed forms) -/

/-- `S₀ = s₀e`. -/
def cornerS0 : A := F.left 0 * F.cornerIdem

@[simp] theorem cornerS0_def : F.cornerS0 = F.left 0 * F.cornerIdem := rfl

/-- `T₀ = et₀`. -/
def cornerT0 : A := F.cornerIdem * F.right 0

@[simp] theorem cornerT0_def : F.cornerT0 = F.cornerIdem * F.right 0 := rfl

/-- `S₁ = s₀·s_{d-1}·t₀ + f`. -/
def cornerS1 : A :=
  F.left 0 * (F.left (Fin.last (n + 1)) * F.right 0) + F.cornerTail

@[simp] theorem cornerS1_def :
    F.cornerS1 =
      F.left 0 * (F.left (Fin.last (n + 1)) * F.right 0) + F.cornerTail :=
  rfl

/-- `T₁ = s₀·t_{d-1}·t₀ + f`. -/
def cornerT1 : A :=
  F.left 0 * (F.right (Fin.last (n + 1)) * F.right 0) + F.cornerTail

@[simp] theorem cornerT1_def :
    F.cornerT1 =
      F.left 0 * (F.right (Fin.last (n + 1)) * F.right 0) + F.cornerTail :=
  rfl

/-! ### Reassociated absorption lemmas

Every product below is normalized to right association by `mul_assoc`, so each
fact is stated with a trailing factor. -/

theorem right_zero_mul_left_zero_mul (x : A) :
    F.right 0 * (F.left 0 * x) = x := by
  rw [← mul_assoc, right_left_zero, one_mul]

theorem right_last_mul_left_last_mul (x : A) :
    F.right (Fin.last (n + 1)) * (F.left (Fin.last (n + 1)) * x) = x := by
  rw [← mul_assoc, right_left_last, one_mul]

theorem cornerIdem_mul_left_zero_mul (x : A) :
    F.cornerIdem * (F.left 0 * x) = F.left 0 * x := by
  rw [← mul_assoc, cornerIdem_mul_left_zero]

theorem cornerIdem_mul_left_last_mul (x : A) :
    F.cornerIdem * (F.left (Fin.last (n + 1)) * x) = 0 := by
  rw [← mul_assoc, cornerIdem_mul_left_last, zero_mul]

theorem right_zero_mul_cornerIdem_mul (x : A) :
    F.right 0 * (F.cornerIdem * x) = F.right 0 * x := by
  rw [← mul_assoc, right_zero_mul_cornerIdem]

theorem right_last_mul_cornerIdem_mul (x : A) :
    F.right (Fin.last (n + 1)) * (F.cornerIdem * x) = 0 := by
  rw [← mul_assoc, right_last_mul_cornerIdem, zero_mul]

theorem cornerIdem_mul_cornerIdem_mul (x : A) :
    F.cornerIdem * (F.cornerIdem * x) = F.cornerIdem * x := by
  rw [← mul_assoc, F.isIdempotentElem_cornerIdem.eq]

theorem cornerTail_mul_left_zero_mul (x : A) :
    F.cornerTail * (F.left 0 * x) = 0 := by
  rw [← mul_assoc, cornerTail_mul_left_zero, zero_mul]

/-! ### Corner membership of the four elements -/

theorem cornerS0_mem :
    F.cornerS0 ∈ Subsemigroup.corner F.cornerIdem := by
  refine mem_corner_of F.isIdempotentElem_cornerIdem ?_ ?_
  · rw [cornerS0_def, cornerIdem_mul_left_zero_mul]
  · rw [cornerS0_def, mul_assoc, F.isIdempotentElem_cornerIdem.eq]

theorem cornerT0_mem :
    F.cornerT0 ∈ Subsemigroup.corner F.cornerIdem := by
  refine mem_corner_of F.isIdempotentElem_cornerIdem ?_ ?_
  · rw [cornerT0_def, ← mul_assoc, F.isIdempotentElem_cornerIdem.eq]
  · rw [cornerT0_def, mul_assoc, right_zero_mul_cornerIdem]

theorem cornerS1_mem :
    F.cornerS1 ∈ Subsemigroup.corner F.cornerIdem := by
  refine mem_corner_of F.isIdempotentElem_cornerIdem ?_ ?_
  · rw [cornerS1_def, mul_add, cornerIdem_mul_left_zero_mul,
      cornerIdem_mul_cornerTail]
  · rw [cornerS1_def, add_mul, cornerTail_mul_cornerIdem, mul_assoc,
      mul_assoc, right_zero_mul_cornerIdem]

theorem cornerT1_mem :
    F.cornerT1 ∈ Subsemigroup.corner F.cornerIdem := by
  refine mem_corner_of F.isIdempotentElem_cornerIdem ?_ ?_
  · rw [cornerT1_def, mul_add, cornerIdem_mul_left_zero_mul,
      cornerIdem_mul_cornerTail]
  · rw [cornerT1_def, add_mul, cornerTail_mul_cornerIdem, mul_assoc,
      mul_assoc, right_zero_mul_cornerIdem]

/-! ### The five binary Leavitt relations, at the level of `A` -/

theorem cornerT0_mul_cornerS0 :
    F.cornerT0 * F.cornerS0 = F.cornerIdem := by
  rw [cornerT0_def, cornerS0_def, mul_assoc, right_zero_mul_left_zero_mul,
    F.isIdempotentElem_cornerIdem.eq]

theorem cornerT0_mul_cornerS1 : F.cornerT0 * F.cornerS1 = 0 := by
  rw [cornerT0_def, cornerS1_def, mul_add]
  rw [show F.cornerIdem * F.right 0 *
      (F.left 0 * (F.left (Fin.last (n + 1)) * F.right 0)) = 0 from by
    rw [mul_assoc, right_zero_mul_left_zero_mul, cornerIdem_mul_left_last_mul]]
  rw [show F.cornerIdem * F.right 0 * F.cornerTail = 0 from by
    rw [mul_assoc, right_zero_mul_cornerTail, mul_zero]]
  rw [add_zero]

theorem cornerT1_mul_cornerS0 : F.cornerT1 * F.cornerS0 = 0 := by
  rw [cornerT1_def, cornerS0_def, add_mul]
  rw [show F.left 0 * (F.right (Fin.last (n + 1)) * F.right 0) *
      (F.left 0 * F.cornerIdem) = 0 from by
    rw [mul_assoc, mul_assoc, right_zero_mul_left_zero_mul,
      right_last_mul_cornerIdem, mul_zero]]
  rw [cornerTail_mul_left_zero_mul, add_zero]

theorem cornerT1_mul_cornerS1 :
    F.cornerT1 * F.cornerS1 = F.cornerIdem := by
  rw [cornerT1_def, cornerS1_def, add_mul, mul_add, mul_add]
  rw [show F.left 0 * (F.right (Fin.last (n + 1)) * F.right 0) *
      (F.left 0 * (F.left (Fin.last (n + 1)) * F.right 0)) =
      F.left 0 * F.right 0 from by
    rw [mul_assoc, mul_assoc, right_zero_mul_left_zero_mul,
      right_last_mul_left_last_mul]]
  rw [show F.left 0 * (F.right (Fin.last (n + 1)) * F.right 0) * F.cornerTail
      = 0 from by
    rw [mul_assoc, mul_assoc, right_zero_mul_cornerTail, mul_zero, mul_zero]]
  rw [cornerTail_mul_left_zero_mul, cornerTail_mul_cornerTail, add_zero,
    zero_add, cornerTail_def]
  abel

theorem cornerS0_mul_cornerT0_add_cornerS1_mul_cornerT1 :
    F.cornerS0 * F.cornerT0 + F.cornerS1 * F.cornerT1 = F.cornerIdem := by
  rw [cornerS0_def, cornerT0_def, cornerS1_def, cornerT1_def, add_mul,
    mul_add, mul_add]
  rw [show F.left 0 * F.cornerIdem * (F.cornerIdem * F.right 0)
      = F.left 0 * (F.cornerIdem * F.right 0) from by
    rw [mul_assoc, cornerIdem_mul_cornerIdem_mul]]
  rw [show F.left 0 * (F.left (Fin.last (n + 1)) * F.right 0) *
      (F.left 0 * (F.right (Fin.last (n + 1)) * F.right 0)) =
      F.left 0 * (F.left (Fin.last (n + 1)) *
        (F.right (Fin.last (n + 1)) * F.right 0)) from by
    rw [mul_assoc, mul_assoc, right_zero_mul_left_zero_mul]]
  rw [show F.left 0 * (F.left (Fin.last (n + 1)) * F.right 0) * F.cornerTail
      = 0 from by
    rw [mul_assoc, mul_assoc, right_zero_mul_cornerTail, mul_zero, mul_zero]]
  rw [cornerTail_mul_left_zero_mul, cornerTail_mul_cornerTail, add_zero,
    zero_add, ← add_assoc, ← mul_add, ← mul_assoc, ← add_mul,
    cornerIdem_add_last, one_mul, cornerTail_def]
  abel

/-! ### The binary family in the corner ring -/

/-- **Dossier §9.**  The corner `eAe` of the idempotent
`e = p₀ + ⋯ + p_{d-2}` of any `d`-ary Leavitt family, `d ≥ 2`, carries a
unital binary Leavitt family.  For `d > 2` the corner is proper, matching the
`K₀` obstruction to a unital binary family in `A` itself. -/
def cornerBinaryFamily :
    LeavittFamily F.isIdempotentElem_cornerIdem.Corner where
  s0 := ⟨F.cornerS0, F.cornerS0_mem⟩
  s1 := ⟨F.cornerS1, F.cornerS1_mem⟩
  t0 := ⟨F.cornerT0, F.cornerT0_mem⟩
  t1 := ⟨F.cornerT1, F.cornerT1_mem⟩
  t0_s0 := Subtype.ext F.cornerT0_mul_cornerS0
  t0_s1 := Subtype.ext F.cornerT0_mul_cornerS1
  t1_s0 := Subtype.ext F.cornerT1_mul_cornerS0
  t1_s1 := Subtype.ext F.cornerT1_mul_cornerS1
  sum_range := Subtype.ext F.cornerS0_mul_cornerT0_add_cornerS1_mul_cornerT1

/-- The corner ring of the §9 idempotent is nontrivial whenever `A` is. -/
theorem cornerBinaryFamily_nontrivial [Nontrivial A] :
    Nontrivial F.isIdempotentElem_cornerIdem.Corner :=
  corner_nontrivial _ F.cornerIdem_ne_zero

end CompleteMatrixFamily
end NonsoficGroupsExist
