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

/-- The two-slot diagonal unit `diag(u, v)`. -/
def diagPair (u v : Rˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![(u : R), 0; 0, (v : R)]
  inv := !![((u⁻¹ : Rˣ) : R), 0; 0, ((v⁻¹ : Rˣ) : R)]
  val_inv := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem diagPair_mul (u v u' v' : Rˣ) :
    diagPair u v * diagPair u' v' = diagPair (u * u') (v * v') := by
  apply Units.ext
  show !![(u : R), 0; 0, (v : R)] * !![(u' : R), 0; 0, (v' : R)] = _
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagPair_inv (u v : Rˣ) :
    (diagPair u v)⁻¹ = diagPair u⁻¹ v⁻¹ := by
  apply Units.ext
  rfl

theorem diagUnit_eq_diagPair (u : Rˣ) : diagUnit u = diagPair u 1 := by
  apply Units.ext
  show !![(u : R), 0; 0, 1] = !![(u : R), 0; 0, ((1 : Rˣ) : R)]
  rw [Units.val_one]

/-- The Whitehead lemma, as a membership of the two-slot diagonal
unit. -/
theorem diagPair_inv_self_mem (u : Rˣ) :
    diagPair u u⁻¹ ∈ elementaryGroup (Fin 2) R := by
  obtain ⟨E, hE, hval⟩ := exists_elementary_whitehead u
  have hEeq : E = diagPair u u⁻¹ := by
    apply Units.ext
    rw [hval]
    rfl
  rwa [hEeq] at hE

/-- **`K₁`-abelianity at the diagonal**: exchanging the factors of a
product of units moves the diagonal class by an elementary matrix, by
three applications of the Whitehead lemma. -/
theorem diagUnit_mul_swap_inv_mem (u v : Rˣ) :
    diagUnit (u * v) * (diagUnit (v * u))⁻¹ ∈
      elementaryGroup (Fin 2) R := by
  have hkey : diagUnit (u * v) * (diagUnit (v * u))⁻¹ =
      diagPair u u⁻¹ * diagPair v v⁻¹ *
        (diagPair (v * u) (v * u)⁻¹)⁻¹ := by
    rw [diagUnit_eq_diagPair (u * v), diagUnit_eq_diagPair (v * u),
      diagPair_inv, diagPair_inv, diagPair_mul, diagPair_mul,
      diagPair_mul]
    congr 1
    · group
    · group
  rw [hkey]
  exact mul_mem (mul_mem (diagPair_inv_self_mem u)
    (diagPair_inv_self_mem v)) (inv_mem (diagPair_inv_self_mem (v * u)))

/-- Commutators of units have elementary diagonal stabilization. -/
theorem diagUnit_commutator_mem (u v : Rˣ) :
    diagUnit ⁅u, v⁆ ∈ elementaryGroup (Fin 2) R := by
  have hcomm : ⁅u, v⁆ = (u * v) * (v * u)⁻¹ := by
    rw [commutatorElement_def]
    group
  have hsplit : diagUnit ((u * v) * (v * u)⁻¹) =
      diagUnit (u * v) * (diagUnit (v * u))⁻¹ := by
    rw [diagUnit_mul]
    congr 1
    exact map_inv diagUnitHom (v * u)
  rw [hcomm, hsplit]
  exact diagUnit_mul_swap_inv_mem u v

/-- The commutator subgroup of the units lies in the diagonal class
group: the quotient by the diagonal class is abelian. -/
theorem commutator_mem_stableUnits (u v : Rˣ) :
    ⁅u, v⁆ ∈ stableUnits R :=
  diagUnit_commutator_mem u v

/-- **`GL₂ / EL₂` is abelian under strong division**: Gaussian
elimination reduces every class to a diagonal one, and diagonal classes
commute by `K₁`-abelianity. -/
theorem commutator_mem_elementaryGroup_of_division [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (X Y : (Matrix (Fin 2) (Fin 2) R)ˣ) :
    ⁅X, Y⁆ ∈ elementaryGroup (Fin 2) R := by
  haveI hN : (elementaryGroup (Fin 2) R).Normal :=
    elementaryGroup_normal_of_division hdiv
  have hdiag : ∀ Z : (Matrix (Fin 2) (Fin 2) R)ˣ, ∃ d : Rˣ,
      (Z : (Matrix (Fin 2) (Fin 2) R)ˣ ⧸ elementaryGroup (Fin 2) R) =
        ((diagUnit d : (Matrix (Fin 2) (Fin 2) R)ˣ) :
          (Matrix (Fin 2) (Fin 2) R)ˣ ⧸ elementaryGroup (Fin 2) R) := by
    intro Z
    obtain ⟨E, F, d, hE, hF, hEZF⟩ := exists_elementary_mul_diag hdiv Z
    refine ⟨d, ?_⟩
    have hZ : Z = E⁻¹ * diagUnit d * F⁻¹ := by
      rw [← hEZF]
      group
    rw [hZ]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr (inv_mem hE),
      (QuotientGroup.eq_one_iff _).mpr (inv_mem hF), one_mul, mul_one]
  have hcomm : ∀ a b : (Matrix (Fin 2) (Fin 2) R)ˣ ⧸
      elementaryGroup (Fin 2) R, a * b = b * a := by
    intro a b
    obtain ⟨X', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨Y', rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨x, hx⟩ := hdiag X'
    obtain ⟨y, hy⟩ := hdiag Y'
    rw [hx, hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    apply QuotientGroup.eq.mpr
    have hmem := diagUnit_mul_swap_inv_mem y x
    have hconj := hN.conj_mem _ hmem (diagUnit (x * y))⁻¹
    have hprod : (diagUnit x * diagUnit y)⁻¹ *
        (diagUnit y * diagUnit x) =
        (diagUnit (x * y))⁻¹ *
          (diagUnit (y * x) * (diagUnit (x * y))⁻¹) *
          ((diagUnit (x * y))⁻¹)⁻¹ := by
      rw [← diagUnit_mul, ← diagUnit_mul]
      group
    rw [hprod]
    exact hconj
  have hone : ((⁅X, Y⁆ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      (Matrix (Fin 2) (Fin 2) R)ˣ ⧸ elementaryGroup (Fin 2) R) = 1 := by
    rw [show ((⁅X, Y⁆ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
        (Matrix (Fin 2) (Fin 2) R)ˣ ⧸ elementaryGroup (Fin 2) R) =
      ⁅((X : (Matrix (Fin 2) (Fin 2) R)ˣ) : _ ⧸ _),
        ((Y : (Matrix (Fin 2) (Fin 2) R)ˣ) : _ ⧸ _)⁆ from
      map_commutatorElement (QuotientGroup.mk' _) X Y]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
  exact (QuotientGroup.eq_one_iff _).mp hone

end MatrixDiagonalization
end NonsoficGroupsExist
