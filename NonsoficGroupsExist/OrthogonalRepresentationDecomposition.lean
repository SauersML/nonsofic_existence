import NonsoficGroupsExist.FiniteClassTwoOrthogonality
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.RepresentationTheory.Maschke

/-!
# Orthogonal decomposition of finite-group representations

Finite-dimensional real orthogonal representations of finite groups split
orthogonally into irreducible invariant summands.  This file develops the
dimension-induction interface needed by the class-two averaging estimate.
-/

namespace NonsoficGroupsExist

open scoped MonoidAlgebra

universe u v

namespace OrthogonalRepresentationDecomposition

variable {G : Type u} [Group G] [Finite G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The underlying linear representation of an orthogonal representation. -/
def linearRepresentation (rho : G →* (E ≃ₗᵢ[ℝ] E)) :
    Representation ℝ G E where
  toFun g := (rho g).toLinearEquiv.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

omit [Finite G] in
@[simp] theorem linearRepresentation_apply
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : E) :
    linearRepresentation rho g x = rho g x := rfl

/-- A nonzero orthogonal representation of a finite group contains an
irreducible invariant subspace. -/
theorem exists_irreducible_subrepresentation
    [Nontrivial E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) :
    ∃ U : Subrepresentation (linearRepresentation rho), IsAtom U := by
  let rhoLin := linearRepresentation rho
  letI : Nontrivial rhoLin.asModule := rhoLin.asModuleEquiv.toEquiv.nontrivial
  letI : IsSemisimpleModule ℝ[G] rhoLin.asModule := inferInstance
  obtain ⟨N, hN⟩ :=
    IsSemisimpleModule.exists_simple_submodule ℝ[G] rhoLin.asModule
  let U : Subrepresentation rhoLin := Subrepresentation.ofSubmodule' N
  refine ⟨U, ?_⟩
  have hAtomN : IsAtom N := isSimpleModule_iff_isAtom.mp hN
  have hmapped :
      (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := rhoLin)) U = N := rfl
  rw [← hmapped] at hAtomN
  exact ((Subrepresentation.subrepresentationSubmoduleOrderIso
    (ρ := rhoLin)).isAtom_iff U).mp hAtomN

/-- Restriction of the orthogonal action to an invariant
subrepresentation. -/
noncomputable def representationOn
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho)) :
    G →* (U.toSubmodule ≃ₗᵢ[ℝ] U.toSubmodule) :=
  KazhdanFixedSpace.restrictToInvariantSubspace rho U.toSubmodule
    fun g _ hz ↦ U.apply_mem_toSubmodule g hz

omit [Finite G] in
@[simp] theorem representationOn_apply
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho)) (g : G)
    (z : U.toSubmodule) :
    ((representationOn rho U g z : U.toSubmodule) : E) = rho g z.1 := rfl

omit [Finite G] in
/-- An atomic invariant subspace is irreducible for the restricted
orthogonal representation. -/
theorem representationOn_irreducible
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho)) (hU : IsAtom U) :
    FiniteClassTwoOrthogonality.IsOrthogonallyIrreducible
      (representationOn rho U) := by
  constructor
  · have hne : U.toSubmodule ≠ ⊥ := by
      intro h
      apply hU.ne_bot
      apply Subrepresentation.toSubmodule_injective
      change U.toSubmodule = (⊥ : Submodule ℝ E)
      exact h
    exact U.toSubmodule.nontrivial_iff_ne_bot.mpr hne
  · intro W hWinv
    let V : Subrepresentation (linearRepresentation rho) := {
      toSubmodule := W.map U.toSubmodule.subtype
      apply_mem_toSubmodule g z hz := by
        obtain ⟨w, hw, rfl⟩ := hz
        refine ⟨representationOn rho U g w, hWinv g w hw, ?_⟩
        rfl }
    have hVU : V ≤ U := by
      intro z hz
      obtain ⟨w, _hw, rfl⟩ := hz
      exact w.2
    rcases hU.le_iff.mp hVU with hVbot | hVUeq
    · left
      apply Submodule.map_injective_of_injective U.toSubmodule.subtype_injective
      have hsub := congrArg Subrepresentation.toSubmodule hVbot
      change W.map U.toSubmodule.subtype = (⊥ : Submodule ℝ E) at hsub
      simpa using hsub
    · right
      apply Submodule.map_injective_of_injective U.toSubmodule.subtype_injective
      have hsub := congrArg Subrepresentation.toSubmodule hVUeq
      simpa [V] using hsub

omit [Finite G] in
/-- The orthogonal complement of an invariant subspace is invariant under
an orthogonal group action. -/
theorem map_mem_orthogonal
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho))
    (g : G) {z : E} (hz : z ∈ U.toSubmoduleᗮ) :
    rho g z ∈ U.toSubmoduleᗮ := by
  rw [Submodule.mem_orthogonal'] at hz ⊢
  intro u hu
  have huInv : rho g⁻¹ u ∈ U.toSubmodule :=
    U.apply_mem_toSubmodule g⁻¹ hu
  have hinner := (rho g).inner_map_map z (rho g⁻¹ u)
  simpa using hinner.trans (hz _ huInv)

omit [Finite G] in
/-- The invariant orthogonal-complement subrepresentation. -/
@[reducible] noncomputable def orthogonalComplement
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho)) :
    Subrepresentation (linearRepresentation rho) where
  toSubmodule := U.toSubmoduleᗮ
  apply_mem_toSubmodule g _ hz := map_mem_orthogonal rho U g hz

omit [Finite G] in
/-- An invariant subspace is carried onto itself, not merely into itself. -/
theorem map_toSubmodule_eq
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho)) (g : G) :
    U.toSubmodule.map (rho g).toLinearIsometry.toLinearMap = U.toSubmodule := by
  apply le_antisymm
  · rintro z ⟨u, hu, rfl⟩
    exact U.apply_mem_toSubmodule g hu
  · intro u hu
    refine ⟨rho g⁻¹ u, U.apply_mem_toSubmodule g⁻¹ hu, ?_⟩
    simp

omit [Finite G] in
/-- Orthogonal projection onto an invariant subspace commutes with the
group action. -/
theorem starProjection_equivariant
    [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho)) (g : G) (z : E) :
    rho g (U.toSubmodule.starProjection z) =
      U.toSubmodule.starProjection (rho g z) := by
  have h := (rho g).toLinearIsometry.map_starProjection U.toSubmodule z
  simp only [map_toSubmodule_eq rho U g] at h
  exact h

omit [Finite G] in
/-- The invariant-subspace component of a fixed vector remains fixed in
the restricted representation. -/
theorem orthogonalProjection_mem_fixedSubspace
    [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho))
    (Y : Subgroup G) {z : E}
    (hz : z ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    U.toSubmodule.orthogonalProjectionOnto z ∈
      KazhdanFixedSpace.fixedSubspace (representationOn rho U) Y := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
  intro y hy
  apply Subtype.ext
  change rho y (U.toSubmodule.starProjection z) =
    U.toSubmodule.starProjection z
  rw [starProjection_equivariant rho U]
  rw [(KazhdanFixedSpace.mem_fixedSubspace_iff rho Y z).mp hz y hy]

omit [Finite G] in
/-- The orthogonal-complement component of a fixed vector remains fixed in
the restricted representation. -/
theorem orthogonalComplementComponent_mem_fixedSubspace
    [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho))
    (Y : Subgroup G) {z : E}
    (hz : z ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    (⟨z - U.toSubmodule.starProjection z,
      U.toSubmodule.sub_starProjection_mem_orthogonal z⟩ : U.toSubmoduleᗮ) ∈
      KazhdanFixedSpace.fixedSubspace
        (representationOn rho (orthogonalComplement rho U)) Y := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
  intro y hy
  apply Subtype.ext
  change rho y (z - U.toSubmodule.starProjection z) =
    z - U.toSubmodule.starProjection z
  rw [map_sub, starProjection_equivariant rho U]
  rw [(KazhdanFixedSpace.mem_fixedSubspace_iff rho Y z).mp hz y hy]

omit [Finite G] in
/-- Restriction to an invariant subrepresentation preserves the absence of
invariant vectors. -/
theorem representationOn_hasNoInvariantVectors
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho))
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho) :
    IsKazhdanPair.HasNoInvariantVectors G (representationOn rho U) := by
  intro z hz
  apply Subtype.ext
  apply hno z.1
  intro g
  exact congrArg Subtype.val (hz g)

/-- Orbit averaging is additive in the averaged vector. -/
theorem orbitAverage_add {H : Type u} [Group H] [Finite H]
    (rho : H →* (E ≃ₗᵢ[ℝ] E)) (x y : E) :
    FiniteGroupAverage.orbitAverage rho (x + y) =
      FiniteGroupAverage.orbitAverage rho x +
        FiniteGroupAverage.orbitAverage rho y := by
  letI := Fintype.ofFinite H
  unfold FiniteGroupAverage.orbitAverage
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact map_add (rho g) x y

omit [Finite G] in
/-- The orbit average computed inside an invariant subspace is the ambient
orbit average of the included vector. -/
theorem coe_orbitAverage_representationOn
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (U : Subrepresentation (linearRepresentation rho))
    (X : Subgroup G) [Finite X] (z : U.toSubmodule) :
    ((FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation (representationOn rho U) X)
        z : U.toSubmodule) : E) =
      FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) (z : E) := by
  letI := Fintype.ofFinite X
  unfold FiniteGroupAverage.orbitAverage
  rw [Submodule.coe_smul, AddSubmonoidClass.coe_finsetSum]
  rfl

/-- The squared-norm half bound for every finite-dimensional orthogonal
representation, by strong induction on the dimension: split off one
irreducible invariant subspace, apply the irreducible finite-order estimate
there, recurse on the invariant orthogonal complement, and recombine by
Pythagoras. -/
theorem norm_orbitAverage_sq_le_half_of_finrank_le
    (X Y C : Subgroup G) [Finite X]
    (n : ℕ) (hn : 0 < n)
    (hgen : X ⊔ Y = ⊤) (hcomm : ⁅Y, X⁆ ≤ C)
    (hcentral : C ≤ Subgroup.center G) (hexp : ∀ c ∈ C, c ^ n = 1) :
    ∀ (k : ℕ) {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F], Module.finrank ℝ F ≤ k →
      ∀ (rho : G →* (F ≃ₗᵢ[ℝ] F)),
        IsKazhdanPair.HasNoInvariantVectors G rho →
        ∀ v ∈ KazhdanFixedSpace.fixedSubspace rho Y,
          ‖FiniteGroupAverage.orbitAverage
              (KazhdanFixedSpace.restrictRepresentation rho X) v‖ ^ 2 ≤
            (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
  intro k
  induction k with
  | zero =>
      intro F _ _ _ hrank rho hno v hv
      have hzero : ∀ x : F, x = 0 :=
        finrank_zero_iff_forall_zero.mp (Nat.le_zero.mp hrank)
      rw [hzero (FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) v), hzero v,
        norm_zero]
      norm_num
  | succ k ih =>
      intro F _ _ _ hrank rho hno v hv
      by_cases hsmall : Module.finrank ℝ F ≤ k
      · exact ih hsmall rho hno v hv
      letI : Nontrivial F :=
        Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
      obtain ⟨U, hU⟩ := exists_irreducible_subrepresentation rho
      let U' := orthogonalComplement rho U
      let vU : U.toSubmodule := U.toSubmodule.orthogonalProjectionOnto v
      let vPerp : U.toSubmoduleᗮ :=
        ⟨v - U.toSubmodule.starProjection v,
          U.toSubmodule.sub_starProjection_mem_orthogonal v⟩
      have hvsum : (vU : F) + (vPerp : F) = v := by
        change U.toSubmodule.starProjection v +
          (v - U.toSubmodule.starProjection v) = v
        abel
      have hpyth : ∀ (a : U.toSubmodule) (b : U.toSubmoduleᗮ),
          ‖(a : F) + (b : F)‖ ^ 2 = ‖(a : F)‖ ^ 2 + ‖(b : F)‖ ^ 2 := by
        intro a b
        have hinner : inner ℝ (a : F) (b : F) = 0 :=
          (Submodule.mem_orthogonal U.toSubmodule (b : F)).mp b.2 (a : F) a.2
        rw [norm_add_sq_real, hinner]
        ring
      have hvUfix : vU ∈ KazhdanFixedSpace.fixedSubspace
          (representationOn rho U) Y :=
        orthogonalProjection_mem_fixedSubspace rho U Y hv
      have hvPerpfix : vPerp ∈ KazhdanFixedSpace.fixedSubspace
          (representationOn rho U') Y :=
        orthogonalComplementComponent_mem_fixedSubspace rho U Y hv
      have hUbound :=
        FiniteClassTwoOrthogonality.norm_orbitAverage_sq_le_half_of_irreducible_finiteOrder
          (representationOn rho U) X Y C n hn hgen hcomm hcentral hexp
          (representationOn_irreducible rho U hU)
          (representationOn_hasNoInvariantVectors rho U hno) hvUfix
      have hne : U.toSubmodule ≠ ⊥ := by
        intro h
        apply hU.ne_bot
        apply Subrepresentation.toSubmodule_injective
        change U.toSubmodule = (⊥ : Submodule ℝ F)
        exact h
      have hrankPerp : Module.finrank ℝ U.toSubmoduleᗮ ≤ k := by
        have hsum := U.toSubmodule.finrank_add_finrank_orthogonal
        have hUpos : 0 < Module.finrank ℝ U.toSubmodule := by
          letI : Nontrivial U.toSubmodule :=
            U.toSubmodule.nontrivial_iff_ne_bot.mpr hne
          exact Module.finrank_pos
        omega
      have hPerpBound := ih hrankPerp (representationOn rho U')
        (representationOn_hasNoInvariantVectors rho U' hno) vPerp hvPerpfix
      let wU := FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation (representationOn rho U) X)
        vU
      let wPerp := FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation (representationOn rho U') X)
        vPerp
      have hwsum : (wU : F) + (wPerp : F) =
          FiniteGroupAverage.orbitAverage
            (KazhdanFixedSpace.restrictRepresentation rho X) v := by
        rw [show ((wU : U.toSubmodule) : F) =
            FiniteGroupAverage.orbitAverage
              (KazhdanFixedSpace.restrictRepresentation rho X) (vU : F) from
            coe_orbitAverage_representationOn rho U X vU,
          show ((wPerp : U'.toSubmodule) : F) =
            FiniteGroupAverage.orbitAverage
              (KazhdanFixedSpace.restrictRepresentation rho X)
              ((vPerp : U'.toSubmodule) : F) from
            coe_orbitAverage_representationOn rho U' X vPerp,
          ← orbitAverage_add, hvsum]
      calc
        ‖FiniteGroupAverage.orbitAverage
            (KazhdanFixedSpace.restrictRepresentation rho X) v‖ ^ 2 =
            ‖(wU : F)‖ ^ 2 + ‖(wPerp : F)‖ ^ 2 := by
          rw [← hwsum]
          exact hpyth wU wPerp
        _ ≤ (1 / 2 : ℝ) * ‖(vU : F)‖ ^ 2 +
            (1 / 2 : ℝ) * ‖(vPerp : F)‖ ^ 2 := add_le_add hUbound hPerpBound
        _ = (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
          rw [← hvsum, hpyth vU vPerp]
          ring

/-- The finite-dimensional squared-norm half estimate for class-two groups
whose central commutators have one positive bounded exponent.  This replaces
the characteristic-two sign-eigenspace recombination. -/
theorem norm_orbitAverage_sq_le_half_boundedExponent
    [FiniteDimensional ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y C : Subgroup G) [Finite X]
    (n : ℕ) (hn : 0 < n)
    (hgen : X ⊔ Y = ⊤) (hcomm : ⁅Y, X⁆ ≤ C)
    (hcentral : C ≤ Subgroup.center G) (hexp : ∀ c ∈ C, c ^ n = 1)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    {v : E} (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    ‖FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) v‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
  norm_orbitAverage_sq_le_half_of_finrank_le X Y C n hn hgen hcomm hcentral
    hexp (Module.finrank ℝ E) le_rfl rho hno v hvY

end OrthogonalRepresentationDecomposition
end NonsoficGroupsExist
