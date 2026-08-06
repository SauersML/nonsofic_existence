import NonsoficGroupsExist.Leavitt.AryEndpoints
import NonsoficGroupsExist.Leavitt.ElementaryPerfect

/-!
# The embedded profile: finitely generated, perfect, Kazhdan, nonsofic

`AryEndpoints` proves that the unit group, every `GL_r`, and every elementary
group of rank at least two over a `d`-ary Leavitt ring are nonsofic, by
transporting subgroups out of the finite-type core of the corner.  This module
upgrades the transported subgroup itself to the full profile: each of those
ambient groups contains a subgroup that is simultaneously

* finitely generated,
* perfect (`commutator = ⊤`),
* Kazhdan (property `(T)`), and
* not sofic.

The source of the profile is `EL₄` of the finite-type core: finitely
generated because the core has finite type over the finite coefficient field,
Kazhdan by the formalized rank-three input and the rank equivalence, perfect
by the Steinberg identity (`ElementaryPerfect`), and nonsofic by the generic
rank-four pipeline.  All four properties descend along surjections, so the
range of any injective homomorphism out of `EL₄` of the core carries them —
and the transports of `AryEndpoints` are injective homomorphisms.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

/-- All four profile properties pass to the range of an injective
homomorphism: finite generation, property `(T)`, and perfectness descend
along the surjection onto the range, and nonsoficity ascends along the
injection from the source. -/
theorem exists_profile_subgroup_of_injective {G G' : Type}
    [Group G] [Group G'] (f : G →* G') (hf : Function.Injective f)
    (hFG : Group.FG G) (hT : HasKazhdanPropertyT.{0, 0} G)
    (hperf : commutator G = ⊤) (hns : ¬ IsSofic G) :
    ∃ H : Subgroup G', Group.FG H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      commutator H = ⊤ ∧ ¬ IsSofic H := by
  refine ⟨f.range, ?_, ?_, ?_, ?_⟩
  · haveI := hFG
    exact Group.fg_of_surjective (f := f.rangeRestrict)
      f.rangeRestrict_surjective
  · exact HasKazhdanPropertyT.of_surjective f.rangeRestrict
      f.rangeRestrict_surjective hT
  · exact commutator_eq_top_of_surjective f.rangeRestrict
      f.rangeRestrict_surjective hperf
  · intro hS
    refine hns (isSofic_of_injective f.rangeRestrict ?_ hS)
    intro x y hxy
    exact hf (congrArg Subtype.val hxy)

namespace CompleteMatrixFamily

variable (k : Type) [Field k] [Finite k]
variable {A : Type} [Ring A] [Algebra k A] [Countable A] [Nontrivial A]
variable {n : ℕ} (F : CompleteMatrixFamily A (Fin (n + 2)))

include k F in
/-- **The profile in the unit group.**  The unit group of any nontrivial
countable `k`-algebra with a `d`-ary Leavitt family contains a finitely
generated, perfect, Kazhdan, nonsofic subgroup: the image of `EL₄` of the
finite-type core of the corner under the four-leaf comb identification and
the two corner extensions. -/
theorem exists_profile_subgroup_units :
    ∃ H : Subgroup Aˣ, Group.FG H ∧ HasKazhdanPropertyT.{0, 0} H ∧
      commutator H = ⊤ ∧ ¬ IsSofic H := by
  classical
  haveI : Countable F.isIdempotentElem_cornerIdem.Corner :=
    inferInstanceAs
      (Countable {x : A // x ∈ Subsemigroup.corner F.cornerIdem})
  haveI : Nontrivial F.isIdempotentElem_cornerIdem.Corner :=
    F.cornerBinaryFamily_nontrivial
  haveI : Algebra.FiniteType k (F.cornerBinaryFamily.coreSubalgebra k) :=
    F.cornerBinaryFamily.coreSubalgebra_finiteType k
  haveI : Nontrivial (F.cornerBinaryFamily.coreSubalgebra k) :=
    F.cornerBinaryFamily.coreSubalgebra_nontrivial k
  -- the composite injection out of `EL₄` of the core:
  -- stabilize to `GL₄`, identify with core units by the comb code, include
  -- into corner units, extend by the complementary idempotent.
  refine exists_profile_subgroup_of_injective
    ((cornerUnitsExtend F.isIdempotentElem_cornerIdem).comp
      ((Units.map
          (F.cornerBinaryFamily.coreSubalgebra k).val.toRingHom.toMonoidHom).comp
        (((F.cornerBinaryFamily.coreFamily k).prefixUnitsEquiv
            (leftCombCode 3)
            ((F.cornerBinaryFamily.coreFamily k).leftCombCode_complete
              3)).toMonoidHom.comp
          (elementaryGroup (Fin 4)
            (F.cornerBinaryFamily.coreSubalgebra k)).subtype)))
    ?_ ?_ ?_ ?_ ?_
  · -- injectivity of the composite
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact (cornerUnitsExtend_injective F.isIdempotentElem_cornerIdem).comp
      ((Units.map_injective fun a b hab => Subtype.ext hab).comp
        ((((F.cornerBinaryFamily.coreFamily k).prefixUnitsEquiv
            (leftCombCode 3) _).injective).comp
          (Subgroup.subtype_injective _)))
  · exact FamilyRankFour.ambientFG (A := (F.cornerBinaryFamily.coreSubalgebra k)) k
  · exact FamilyRankFour.ambient_hasKazhdanPropertyT
      (F.cornerBinaryFamily.coreFamily k) k
  · exact elementaryGroup_commutator_eq_top 4 (by omega)
  · exact FamilyRankFour.ambient_not_isSofic
      (F.cornerBinaryFamily.coreFamily k) k

include k F in
/-- **The profile in every general linear group.**  Transport of the unit
profile along the scalar diagonal embedding. -/
theorem exists_profile_subgroup_gl (m : ℕ) :
    ∃ H : Subgroup ((Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ),
      Group.FG H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        commutator H = ⊤ ∧ ¬ IsSofic H := by
  obtain ⟨H, hFG, hT, hperf, hns⟩ := F.exists_profile_subgroup_units k
  refine exists_profile_subgroup_of_injective
    ((Units.map (Matrix.scalar (Fin (m + 1))).toMonoidHom).comp H.subtype)
    ?_ hFG hT hperf hns
  intro x y hxy
  exact Subtype.ext
    (Units.map_injective (fun a b hab => Matrix.scalar_inj.mp hab) hxy)

include k F in
/-- **The profile in every elementary group of rank at least two.**  The
source is `EL_{m+1}` of the finite-type core; its four properties are
transported from `EL₄` of the core through the binary rank equivalence, and
the injection into `EL_{m+1}(A)` is the elementary corner transport of
`AryEndpoints`. -/
theorem exists_profile_subgroup_elementary (m : ℕ) (hm : 0 < m) :
    ∃ H : Subgroup (elementaryGroup (Fin (m + 1)) A),
      Group.FG H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        commutator H = ⊤ ∧ ¬ IsSofic H := by
  classical
  haveI : Countable F.isIdempotentElem_cornerIdem.Corner :=
    inferInstanceAs
      (Countable {x : A // x ∈ Subsemigroup.corner F.cornerIdem})
  haveI : Nontrivial F.isIdempotentElem_cornerIdem.Corner :=
    F.cornerBinaryFamily_nontrivial
  haveI : Algebra.FiniteType k (F.cornerBinaryFamily.coreSubalgebra k) :=
    F.cornerBinaryFamily.coreSubalgebra_finiteType k
  haveI : Nontrivial (F.cornerBinaryFamily.coreSubalgebra k) :=
    F.cornerBinaryFamily.coreSubalgebra_nontrivial k
  -- the equivalence `EL_{m+1}(core) ≃* EL₄(core)` carries the four
  -- properties of the rank-four group onto the rank-`m+1` group
  have hEq := (F.cornerBinaryFamily.coreFamily k).rankSuccEquiv m 3 hm
    (by omega)
  have hFG : Group.FG
      (elementaryGroup (Fin (m + 1)) (F.cornerBinaryFamily.coreSubalgebra k)) := by
    haveI := FamilyRankFour.ambientFG
      (A := (F.cornerBinaryFamily.coreSubalgebra k)) k
    exact Group.fg_of_surjective (f := hEq.symm.toMonoidHom) hEq.symm.surjective
  have hT : HasKazhdanPropertyT.{0, 0}
      (elementaryGroup (Fin (m + 1)) (F.cornerBinaryFamily.coreSubalgebra k)) :=
    HasKazhdanPropertyT.of_surjective hEq.symm.toMonoidHom hEq.symm.surjective
      (FamilyRankFour.ambient_hasKazhdanPropertyT
        (F.cornerBinaryFamily.coreFamily k) k)
  have hperf : commutator
      (elementaryGroup (Fin (m + 1)) (F.cornerBinaryFamily.coreSubalgebra k)) = ⊤ :=
    commutator_eq_top_of_surjective hEq.symm.toMonoidHom hEq.symm.surjective
      (elementaryGroup_commutator_eq_top 4 (by omega))
  have hns : ¬ IsSofic
      (elementaryGroup (Fin (m + 1)) (F.cornerBinaryFamily.coreSubalgebra k)) :=
    FamilyRankFour.elementary_not_isSofic
      (F.cornerBinaryFamily.coreFamily k) k m hm
  -- transport into `EL_{m+1}(A)` along the two elementary injections
  refine exists_profile_subgroup_of_injective
    ((cornerElementaryExtend F.isIdempotentElem_cornerIdem
        (Fin (m + 1))).comp
      (elementaryGroupMap
        (F.cornerBinaryFamily.coreSubalgebra k).val.toRingHom))
    ?_ hFG hT hperf hns
  -- the two injections are composed by hand: `apply Function.Injective.comp`
  -- has to invert the coercion of a `MonoidHom.comp` at these types, which is
  -- what ran the elaborator out of heartbeats
  intro x y hxy
  have hxy' :
      cornerElementaryExtend F.isIdempotentElem_cornerIdem (Fin (m + 1))
          (elementaryGroupMap
            (F.cornerBinaryFamily.coreSubalgebra k).val.toRingHom x) =
        cornerElementaryExtend F.isIdempotentElem_cornerIdem (Fin (m + 1))
          (elementaryGroupMap
            (F.cornerBinaryFamily.coreSubalgebra k).val.toRingHom y) := hxy
  exact elementaryGroupMap_injective
    (F.cornerBinaryFamily.coreSubalgebra k).val.toRingHom
    (fun a b hab => Subtype.ext hab)
    (cornerElementaryExtend_injective F.isIdempotentElem_cornerIdem
      (Fin (m + 1)) hxy')

end CompleteMatrixFamily

namespace AryLeavitt

variable (k : Type) [Field k] [Finite k]

/-- The unit group of `L_k(1,d)` contains a finitely generated, perfect,
Kazhdan, nonsofic subgroup, for every finite field `k` and every `d ≥ 2`. -/
theorem aryLeavitt_units_profile (d : ℕ) (hd : 2 ≤ d) :
    ∃ H : Subgroup (AryLeavittAlgebra k d)ˣ,
      Group.FG H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        commutator H = ⊤ ∧ ¬ IsSofic H := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  haveI : NeZero (n + 2) := ⟨by omega⟩
  exact (family k (n + 2)).exists_profile_subgroup_units k

/-- Every `GL_{m+1}(L_k(1,d))` contains a finitely generated, perfect,
Kazhdan, nonsofic subgroup. -/
theorem aryLeavitt_gl_profile (d : ℕ) (hd : 2 ≤ d) (m : ℕ) :
    ∃ H : Subgroup ((Matrix (Fin (m + 1)) (Fin (m + 1))
        (AryLeavittAlgebra k d))ˣ),
      Group.FG H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        commutator H = ⊤ ∧ ¬ IsSofic H := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  haveI : NeZero (n + 2) := ⟨by omega⟩
  exact (family k (n + 2)).exists_profile_subgroup_gl k m

/-- Every `EL_{m+1}(L_k(1,d))` with `m ≥ 1` contains a finitely generated,
perfect, Kazhdan, nonsofic subgroup. -/
theorem aryLeavitt_elementary_profile (d : ℕ) (hd : 2 ≤ d) (m : ℕ)
    (hm : 0 < m) :
    ∃ H : Subgroup (elementaryGroup (Fin (m + 1)) (AryLeavittAlgebra k d)),
      Group.FG H ∧ HasKazhdanPropertyT.{0, 0} H ∧
        commutator H = ⊤ ∧ ¬ IsSofic H := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  haveI : NeZero (n + 2) := ⟨by omega⟩
  exact (family k (n + 2)).exists_profile_subgroup_elementary k m hm

end AryLeavitt
end NonsoficGroupsExist
