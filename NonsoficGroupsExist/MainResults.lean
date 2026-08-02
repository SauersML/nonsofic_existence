import NonsoficGroupsExist.CriterionAssembly
import NonsoficGroupsExist.TableCover
import NonsoficGroupsExist.ThompsonWitness

/-!
# Kernel-level statements of the existence consequences

The carrier, group law, and countability evidence are bundled so that the
headline statement does not hide any typeclass precondition.
-/

namespace NonsoficGroupsExist

/-- A countable group together with a proof that it is not sofic. -/
structure NonsoficGroupWitness where
  carrier : Type
  group : Group carrier
  countable : Countable carrier
  notSofic : @IsSofic carrier group countable → False

/-- The literal headline proposition “a nonsofic countable group exists.” -/
def NonsoficGroupExists : Prop := Nonempty NonsoficGroupWitness

/-- A compression setup with a non-LEF centralizer produces the headline
witness.  All three non-elementary inputs are ordinary theorem hypotheses. -/
theorem nonsofic_groups_exist
    (hKun : KunTheorem) (hKT : KunThomTheorem)
    (hmatch : ConservativeMatchingTheorem)
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable G] [Countable Γ]
    (C : CompressionSetup G Γ J)
    (hTG : HasKazhdanPropertyT G) (hTΓ : HasKazhdanPropertyT Γ)
    (hJ : ¬ IsLEF J) : NonsoficGroupExists := by
  let W : NonsoficGroupWitness :=
    { carrier := G
      group := inferInstance
      countable := inferInstance
      notSofic := not_isSofic_of_kazhdan_compression
        hKun hKT hmatch C hTG hTΓ hJ }
  exact ⟨W⟩

/-- Theorem `thm:spine` after the finite Leavitt matrix calculation has been
packaged as its exact `CompressionSetup`. -/
theorem explicit_spine_not_sofic
    (hKun : KunTheorem) (hKT : KunThomTheorem)
    (hmatch : ConservativeMatchingTheorem)
    {A J : Type} [Ring A] [Countable A] [Group J]
    [Algebra (ZMod 2) A] [Algebra.FiniteType (ZMod 2) A]
    [Countable (elementaryGroup (Fin 4) A)]
    [Countable (elementaryGroup (Fin 3) A)]
    (hEJZ : ErshovJaikinTheorem)
    (C : CompressionSetup (elementaryGroup (Fin 4) A)
      (elementaryGroup (Fin 3) A) J)
    (hJ : ¬ IsLEF J) : ¬ IsSofic (elementaryGroup (Fin 4) A) := by
  have hT4 : HasKazhdanPropertyT (elementaryGroup (Fin 4) A) :=
    hEJZ A 4 (by omega)
  have hT3 : HasKazhdanPropertyT (elementaryGroup (Fin 3) A) :=
    hEJZ A 3 (by omega)
  exact not_isSofic_of_kazhdan_compression hKun hKT hmatch C hT4 hT3 hJ

/-- The finite-table theorem supplies a concrete finitely presented cover in
the exact `PresentedGroup` sense used by Mathlib. -/
theorem finitelyPresented_nonsofic_cover
    {G : Type*} [Group G] [Countable G] [Nonempty G] [Group.FG G]
    (hG : ¬ IsSofic G) :
    ∃ (F : Finset G) (h₁ : 1 ∈ F) (ε : ℝ),
      0 < ε ∧ ¬ IsSofic (tableGroup F h₁) ∧
        Function.Surjective (tableEvaluation F h₁) := by
  obtain ⟨F, h₁, ε, hε, _, hnsofic, hsurj⟩ :=
    exists_finitelyPresented_obstruction hG
  exact ⟨F, h₁, ε, hε, hnsofic, hsurj⟩

/-- A finitely presented nonsofic countable group follows from the compression
construction and the finite multiplication-table cover. -/
theorem finitely_presented_nonsofic_groups_exist
    (hKun : KunTheorem) (hKT : KunThomTheorem)
    (hmatch : ConservativeMatchingTheorem)
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable G] [Countable Γ] [Nonempty G]
    (C : CompressionSetup G Γ J)
    (hTG : HasKazhdanPropertyT G) (hTΓ : HasKazhdanPropertyT Γ)
    (hJ : ¬ IsLEF J) :
    ∃ (F : Finset G) (h₁ : 1 ∈ F) (ε : ℝ),
      0 < ε ∧ ¬ IsSofic (tableGroup F h₁) ∧
        Function.Surjective (tableEvaluation F h₁) := by
  letI : Group.FG G := (Group.fg_iff').mpr
    ⟨C.ambientGenerators.card, C.ambientGenerators, rfl,
      C.ambientGenerators_generate⟩
  apply finitelyPresented_nonsofic_cover
  exact not_isSofic_of_kazhdan_compression hKun hKT hmatch C hTG hTΓ hJ

end NonsoficGroupsExist
