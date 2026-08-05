import NonsoficGroupsExist.TableCover
import NonsoficGroupsExist.ShalomFinitePresentation
import NonsoficGroupsExist.KazhdanFiniteGeneration

/-!
# Kazhdan covers of nonsofic groups

Theorem `thm:kcover`: a nonsofic group with Kazhdan's property `(T)` is
covered by an infinite finitely presented property-`(T)` group that is
not sofic.  The cover imposes the forbidden multiplication table of
`thm:table` as finitely many additional relators on the presented
Kazhdan cover produced by Shalom's theorem
(`Shalom.exists_presented_kazhdan_cover`).  The nonsoficity transfer
generalizes `pullbackTableModel` away from presented groups: any group
carrying a multiplicative separated family indexed by the forbidden
table admits no accurate model of the family's image table.
-/

namespace NonsoficGroupsExist

set_option linter.unusedSectionVars false

universe u

variable {G : Type u} [Group G]

section Family

variable {H : Type*} [Group H] (F : Finset G) (y : G → H)

/-- The image table of a multiplicative family. -/
noncomputable def familyTestSet : Finset H := by
  classical
  exact F.attach.image fun g ↦ y g.1

theorem y_mem_familyTestSet {g : G} (hg : g ∈ F) :
    y g ∈ familyTestSet F y := by
  classical
  exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩

variable (hymul : ∀ g ∈ F, ∀ h ∈ F, y g * y h = y (g * h))

include hymul in
theorem y_mem_familyDomain (g : ↥(tableDomain F)) :
    y g.1 ∈ tableDomain (familyTestSet F y) := by
  classical
  have hg := g.2
  simp only [tableDomain, Finset.mem_union, Finset.mem_image,
    Finset.mem_product] at hg
  rcases hg with hg | ⟨⟨a, b⟩, ⟨ha, hb⟩, hab⟩
  · exact mem_tableDomain_of_mem (y_mem_familyTestSet F y hg)
  · rw [← hab, ← hymul a ha b hb]
    exact mul_mem_tableDomain (y_mem_familyTestSet F y ha)
      (y_mem_familyTestSet F y hb)

variable (hysep : ∀ g ∈ F, ∀ h ∈ F, g ≠ h → y g ≠ y h)

include hymul in
/-- Pulling a model of the family's image table back along the family
produces a model of the original table. -/
noncomputable def familyPullbackModel {ε : ℝ}
    (M : TableModel H (familyTestSet F y) ε) :
    TableModel G F ε := by
  classical
  refine
    { carrier := M.carrier
      nonempty := M.nonempty
      act := fun g ↦ M.act ⟨y g.1, y_mem_familyDomain F y hymul g⟩
      multiplicative := ?_
      separated := ?_ }
  · intro g hg h hh
    have heq : (⟨y ((⟨g * h, mul_mem_tableDomain hg hh⟩ :
        ↥(tableDomain F)).1),
        y_mem_familyDomain F y hymul
          ⟨g * h, mul_mem_tableDomain hg hh⟩⟩ :
        ↥(tableDomain (familyTestSet F y))) =
        ⟨y g * y h,
          mul_mem_tableDomain (y_mem_familyTestSet F y hg)
            (y_mem_familyTestSet F y hh)⟩ := by
      apply Subtype.ext
      exact (hymul g hg h hh).symm
    change hammingDistance M.carrier
      (M.act ⟨y ((⟨g * h, mul_mem_tableDomain hg hh⟩ :
        ↥(tableDomain F)).1),
        y_mem_familyDomain F y hymul
          ⟨g * h, mul_mem_tableDomain hg hh⟩⟩)
      (M.act ⟨y g, y_mem_familyDomain F y hymul
        ⟨g, mem_tableDomain_of_mem hg⟩⟩ *
        M.act ⟨y h, y_mem_familyDomain F y hymul
          ⟨h, mem_tableDomain_of_mem hh⟩⟩) ≤ ε
    rw [heq]
    exact M.multiplicative (y g) (y_mem_familyTestSet F y hg)
      (y h) (y_mem_familyTestSet F y hh)
  · intro g hg h hh hne
    exact M.separated (y g) (y_mem_familyTestSet F y hg)
      (y h) (y_mem_familyTestSet F y hh) (hysep g hg h hh hne)

include y hymul hysep in
/-- A group carrying a multiplicative separated family over a table with
no accurate models is itself not sofic. -/
theorem not_isSofic_of_family {ε : ℝ} (hε : 0 < ε)
    (hbad : IsEmpty (TableModel G F ε)) :
    ¬ IsSofic H := by
  intro hsofic
  obtain ⟨M⟩ := tableModel_of_isSofic hsofic (familyTestSet F y) ε hε
  exact hbad.false (familyPullbackModel F y hymul hysep M)

end Family

section HomExt

variable {α : Type*} {M : Type*} [Group M]

/-- Homomorphisms out of a free group agree once they agree on the
generators. -/
theorem freeGroup_hom_eq_on {f g : FreeGroup α →* M}
    (h : ∀ i, f (FreeGroup.of i) = g (FreeGroup.of i)) :
    ∀ w, f w = g w := by
  intro w
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · rw [map_one, map_one]
  · exact h
  · intro i hi
    rw [map_inv, map_inv, hi]
  · intro a b ha hb
    rw [map_mul, map_mul, ha, hb]

/-- The universal map of a presented group computes on classes via the
free lift. -/
theorem presentedGroup_toGroup_mk {rels : Set (FreeGroup α)}
    {f : α → M} (h : ∀ r ∈ rels, FreeGroup.lift f r = 1)
    (w : FreeGroup α) :
    PresentedGroup.toGroup h (PresentedGroup.mk rels w) =
      FreeGroup.lift f w := by
  refine freeGroup_hom_eq_on
    (f := (PresentedGroup.toGroup h).comp (PresentedGroup.mk rels))
    (g := FreeGroup.lift f) (fun i ↦ ?_) w
  rw [MonoidHom.comp_apply,
    show PresentedGroup.mk rels (FreeGroup.of i) =
      PresentedGroup.of i from rfl,
    PresentedGroup.toGroup.of, FreeGroup.lift_apply_of]

end HomExt

/-- **Theorem `thm:kcover`** (Kazhdan covers): every infinite nonsofic
group with property `(T)` is covered by an infinite finitely presented
property-`(T)` group that is not sofic.  Finite generation is not a
hypothesis: property `(T)` forces it
(`KazhdanFiniteGeneration.exists_symmetric_generating_finset`). -/
theorem exists_kazhdan_finitelyPresented_nonsofic_cover
    [Infinite G] (hns : ¬ IsSofic G)
    (hT : HasKazhdanPropertyT.{u, u} G) :
    ∃ (Γ : Type) (_ : Group Γ) (φ : Γ →* G),
      Function.Surjective φ ∧ Infinite Γ ∧
        Group.IsFinitelyPresented Γ ∧
        HasKazhdanPropertyT.{0, 0} Γ ∧ ¬ IsSofic Γ := by
  classical
  obtain ⟨F, ε, -, hε, hbad⟩ := exists_table_obstruction hns
  obtain ⟨S, -, -, hgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset G hT
  obtain ⟨m, relsP, θ, hθsurj, hθT⟩ :=
    Shalom.exists_presented_kazhdan_cover S hgen hT
  set θhat : FreeGroup (Fin m) →* G :=
    θ.comp (PresentedGroup.mk _) with hθhat
  have hθhatsurj : Function.Surjective θhat :=
    hθsurj.comp (PresentedGroup.mk_surjective _)
  set yhat : G → FreeGroup (Fin m) := fun g ↦
    if g = 1 then 1 else Function.surjInv hθhatsurj g with hyhat
  have hlift : ∀ g : G, θhat (yhat g) = g := by
    intro g
    by_cases hg : g = 1
    · subst hg
      have h1 : yhat 1 = 1 := by
        rw [hyhat]
        simp
      rw [h1, map_one]
    · rw [hyhat]
      simp only [if_neg hg]
      exact Function.surjInv_eq hθhatsurj g
  set relsH : Finset (FreeGroup (Fin m)) := relsP ∪
    (F ×ˢ F).image fun p ↦
      yhat p.1 * yhat p.2 * (yhat (p.1 * p.2))⁻¹ with hrelsH
  -- The cover and its structure maps.
  have hφcond : ∀ r ∈ ((relsH : Finset (FreeGroup (Fin m))) :
      Set (FreeGroup (Fin m))),
      FreeGroup.lift (fun i ↦ θhat (FreeGroup.of i)) r = 1 := by
    intro r hr
    have hlifteq : ∀ w, FreeGroup.lift
        (fun i ↦ θhat (FreeGroup.of i)) w = θhat w :=
      freeGroup_hom_eq_on fun i ↦ by rw [FreeGroup.lift_apply_of]
    rw [hlifteq]
    rw [Finset.mem_coe, hrelsH, Finset.mem_union] at hr
    rcases hr with hr | hr
    · have hone : PresentedGroup.mk
          ((relsP : Finset (FreeGroup (Fin m))) :
            Set (FreeGroup (Fin m))) r = 1 :=
        PresentedGroup.one_of_mem (Finset.mem_coe.mpr hr)
      rw [hθhat, MonoidHom.comp_apply, hone, map_one]
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [map_mul, map_mul, map_inv, hlift, hlift, hlift]
      rw [mul_inv_cancel]
  set φ : PresentedGroup ((relsH : Finset (FreeGroup (Fin m))) :
      Set (FreeGroup (Fin m))) →* G :=
    PresentedGroup.toGroup hφcond with hφ
  have hφmk : ∀ w, φ (PresentedGroup.mk _ w) = θhat w := by
    intro w
    rw [hφ, presentedGroup_toGroup_mk]
    exact freeGroup_hom_eq_on (fun i ↦ by rw [FreeGroup.lift_apply_of]) w
  have hφsurj : Function.Surjective φ := by
    intro g
    obtain ⟨w, hw⟩ := hθhatsurj g
    exact ⟨PresentedGroup.mk _ w, by rw [hφmk w, hw]⟩
  -- The Kazhdan cover surjects onto the new cover.
  have hPHcond : ∀ r ∈ ((relsP : Finset (FreeGroup (Fin m))) :
      Set (FreeGroup (Fin m))),
      FreeGroup.lift (fun i ↦ (PresentedGroup.of i :
        PresentedGroup ((relsH : Finset (FreeGroup (Fin m))) :
          Set (FreeGroup (Fin m))))) r = 1 := by
    intro r hr
    have hlifteq : ∀ w, FreeGroup.lift
        (fun i ↦ (PresentedGroup.of i :
          PresentedGroup ((relsH : Finset (FreeGroup (Fin m))) :
            Set (FreeGroup (Fin m))))) w =
        PresentedGroup.mk _ w :=
      freeGroup_hom_eq_on fun i ↦ by
        rw [FreeGroup.lift_apply_of]
        rfl
    rw [hlifteq]
    apply PresentedGroup.one_of_mem
    rw [Finset.mem_coe, hrelsH, Finset.mem_union]
    exact Or.inl (Finset.mem_coe.mp hr)
  set εPH : PresentedGroup ((relsP : Finset (FreeGroup (Fin m))) :
      Set (FreeGroup (Fin m))) →*
      PresentedGroup ((relsH : Finset (FreeGroup (Fin m))) :
        Set (FreeGroup (Fin m))) :=
    PresentedGroup.toGroup hPHcond with hεPH
  have hεPHsurj : Function.Surjective εPH := by
    intro γ
    obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective _ γ
    refine ⟨PresentedGroup.mk _ w, ?_⟩
    rw [hεPH, presentedGroup_toGroup_mk, ← hw]
    exact freeGroup_hom_eq_on (fun i ↦ by
      rw [FreeGroup.lift_apply_of]
      rfl) w
  -- The multiplicative separated family.
  set y : G → PresentedGroup ((relsH : Finset (FreeGroup (Fin m))) :
      Set (FreeGroup (Fin m))) :=
    fun g ↦ PresentedGroup.mk _ (yhat g) with hy
  have hymul : ∀ g ∈ F, ∀ h ∈ F, y g * y h = y (g * h) := by
    intro g hg h hh
    have hrel : PresentedGroup.mk
        ((relsH : Finset (FreeGroup (Fin m))) :
          Set (FreeGroup (Fin m)))
        (yhat g * yhat h * (yhat (g * h))⁻¹) = 1 := by
      apply PresentedGroup.one_of_mem
      rw [Finset.mem_coe, hrelsH, Finset.mem_union]
      refine Or.inr (Finset.mem_image.mpr
        ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩)
    rw [map_mul, map_mul, map_inv] at hrel
    have := mul_inv_eq_one.mp hrel
    rw [hy]
    exact this
  have hysep : ∀ g ∈ F, ∀ h ∈ F, g ≠ h → y g ≠ y h := by
    intro g hg h hh hne hcon
    apply hne
    have h1 : φ (y g) = g := by rw [hy]; rw [hφmk, hlift]
    have h2 : φ (y h) = h := by rw [hy]; rw [hφmk, hlift]
    rw [← h1, ← h2, hcon]
  -- Assemble.
  refine ⟨PresentedGroup ((relsH : Finset (FreeGroup (Fin m))) :
      Set (FreeGroup (Fin m))), inferInstance, φ, hφsurj,
    Infinite.of_surjective φ hφsurj, inferInstance,
    HasKazhdanPropertyT.of_surjective εPH hεPHsurj hθT,
    not_isSofic_of_family F y hymul hysep hε hbad⟩

end NonsoficGroupsExist
