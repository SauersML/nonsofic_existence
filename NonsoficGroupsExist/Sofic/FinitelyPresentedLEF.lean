import NonsoficGroupsExist.Sofic.LEF
import NonsoficGroupsExist.Covers.KazhdanCover

/-!
# Finitely presented LEF groups are residually finite

The manuscript's `lem:fplef`: if a group defined by finitely many
relators is LEF, every nontrivial element survives in a finite
quotient.  The proof is the paper's: a local embedding on the finite
set of all partial products of the relators and of one word for the
element extends, by killing the relators through the free lift, to a
genuine homomorphism into a finite symmetric group, and injectivity of
the local embedding separates the element from the identity.  The
partial-product bookkeeping is `exists_local_word_control`.
-/

namespace NonsoficGroupsExist

open scoped Classical

/-- **Lemma `lem:fplef`**: a group presented by finitely many relators
that is LEF is residually finite --- every nontrivial element is
separated from the identity by a homomorphism to a finite symmetric
group. -/
theorem finitelyPresented_isLEF_residuallyFinite
    {α : Type*} (rels : Finset (FreeGroup α))
    (hLEF : IsLEF (PresentedGroup (rels : Set (FreeGroup α))))
    (g : PresentedGroup (rels : Set (FreeGroup α))) (hg : g ≠ 1) :
    ∃ (n : ℕ)
      (φ : PresentedGroup (rels : Set (FreeGroup α)) →*
        Equiv.Perm (Fin n)), φ g ≠ 1 := by
  classical
  set mk : FreeGroup α →*
      PresentedGroup (rels : Set (FreeGroup α)) :=
    PresentedGroup.mk (rels : Set (FreeGroup α)) with hmkdef
  obtain ⟨w, hw⟩ :=
    PresentedGroup.mk_surjective (rels : Set (FreeGroup α)) g
  -- one finite control set per relator, one for the chosen word
  choose sControl hControl using fun z : FreeGroup α ↦
    exists_local_word_control (φ := mk) z
  set S : Finset (PresentedGroup (rels : Set (FreeGroup α))) :=
    (rels.sup sControl ∪ sControl w) ∪ {1, g} with hS
  obtain ⟨n, f, hinj, hmul⟩ := hLEF S
  -- the free lift kills every relator
  have hkill : ∀ r ∈ (rels : Set (FreeGroup α)),
      FreeGroup.lift (fun a ↦ f (mk (FreeGroup.of a))) r = 1 := by
    intro r hr
    have hsup : sControl r ⊆ rels.sup sControl :=
      Finset.le_sup (Finset.mem_coe.mp hr)
    have hsub : sControl r ⊆ S := by
      intro x hx
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (hsup hx))
    rw [hControl r (Equiv.Perm (Fin n)) f (hmul.mono hsub),
      PresentedGroup.one_of_mem hr, hmul.map_one]
  refine ⟨n, PresentedGroup.toGroup hkill, ?_⟩
  -- the extension agrees with the local embedding at `g`
  have hsubw : sControl w ⊆ S := fun x hx ↦
    Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hval : PresentedGroup.toGroup hkill g = f g := by
    rw [← hw, presentedGroup_toGroup_mk hkill w,
      hControl w (Equiv.Perm (Fin n)) f (hmul.mono hsubw)]
  rw [hval]
  intro hone
  have hgS : g ∈ S :=
    Finset.mem_union_right _ (by simp)
  have h1S : (1 : PresentedGroup (rels : Set (FreeGroup α))) ∈ S :=
    Finset.mem_union_right _ (by simp)
  exact hg (hinj hgS h1S (by rw [hone, hmul.map_one]))

end NonsoficGroupsExist
