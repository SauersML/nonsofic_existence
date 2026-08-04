import NonsoficGroupsExist.KunThreshold
import NonsoficGroupsExist.Criterion

/-!
# Generator-graph cut and variation identities

These identities connect the analytic finite Markov estimates to the actual
occurrence graph of a sofic approximation.  Generator labels remain distinct,
and fixed-point loops contribute neither to cuts nor to variation.
-/

namespace NonsoficGroupsExist
namespace KunGeneratorGraph

open KazhdanGNS
open FiniteMultiGraph
open scoped symmDiff

variable {G : Type} [Group G]

/-- The occurrence boundary of the generator graph is exactly the directed
generator cut size used by the Markov estimate. -/
theorem boundaryCard_generatorGraph
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (U : Finset Y) :
    (generatorGraph Y T act).boundaryCard U =
      generatorCutSize Y act T U := by
  classical
  let crosses : T → Y → Prop := fun t y ↦
    (y ∈ U ∧ act t.1 y ∉ U) ∨ (act t.1 y ∈ U ∧ y ∉ U)
  have hleft :
      (generatorGraph Y T act).boundaryCard U =
        (Finset.univ.filter fun p : T × Y ↦ crosses p.1 p.2).card := by
    unfold boundaryCard boundary
    dsimp only [generatorGraph]
    apply Finset.card_bij (fun e _ ↦ e.1)
    · intro e he
      have hecross : crosses e.1.1 e.1.2 := by
        simpa [crosses] using (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hecross⟩
    · intro e₁ _ e₂ _ heq
      exact Subtype.ext heq
    · intro p hp
      have hcross : crosses p.1 p.2 := (Finset.mem_filter.mp hp).2
      have hmove : act p.1.1 p.2 ≠ p.2 := by
        intro heq
        simp [crosses, heq] at hcross
      let e : (generatorGraph Y T act).edge :=
        ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩⟩
      refine ⟨e, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [e, crosses] using hcross⟩
  have hpairs :
      (Finset.univ.filter fun p : T × Y ↦ crosses p.1 p.2).card =
        ∑ t : T, (Finset.univ.filter fun y : Y ↦ crosses t y).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hper (t : T) :
      ((U.map (act t.1).toEmbedding) ∆ U).card =
        (Finset.univ.filter fun y : Y ↦ crosses t y).card := by
    apply Finset.card_bij (fun z _ ↦ (act t.1).symm z)
    · intro z hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_symmDiff] at hz
      simpa [crosses] using hz
    · intro z₁ _ z₂ _ h
      exact (act t.1).symm.injective h
    · intro y hy
      refine ⟨act t.1 y, ?_, (act t.1).symm_apply_apply y⟩
      have hycross : crosses t y := (Finset.mem_filter.mp hy).2
      simp only [Finset.mem_symmDiff]
      simpa [crosses] using hycross
  rw [hleft, hpairs, generatorCutSize]
  calc
    ∑ t : T, (Finset.univ.filter fun y : Y ↦ crosses t y).card =
        ∑ t : T, ((U.map (act t.1).toEmbedding) ∆ U).card := by
      apply Finset.sum_congr rfl
      intro t _
      exact (hper t).symm
    _ = ∑ s ∈ T, ((U.map (act s).toEmbedding) ∆ U).card := by
      simpa using Finset.sum_attach T
        (fun s ↦ ((U.map (act s).toEmbedding) ∆ U).card)

/-- Removing fixed-point loops does not change the total generator variation,
so the graph variation is the full label-by-vertex sum. -/
theorem edgeVariation_generatorGraph
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (f : Y → ℝ) :
    (generatorGraph Y T act).edgeVariation f =
      ∑ t : T, ∑ y : Y, |f (act t.1 y) - f y| := by
  classical
  let arcs : Finset (T × Y) :=
    Finset.univ.filter fun p ↦ act p.1.1 p.2 ≠ p.2
  unfold edgeVariation
  dsimp only [generatorGraph]
  change (∑ a : ↑(Finset.univ.filter fun p : T × Y ↦
      act p.1.1 p.2 ≠ p.2), |f a.1.2 - f (act a.1.1.1 a.1.2)|) = _
  calc
    (∑ a : ↑(Finset.univ.filter fun p : T × Y ↦
        act p.1.1 p.2 ≠ p.2), |f a.1.2 - f (act a.1.1.1 a.1.2)|) =
        arcs.sum fun p ↦ |f p.2 - f (act p.1.1 p.2)| := by
      simpa [arcs] using Finset.sum_attach arcs
        (fun p : T × Y ↦ |f p.2 - f (act p.1.1 p.2)|)
    _ = ∑ p : T × Y, |f p.2 - f (act p.1.1 p.2)| := by
      apply Finset.sum_subset (Finset.subset_univ arcs)
      intro p _ hp
      have hfix : act p.1.1 p.2 = p.2 := by
        by_contra hmove
        exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩)
      simp [hfix]
    _ = ∑ t : T, ∑ y : Y, |f y - f (act t.1 y)| := by
      rw [Fintype.sum_prod_type]
    _ = ∑ t : T, ∑ y : Y, |f (act t.1 y) - f y| := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro y _
      exact abs_sub_comm _ _

end KunGeneratorGraph
end NonsoficGroupsExist
