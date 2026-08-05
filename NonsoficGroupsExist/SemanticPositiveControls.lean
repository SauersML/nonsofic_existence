import Mathlib.Data.ZMod.Basic
import NonsoficGroupsExist.AlmostAutomorphism
import NonsoficGroupsExist.KazhdanControl
import NonsoficGroupsExist.SoficPositiveControl
import NonsoficGroupsExist.TableCover

/-!
# Semantic positive controls

Closed examples for proposition and structure interfaces used by the negative
argument.  These declarations are deliberately independent of the headline
nonsoficity proof: they show that the interfaces describe actual mathematics,
instead of being satisfied only under relocated hypotheses.
-/

namespace NonsoficGroupsExist

/-- The one-element group has the elementary Kazhdan pair `(∅, 1)`. -/
theorem unit_isKazhdanPair :
    IsKazhdanPair.{0, 0} Unit ∅ 1 := by
  refine ⟨by norm_num, ?_⟩
  intro E _ _ _ ρ x hx _
  refine ⟨x, ?_, ?_⟩
  · intro hzero
    rw [hzero, norm_zero] at hx
    norm_num at hx
  · intro g
    cases g
    change ρ 1 x = x
    rw [map_one]
    rfl

/-- The same finite control set is an inhabited Kazhdan subset. -/
theorem unit_isKazhdanSubset :
    IsKazhdanSubset.{0, 0} Unit (∅ : Set Unit) 1 :=
  by simpa using IsKazhdanSubset.of_pair unit_isKazhdanPair

/-- Product-restricted soficity is satisfiable, independently of its
equivalence theorem. -/
theorem unit_isSoficProductRestricted : IsSoficProductRestricted Unit :=
  (isSofic_iff_productRestricted Unit).mp (isSofic_of_finite Unit)

/-- A closed multiplication-table model on a concrete finite group. -/
theorem zmodTwo_tableModel :
    Nonempty (TableModel (Multiplicative (ZMod 2)) {1} (1 / 2 : ℝ)) :=
  tableModel_of_isSofic (isSofic_of_finite (Multiplicative (ZMod 2)))
    {1} (1 / 2) (by norm_num)

/-- A closed finite cluster.  Its ambient permutation model has two points;
the selected finite group is the identity subgroup and rounding is its retraction. -/
noncomputable def zmodTwo_identityClusterData :
    AlmostAutomorphism.ClusterData
      (regularModel (Multiplicative (ZMod 2))) where
  radius := 1 / 4
  radius_pos := by norm_num
  candidate := {1}
  one_mem := by simp
  inv_mem := by
    intro c hc
    simpa using hc
  round := fun _ ↦ 1
  round_product_mem := by simp
  round_product_close := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    simp
  gap := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    left
    simp

end NonsoficGroupsExist
