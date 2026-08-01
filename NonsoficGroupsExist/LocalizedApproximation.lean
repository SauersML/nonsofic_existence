import NonsoficGroupsExist.Asymptotics
import NonsoficGroupsExist.Localization

/-!
# Localized approximations

This is the asymptotic wrapper around Lemma `lem:complete`.  It deliberately
starts from ambient permutations and selected finite subsets, not from a sofic
approximation on those subsets.  The latter is constructed by completing each
restricted partial injection.
-/

namespace NonsoficGroupsExist

/-- Post-selection data established in the last part of the matching argument.
Every error is normalized by the selected subset itself. -/
structure LocalizedApproximationData (H : Type) [Group H] where
  ambient : ℕ → FiniteModel
  subset : ∀ n, Finset (ambient n)
  act : ∀ n, H → Equiv.Perm (ambient n)
  card_diverges : Diverges fun n ↦ ((subset n).card : ℝ)
  invariant : ∀ g, Vanishing fun n ↦
    ((Finset.univ.filter fun x : subset n ↦ act n g (x : ambient n) ∉ subset n).card : ℝ) /
      (subset n).card
  multiplicative : ∀ g h, Vanishing fun n ↦
    ((Finset.univ.filter fun x : subset n ↦
      act n (g * h) (x : ambient n) ≠ act n g (act n h x)).card : ℝ) /
        (subset n).card
  faithful : ∀ g, g ≠ 1 → Vanishing fun n ↦
    ((Finset.univ.filter fun x : subset n ↦ act n g (x : ambient n) = x).card : ℝ) /
      (subset n).card

namespace LocalizedApproximationData

variable {H : Type} [Group H] (D : LocalizedApproximationData H)

/-- A chosen completion of the restriction of the ambient permutation. -/
noncomputable def completedMap (n : ℕ) (g : H) : Equiv.Perm (D.subset n) :=
  Classical.choose (Localization.exists_completion_with_bound (D.subset n) (D.act n g))

theorem completedMap_disagreement_bound (n : ℕ) (g : H) :
    (Finset.univ.filter fun x : D.subset n ↦
      (D.completedMap n g x : D.ambient n) ≠ D.act n g x).card ≤
    (Finset.univ.filter fun x : D.subset n ↦
      D.act n g (x : D.ambient n) ∉ D.subset n).card :=
  Classical.choose_spec
    (Localization.exists_completion_with_bound (D.subset n) (D.act n g))

theorem completedMap_disagreement_vanishing (g : H) : Vanishing fun n ↦
    ((Finset.univ.filter fun x : D.subset n ↦
      (D.completedMap n g x : D.ambient n) ≠ D.act n g x).card : ℝ) /
        (D.subset n).card := by
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) (D.invariant g)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast D.completedMap_disagreement_bound n g

end LocalizedApproximationData
end NonsoficGroupsExist
