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

private noncomputable def disagreement (n : ℕ) (g : H) : Finset (D.subset n) :=
  Finset.univ.filter fun x ↦
    (D.completedMap n g x : D.ambient n) ≠ D.act n g x

private noncomputable def ambientMultiplicationBad (n : ℕ) (g h : H) : Finset (D.subset n) :=
  Finset.univ.filter fun x ↦
    D.act n (g * h) (x : D.ambient n) ≠ D.act n g (D.act n h x)

private noncomputable def completedMultiplicationBad (n : ℕ) (g h : H) : Finset (D.subset n) :=
  Finset.univ.filter fun x ↦
    D.completedMap n (g * h) x ≠ D.completedMap n g (D.completedMap n h x)

private noncomputable def disagreementPreimage (n : ℕ) (g h : H) : Finset (D.subset n) :=
  Finset.univ.filter fun x ↦ D.completedMap n h x ∈ D.disagreement n g

private theorem completedMultiplicationBad_subset (n : ℕ) (g h : H) :
    D.completedMultiplicationBad n g h ⊆
      D.disagreement n (g * h) ∪ D.disagreement n h ∪
        D.disagreementPreimage n g h ∪ D.ambientMultiplicationBad n g h := by
  classical
  intro x hx
  simp only [completedMultiplicationBad, disagreement, disagreementPreimage,
    ambientMultiplicationBad, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union] at hx ⊢
  by_cases hgh : (D.completedMap n (g * h) x : D.ambient n) ≠ D.act n (g * h) x
  · exact Or.inl (Or.inl (Or.inl hgh))
  by_cases hh : (D.completedMap n h x : D.ambient n) ≠ D.act n h x
  · exact Or.inl (Or.inl (Or.inr hh))
  by_cases hg :
      (D.completedMap n g (D.completedMap n h x) : D.ambient n) ≠
        D.act n g (D.completedMap n h x : D.ambient n)
  · exact Or.inl (Or.inr hg)
  by_cases hamb : D.act n (g * h) (x : D.ambient n) ≠
      D.act n g (D.act n h x)
  · exact Or.inr hamb
  exfalso
  apply hx
  apply Subtype.ext
  rw [not_ne_iff.mp hgh, not_ne_iff.mp hg, not_ne_iff.mp hh,
    not_ne_iff.mp hamb]

private theorem disagreementPreimage_card (n : ℕ) (g h : H) :
    (D.disagreementPreimage n g h).card = (D.disagreement n g).card := by
  classical
  let p := D.completedMap n h
  have himage : D.disagreementPreimage n g h =
      (D.disagreement n g).image p.symm := by
    ext x
    simp only [disagreementPreimage, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hx
      exact ⟨p x, hx, p.symm_apply_apply x⟩
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = p x := by
        have := congrArg p hxy
        simpa using this
      rw [← hyx]
      exact hy
  rw [himage, Finset.card_image_of_injective _ p.symm.injective]

private theorem completedMultiplicationBad_card_le (n : ℕ) (g h : H) :
    (D.completedMultiplicationBad n g h).card ≤
      (D.disagreement n (g * h)).card + (D.disagreement n h).card +
        (D.disagreement n g).card + (D.ambientMultiplicationBad n g h).card := by
  classical
  have hs := Finset.card_le_card (D.completedMultiplicationBad_subset n g h)
  have h1 := Finset.card_union_le (D.disagreement n (g * h)) (D.disagreement n h)
  have h2 := Finset.card_union_le
    (D.disagreement n (g * h) ∪ D.disagreement n h) (D.disagreementPreimage n g h)
  have h3 := Finset.card_union_le
    (D.disagreement n (g * h) ∪ D.disagreement n h ∪ D.disagreementPreimage n g h)
      (D.ambientMultiplicationBad n g h)
  rw [D.disagreementPreimage_card n g h] at h2
  omega

end LocalizedApproximationData
end NonsoficGroupsExist
