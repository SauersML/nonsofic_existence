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
  Classical.choose (Localization.exists_completion (D.subset n) (D.act n g))

/-- The chosen completion retains every value whose ambient image remains in
the selected subset. -/
theorem completedMap_agrees (n : ℕ) (g : H) (x : D.subset n)
    (hx : D.act n g (x : D.ambient n) ∈ D.subset n) :
    (D.completedMap n g x : D.ambient n) = D.act n g x :=
  Classical.choose_spec
    (Localization.exists_completion (D.subset n) (D.act n g)) x hx

theorem completedMap_disagreement_bound (n : ℕ) (g : H) :
    (Finset.univ.filter fun x : D.subset n ↦
      (D.completedMap n g x : D.ambient n) ≠ D.act n g x).card ≤
    (Finset.univ.filter fun x : D.subset n ↦
      D.act n g (x : D.ambient n) ∉ D.subset n).card :=
  Finset.card_le_card (by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro hin
    exact hx (D.completedMap_agrees n g x hin))

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

theorem completedMultiplication_vanishing (g h : H) : Vanishing fun n ↦
    ((D.completedMultiplicationBad n g h).card : ℝ) / (D.subset n).card := by
  have hsum := Vanishing.add
    (Vanishing.add
      (D.completedMap_disagreement_vanishing (g * h))
      (D.completedMap_disagreement_vanishing h))
    (Vanishing.add
      (D.completedMap_disagreement_vanishing g)
      (D.multiplicative g h))
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  calc
    ((D.completedMultiplicationBad n g h).card : ℝ) / (D.subset n).card ≤
        (((D.disagreement n (g * h)).card + (D.disagreement n h).card +
          (D.disagreement n g).card + (D.ambientMultiplicationBad n g h).card : ℕ) : ℝ) /
            (D.subset n).card := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast D.completedMultiplicationBad_card_le n g h
    _ =
        ((D.disagreement n (g * h)).card : ℝ) / (D.subset n).card +
          ((D.disagreement n h).card : ℝ) / (D.subset n).card +
        (((D.disagreement n g).card : ℝ) / (D.subset n).card +
          ((D.ambientMultiplicationBad n g h).card : ℝ) / (D.subset n).card) := by
      push_cast
      ring

private noncomputable def completedFixed (n : ℕ) (g : H) : Finset (D.subset n) :=
  Finset.univ.filter fun x ↦ D.completedMap n g x = x

private noncomputable def completedMoved (n : ℕ) (g : H) : Finset (D.subset n) :=
  Finset.univ.filter fun x ↦ D.completedMap n g x ≠ x

private noncomputable def ambientFixed (n : ℕ) (g : H) : Finset (D.subset n) :=
  Finset.univ.filter fun x ↦ D.act n g (x : D.ambient n) = x

private theorem completedFixed_subset (n : ℕ) (g : H) :
    D.completedFixed n g ⊆ D.disagreement n g ∪ D.ambientFixed n g := by
  classical
  intro x hx
  simp only [completedFixed, disagreement, ambientFixed, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_cases hd : (D.completedMap n g x : D.ambient n) ≠ D.act n g x
  · exact Or.inl hd
  · right
    rw [← not_ne_iff.mp hd]
    exact congrArg Subtype.val hx

private theorem completedFixed_card_le (n : ℕ) (g : H) :
    (D.completedFixed n g).card ≤
      (D.disagreement n g).card + (D.ambientFixed n g).card := by
  exact (Finset.card_le_card (D.completedFixed_subset n g)).trans
    (Finset.card_union_le _ _)

theorem completedFixed_vanishing (g : H) (hg : g ≠ 1) : Vanishing fun n ↦
    ((D.completedFixed n g).card : ℝ) / (D.subset n).card := by
  have hsum := Vanishing.add (D.completedMap_disagreement_vanishing g) (D.faithful g hg)
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  calc
    ((D.completedFixed n g).card : ℝ) / (D.subset n).card ≤
        (((D.disagreement n g).card + (D.ambientFixed n g).card : ℕ) : ℝ) /
          (D.subset n).card := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast D.completedFixed_card_le n g
    _ = ((D.disagreement n g).card : ℝ) / (D.subset n).card +
        ((D.ambientFixed n g).card : ℝ) / (D.subset n).card := by
      push_cast
      ring

/-- The finite model carried by the selected subset. -/
abbrev localizedModel (n : ℕ) : FiniteModel where
  carrier := D.subset n
  fintype := inferInstance
  decidableEq := inferInstance

@[simp] theorem card_localizedModel (n : ℕ) :
    Fintype.card (D.localizedModel n) = (D.subset n).card := by
  simp [localizedModel]

private theorem hammingDistance_completed_mul (n : ℕ) (g h : H) :
    hammingDistance (D.localizedModel n) (D.completedMap n (g * h))
        (D.completedMap n g * D.completedMap n h) =
      ((D.completedMultiplicationBad n g h).card : ℝ) / (D.subset n).card := by
  unfold hammingDistance
  rw [D.card_localizedModel]
  congr 2

private theorem hammingDistance_completed_one (n : ℕ) (g : H) :
    hammingDistance (D.localizedModel n) (D.completedMap n g) 1 =
      ((D.completedMoved n g).card : ℝ) / (D.subset n).card := by
  unfold hammingDistance
  rw [D.card_localizedModel]
  congr 2

/-- Lemma `lem:complete`: completion turns the selected ambient restrictions
into a genuine sofic approximation. -/
noncomputable def toSoficApproximation : SoficApproximation H where
  model := D.localizedModel
  map := D.completedMap
  card_tendsToInfinity := by
    intro M
    obtain ⟨N, hN⟩ := D.card_diverges M
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [D.card_localizedModel]
    have h := hN n hn
    change (M : ℝ) ≤ (D.subset n).card at h
    exact_mod_cast h
  asymptoticallyMultiplicative := by
    intro g h ε hε
    obtain ⟨N, hN⟩ := D.completedMultiplication_vanishing g h ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hv := lt_of_abs_lt (hN n hn)
    rw [D.hammingDistance_completed_mul]
    exact hv
  asymptoticallyFaithful := by
    intro g hg ε hε
    obtain ⟨N₁, hN₁⟩ := D.completedFixed_vanishing g hg ε hε
    obtain ⟨N₂, hN₂⟩ := D.card_diverges 1
    refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
    have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
    have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
    have hsmall := lt_of_abs_lt (hN₁ n hn₁)
    have hcardR : (0 : ℝ) < (D.subset n).card := by
      have := hN₂ n hn₂
      positivity
    have hpartition :
        (D.completedMoved n g).card + (D.completedFixed n g).card =
          (D.subset n).card := by
      simpa [completedMoved, completedFixed] using
        (Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (fun x ↦ D.completedMap n g x ≠ x))
    have heq :
        ((D.completedMoved n g).card : ℝ) / (D.subset n).card =
          1 - ((D.completedFixed n g).card : ℝ) / (D.subset n).card := by
      have hpartitionR :
          ((D.completedMoved n g).card : ℝ) + ((D.completedFixed n g).card : ℝ) =
            (D.subset n).card := by
        exact_mod_cast hpartition
      field_simp
      linarith
    rw [D.hammingDistance_completed_one]
    rw [heq]
    linarith

end LocalizedApproximationData
end NonsoficGroupsExist
