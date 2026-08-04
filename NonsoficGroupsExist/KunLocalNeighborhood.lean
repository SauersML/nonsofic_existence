import NonsoficGroupsExist.GeneratorWords
import NonsoficGroupsExist.KunMarkerSelection
import NonsoficGroupsExist.SoficErrors

/-!
# Uniformly large local neighborhoods in an infinite sofic approximation

For a prescribed cardinal `q`, choose `q` distinct elements of the infinite
group and fixed generator words for them.  Away from the finite union of word
evaluation and collision errors, their images of a vertex are distinct and
all lie in one fixed-radius forward neighborhood.  This supplies the lower
neighborhood-cardinality input used by Kun's repair argument.
-/

namespace NonsoficGroupsExist
namespace KunLocalNeighborhood

open KunSupport

variable {G : Type} [Group G] [Infinite G]

/-- A canonical family of distinct group elements, available because `G` is
infinite. -/
noncomputable def witness (i : ℕ) : G := Infinite.natEmbedding G i

omit [Group G] in
theorem witness_injective : Function.Injective (witness : ℕ → G) :=
  (Infinite.natEmbedding G).injective

/-- A fixed word in `S` for the `i`th canonical witness. -/
noncomputable def witnessWord
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (i : ℕ) : List G :=
  Classical.choose (exists_generator_word S hsymm hgen (witness i))

theorem witnessWord_mem
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (i : ℕ) :
    ∀ g ∈ witnessWord S hsymm hgen i, g ∈ S :=
  (Classical.choose_spec
    (exists_generator_word S hsymm hgen (witness i))).1

@[simp] theorem witnessWord_prod
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (i : ℕ) :
    (witnessWord S hsymm hgen i).prod = witness i :=
  (Classical.choose_spec
    (exists_generator_word S hsymm hgen (witness i))).2

/-- The sum of the chosen word lengths is a convenient common radius. -/
noncomputable def witnessRadius
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (q : ℕ) : ℕ :=
  ∑ i : Fin q, (witnessWord S hsymm hgen i).length

theorem witnessWord_length_le_radius
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (q : ℕ) (i : Fin q) :
    (witnessWord S hsymm hgen i).length ≤
      witnessRadius S hsymm hgen q := by
  classical
  unfold witnessRadius
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin q ↦ (witnessWord S hsymm hgen j).length)
    (fun j _ ↦ Nat.zero_le (witnessWord S hsymm hgen j).length)
    (Finset.mem_univ i)

omit [Group G] [Infinite G] in
/-- Evaluation of a word in `S` is reached by its corresponding forward
trajectory. -/
theorem evaluateWord_mem_forwardNeighborhood
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (w : List G) (hw : ∀ g ∈ w, g ∈ S) (x : M) :
    SoficApproximation.evaluateWord τ w x ∈
      forwardNeighborhood M τ S w.length {x} := by
  induction w with
  | nil => simp [SoficApproximation.evaluateWord, forwardNeighborhood]
  | cons g w ih =>
      change τ g (SoficApproximation.evaluateWord τ w x) ∈
        forwardStep M τ S (forwardNeighborhood M τ S w.length {x})
      apply mem_forwardStep_of_mem M τ S _ (hw g (by simp))
      exact ih (fun a ha ↦ hw a (by simp [ha]))

namespace SoficApproximation

variable (A : SoficApproximation G)

/-- Vertices where a fixed word does not evaluate to the permutation assigned
to its product. -/
noncomputable def wordEvaluationError (n : ℕ) (w : List G) :
    Finset (A.model n) :=
  Finset.univ.filter fun x ↦
    A.map n w.prod x ≠ SoficApproximation.evaluateWord (A.map n) w x

omit [Infinite G] in
theorem wordEvaluationError_negligible (w : List G) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((wordEvaluationError A n w).card : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := A.word_close w ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  change |((wordEvaluationError A n w).card : ℝ) /
    Fintype.card (A.model n)| < ε
  rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
  simpa [hammingDistance, wordEvaluationError] using hN n hn

/-- All word-evaluation failures for the first `q` canonical witnesses. -/
noncomputable def wordErrorUnion
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (q n : ℕ) :
    Finset (A.model n) :=
  Finset.univ.biUnion fun i : Fin q ↦
    wordEvaluationError A n (witnessWord S hsymm hgen i)

/-- All pairwise collision failures for the first `q` canonical witnesses. -/
noncomputable def collisionUnion (q n : ℕ) : Finset (A.model n) :=
  Finset.univ.biUnion fun i : Fin q ↦
    (Finset.univ.filter fun j : Fin q ↦ i ≠ j).biUnion fun j ↦
      A.collisionError n (witness i) (witness j)

/-- The complete exceptional locus for the local-neighborhood lower bound. -/
noncomputable def localNeighborhoodBad
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (q n : ℕ) :
    Finset (A.model n) :=
  wordErrorUnion A S hsymm hgen q n ∪ collisionUnion A q n

theorem wordErrorUnion_negligible
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (q : ℕ) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((wordErrorUnion A S hsymm hgen q n).card : ℝ) := by
  let I : Finset (Fin q) := Finset.univ
  have hsum : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ∑ i ∈ I,
        ((wordEvaluationError A n (witnessWord S hsymm hgen i)).card : ℝ) :=
    Negligible.sum I _ fun i _ ↦
      wordEvaluationError_negligible A (witnessWord S hsymm hgen i)
  apply Negligible.mono_nonneg
    (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hsum
  intro n
  exact_mod_cast (Finset.card_biUnion_le :
    (wordErrorUnion A S hsymm hgen q n).card ≤
      ∑ i ∈ I,
        (wordEvaluationError A n (witnessWord S hsymm hgen i)).card)

theorem collisionUnion_negligible (q : ℕ) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((collisionUnion A q n).card : ℝ) := by
  let I : Finset (Fin q) := Finset.univ
  have hinner : ∀ i : Fin q, Negligible
      (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ∑ j ∈ I.filter fun j ↦ i ≠ j,
        ((A.collisionError n (witness i) (witness j)).card : ℝ) := by
    intro i
    exact Negligible.sum (I.filter fun j ↦ i ≠ j) _ fun j hj ↦
      A.collisionError_negligible (witness i) (witness j) (by
        intro hij
        exact (Finset.mem_filter.mp hj).2
          (Fin.ext (witness_injective hij)))
  have hsum : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ∑ i ∈ I, ∑ j ∈ I.filter fun j ↦ i ≠ j,
        ((A.collisionError n (witness i) (witness j)).card : ℝ) :=
    Negligible.sum I _ fun i _ ↦ hinner i
  apply Negligible.mono_nonneg
    (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hsum
  intro n
  have hcard : (collisionUnion A q n).card ≤
      ∑ i ∈ I, ∑ j ∈ I.filter fun j ↦ i ≠ j,
        (A.collisionError n (witness i) (witness j)).card := by
    refine (Finset.card_biUnion_le).trans
      (Finset.sum_le_sum fun i _ ↦ ?_)
    exact Finset.card_biUnion_le
  exact_mod_cast hcard

theorem localNeighborhoodBad_negligible
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (q : ℕ) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((localNeighborhoodBad A S hsymm hgen q n).card : ℝ) := by
  have hsum := Negligible.add
    (wordErrorUnion_negligible A S hsymm hgen q)
    (collisionUnion_negligible A q)
  apply Negligible.mono_nonneg
    (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hsum
  intro n
  exact_mod_cast Finset.card_union_le
    (wordErrorUnion A S hsymm hgen q n) (collisionUnion A q n)

/-- Outside the explicitly negligible error locus, a radius independent of
`n` contains at least `q` vertices. -/
theorem card_forwardNeighborhood_ge
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (q n : ℕ)
    (x : A.model n)
    (hx : x ∉ localNeighborhoodBad A S hsymm hgen q n) :
    q ≤ (forwardNeighborhood (A.model n) (A.map n) S
      (witnessRadius S hsymm hgen q) {x}).card := by
  classical
  have hxWord : x ∉ wordErrorUnion A S hsymm hgen q n := by
    intro h
    exact hx (Finset.mem_union_left _ h)
  have hxCollision : x ∉ collisionUnion A q n := by
    intro h
    exact hx (Finset.mem_union_right _ h)
  have heval (i : Fin q) :
      SoficApproximation.evaluateWord (A.map n)
          (witnessWord S hsymm hgen i) x =
        A.map n (witness i) x := by
    have hnot : x ∉ wordEvaluationError A n
        (witnessWord S hsymm hgen i) := by
      intro hi
      apply hxWord
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, hi⟩
    have hEq : A.map n (witnessWord S hsymm hgen i).prod x =
        SoficApproximation.evaluateWord (A.map n)
          (witnessWord S hsymm hgen i) x := by
      simpa [wordEvaluationError] using hnot
    rw [witnessWord_prod] at hEq
    exact hEq.symm
  have hinjective : Function.Injective fun i : Fin q ↦
      SoficApproximation.evaluateWord (A.map n)
        (witnessWord S hsymm hgen i) x := by
    intro i j hij
    by_contra hijIndex
    have hnot : x ∉ A.collisionError n (witness i) (witness j) := by
      intro hcollision
      apply hxCollision
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hijIndex⟩,
        hcollision⟩
    have hmaps : A.map n (witness i) x = A.map n (witness j) x := by
      rw [← heval i, ← heval j]
      exact hij
    exfalso
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmaps⟩)
  let images : Finset (A.model n) := Finset.univ.image fun i : Fin q ↦
    SoficApproximation.evaluateWord (A.map n)
      (witnessWord S hsymm hgen i) x
  have himages : images ⊆ forwardNeighborhood (A.model n) (A.map n) S
      (witnessRadius S hsymm hgen q) {x} := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    apply forwardNeighborhood_mono_time (A.model n) (A.map n) S
      (witnessWord_length_le_radius S hsymm hgen q i)
    exact evaluateWord_mem_forwardNeighborhood (A.model n) (A.map n) S
      (witnessWord S hsymm hgen i) (witnessWord_mem S hsymm hgen i) x
  have hcard : images.card = q := by
    rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ,
      Fintype.card_fin]
  calc
    q = images.card := hcard.symm
    _ ≤ (forwardNeighborhood (A.model n) (A.map n) S
        (witnessRadius S hsymm hgen q) {x}).card :=
      Finset.card_le_card himages

end SoficApproximation
end KunLocalNeighborhood
end NonsoficGroupsExist
