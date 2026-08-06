import NonsoficGroupsExist.KOne.CodeChangeUnits
import NonsoficGroupsExist.KOne.CodePairTransport

/-!
# Glue: indexed code bijections are code-change units

The Higman–Thompson generation theorem (`codeChange_mem_stableUnits`)
speaks of pair *lists*; the pencil elimination produces pair data
indexed by a `Fintype`.  This file converts: a family of target words
and a family of source words, each forming a complete prefix code,
yields a unit `Σᵢ s_{τᵢ} t_{σᵢ}` of the diagonal class group.  It also
provides the single-word split (one code word replaced by its two
children), which is how the atom peel's intermediate codes arise.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
-- `codeChange_mem_stableUnits` is stated over a base field (it carries
-- `include k in`), so the wrappers below have to carry one as well.
variable {k : Type*} [Field k] [Algebra k A]

omit [DecidableEq ι] in
/-- A word family whose members are pairwise incomparable and whose
cylinders sum to `1`, in the list form of the generation theorem. -/
theorem isCompleteCode_of_family (τ : ι → List (Fin 2))
    (hfree : ∀ ⦃i j : ι⦄, i ≠ j → ¬τ i <+: τ j)
    (hsum : ∑ i, L.cylinder (τ i) = 1) :
    L.IsCompleteCode (Finset.univ.toList.map τ) := by
  classical
  constructor
  · rw [List.pairwise_map]
    have hnodup : Finset.univ.toList.Pairwise
        (fun i j : ι ↦ i ≠ j) := Finset.univ.nodup_toList
    exact hnodup.imp fun hne ↦ ⟨hfree hne, hfree (Ne.symm hne)⟩
  · rw [List.map_map]
    have h : (Finset.univ.toList.map
        ((fun w ↦ L.cylinder w) ∘ τ)).sum =
        ∑ i, L.cylinder (τ i) := Finset.sum_map_toList _ _
    rw [h, hsum]

-- `k` is named only in the proof, so it needs including explicitly, while
-- `DecidableEq ι` is never used; both directives must precede the docstring
-- or the doc comment is orphaned from its theorem.
omit [DecidableEq ι] in
include k in
/-- **Indexed code bijections lie in the class group**: the value
`Σᵢ s_{τᵢ} t_{σᵢ}` over complete prefix families `τ`, `σ` is a
code-change unit. -/
theorem codeBijection_mem_stableUnits [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (τ σ : ι → List (Fin 2))
    (hτfree : ∀ ⦃i j : ι⦄, i ≠ j → ¬τ i <+: τ j)
    (hτsum : ∑ i, L.cylinder (τ i) = 1)
    (hσfree : ∀ ⦃i j : ι⦄, i ≠ j → ¬σ i <+: σ j)
    (hσsum : ∑ i, L.cylinder (σ i) = 1)
    (u : Aˣ) (hu : (u : A) = ∑ i, L.wordS (τ i) * L.wordT (σ i)) :
    u ∈ stableUnits A := by
  classical
  refine L.codeChange_mem_stableUnits (k := k) hdiv
    (Finset.univ.toList.map (fun i ↦ (τ i, σ i))).length
    (Finset.univ.toList.map (fun i ↦ (τ i, σ i))) rfl ?_ ?_ u ?_
  · rw [List.map_map]
    exact L.isCompleteCode_of_family σ hσfree hσsum
  · rw [List.map_map]
    exact L.isCompleteCode_of_family τ hτfree hτsum
  · rw [hu]
    unfold pairValue
    rw [List.map_map]
    exact (Finset.sum_map_toList _ _).symm

-- `cylinder_split` is already proved in `LeavittWords.lean` (as
-- `lem:leaf`(iii)) with exactly this statement, and is in scope here, so the
-- copy that stood at this point has been dropped rather than shadowed.

/-- Prefix comparison against a one-letter extension. -/
theorem incomparable_append_single {v w : List (Fin 2)}
    (hvw : ¬v <+: w) (hwv : ¬w <+: v) (z : Fin 2) :
    ¬v <+: w ++ [z] ∧ ¬w ++ [z] <+: v := by
  constructor
  · intro h
    by_cases hlen : v.length ≤ w.length
    · exact hvw (List.prefix_of_prefix_length_le h
        (List.prefix_append w [z]) hlen)
    · have hlen2 : v.length = (w ++ [z]).length := by
        have h1 := h.length_le
        simp only [List.length_append, List.length_singleton] at h1 ⊢
        omega
      have heq := h.eq_of_length hlen2
      refine hwv ?_
      rw [heq]
      exact List.prefix_append w [z]
  · intro h
    exact hwv ((List.prefix_append w [z]).trans h)

omit [Fintype ι] [DecidableEq ι] in
/-- **The split family**: replacing the word at one index of a
complete prefix family by its two children (indexed by
`Bool ⊕ (everything else)`) is again a complete prefix family. -/
theorem split_family_free (τ : ι → List (Fin 2))
    (hfree : ∀ ⦃i j : ι⦄, i ≠ j → ¬τ i <+: τ j) (j₀ : ι) :
    ∀ ⦃p q : Fin 2 ⊕ {i : ι // i ≠ j₀}⦄, p ≠ q →
      ¬(Sum.elim (fun z ↦ τ j₀ ++ [z]) (fun i ↦ τ i.1)) p <+:
        (Sum.elim (fun z ↦ τ j₀ ++ [z]) (fun i ↦ τ i.1)) q := by
  rintro (z₁ | i₁) (z₂ | i₂) hne h
  · -- two children of the same word: distinct letters
    have hz : z₁ ≠ z₂ := fun hz ↦ hne (by rw [hz])
    have hlen : (τ j₀ ++ [z₁]).length = (τ j₀ ++ [z₂]).length := by
      simp
    have heq := h.eq_of_length hlen
    have : z₁ = z₂ := by
      have := List.append_inj_right heq rfl
      simpa using this
    exact hz this
  · -- child versus another word
    have hinc := incomparable_append_single
      (hfree i₂.2) (hfree (Ne.symm i₂.2)) z₁
    exact hinc.2 h
  · -- another word versus child
    have hinc := incomparable_append_single
      (hfree i₁.2) (hfree (Ne.symm i₁.2)) z₂
    exact hinc.1 h
  · -- two other words
    have hne' : i₁.1 ≠ i₂.1 := fun hh ↦
      hne (congrArg Sum.inr (Subtype.ext hh))
    exact hfree hne' h

/-- The split family's cylinders still sum to `1`. -/
theorem split_family_sum (τ : ι → List (Fin 2))
    (hsum : ∑ i, L.cylinder (τ i) = 1) (j₀ : ι) :
    ∑ p : Fin 2 ⊕ {i : ι // i ≠ j₀},
      L.cylinder ((Sum.elim (fun z ↦ τ j₀ ++ [z])
        (fun i ↦ τ i.1)) p) = 1 := by
  classical
  rw [Fintype.sum_sum_type]
  have h1 : ∑ z : Fin 2, L.cylinder (τ j₀ ++ [z]) =
      L.cylinder (τ j₀) := by
    rw [Fin.sum_univ_two]
    exact (L.cylinder_split (τ j₀)).symm
  have h2 : ∑ i : {i : ι // i ≠ j₀}, L.cylinder (τ i.1) =
      ∑ i ∈ Finset.univ.erase j₀, L.cylinder (τ i) :=
    (Finset.sum_subtype (Finset.univ.erase j₀)
      (fun x ↦ by simp [Finset.mem_erase]) (fun i ↦ L.cylinder (τ i))).symm
  -- the two summands still read `Sum.elim … (Sum.inl a)` / `(Sum.inr a)`,
  -- so `h1`/`h2` have nothing to match until those reduce
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [h1, h2, Finset.add_sum_erase _ (fun i ↦ L.cylinder (τ i))
    (Finset.mem_univ j₀)]
  exact hsum

end LeavittFamily
end NonsoficGroupsExist
