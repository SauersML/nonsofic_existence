import NonsoficGroupsExist.CodeChangeGlue

/-!
# Complete prefix codes of every size

Every nonempty finite index type carries a complete prefix family:
start from the root code `{ε}` and repeatedly split one word into its
two children (`split_family_free`, `split_family_sum`), transporting
along index equivalences.  The elimination's intermediate codes are
drawn from this supply.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- Transport of a complete prefix family along an index
equivalence. -/
theorem family_transport {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (w : ι → List (Fin 2))
    (hfree : ∀ ⦃i j : ι⦄, i ≠ j → ¬w i <+: w j)
    (hsum : ∑ i, L.cylinder (w i) = 1) :
    (∀ ⦃p q : ι'⦄, p ≠ q → ¬(w ∘ e) p <+: (w ∘ e) q) ∧
      ∑ p, L.cylinder ((w ∘ e) p) = 1 := by
  constructor
  · intro p q hpq
    exact hfree (fun h ↦ hpq (e.injective h))
  · -- forward direction: rewrite the `e`-indexed sum into the `ι`-indexed one
    rw [Fintype.sum_equiv e (fun p ↦ L.cylinder ((w ∘ e) p))
      (fun i ↦ L.cylinder (w i)) (fun p ↦ rfl)]
    exact hsum

/-- **Complete prefix families of every positive size.** -/
theorem exists_complete_family : ∀ m : ℕ, 1 ≤ m →
    ∃ w : Fin m → List (Fin 2),
      (∀ ⦃i j : Fin m⦄, i ≠ j → ¬w i <+: w j) ∧
      ∑ i, L.cylinder (w i) = 1 := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ n ih =>
      intro _
      by_cases hn : 1 ≤ n
      · obtain ⟨w, hfree, hsum⟩ := ih hn
        set j₀ : Fin n := ⟨0, by omega⟩ with hj₀
        have hfree' := split_family_free w hfree j₀
        have hsum' := L.split_family_sum w hsum j₀
        have hcard : Fintype.card (Fin (n + 1)) =
            Fintype.card (Fin 2 ⊕ {i : Fin n // i ≠ j₀}) := by
          -- `card_subtype_compl` reintroduces `Fintype.card (Fin n)`, which
          -- the earlier `card_fin` rewrites cannot have touched; without a
          -- second pass `omega` sees it as an opaque atom unrelated to `n`.
          rw [Fintype.card_sum, Fintype.card_subtype_compl,
            Fintype.card_subtype_eq]
          simp only [Fintype.card_fin]
          omega
        set e := Fintype.equivOfCardEq hcard with he
        obtain ⟨hf, hs⟩ := L.family_transport e
          (Sum.elim (fun z ↦ w j₀ ++ [z]) (fun i ↦ w i.1))
          hfree' hsum'
        exact ⟨_, hf, hs⟩
      · -- `n = 0`: the root code
        have hn0 : n = 0 := by omega
        subst hn0
        refine ⟨fun _ ↦ [], ?_, ?_⟩
        · intro i j hij
          -- instance search will not reduce `Fin (0 + 1)` to `Fin 1`, so
          -- `Subsingleton` is not found; go through the value instead.
          exact absurd (Fin.ext (by omega)) hij
        · rw [Fin.sum_univ_one]
          show L.wordS [] * L.wordT [] = 1
          rw [wordS_nil, wordT_nil, one_mul]

/-- Every nonempty finite index type carries a complete prefix
family. -/
theorem exists_complete_family_of_nonempty (ι' : Type*) [Fintype ι']
    [Nonempty ι'] :
    ∃ w : ι' → List (Fin 2),
      (∀ ⦃p q : ι'⦄, p ≠ q → ¬w p <+: w q) ∧
      ∑ p, L.cylinder (w p) = 1 := by
  obtain ⟨w, hfree, hsum⟩ := L.exists_complete_family
    (Fintype.card ι') Fintype.card_pos
  obtain ⟨hf, hs⟩ := L.family_transport (Fintype.equivFin ι') w
    hfree hsum
  exact ⟨_, hf, hs⟩

end LeavittFamily
end NonsoficGroupsExist
