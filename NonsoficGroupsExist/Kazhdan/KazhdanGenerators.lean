import NonsoficGroupsExist.Kazhdan.Kazhdan
import NonsoficGroupsExist.Matching.GeneratorWords

/-!
# Property (T) on a prescribed finite generating set

Property `(T)` supplies some finite Kazhdan set.  A word-length triangle
inequality transfers its tolerance to any prescribed finite symmetric
generating set.  This is needed to run Kun's theorem on the concrete generator
sets occurring in the compression construction.
-/

namespace NonsoficGroupsExist

universe u v

namespace KazhdanGenerators

variable {G : Type u} [Group G]

theorem word_displacement_le
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (S : Finset G) (δ : ℝ)
    (w : List G) (hw : ∀ g ∈ w, g ∈ S)
    (hnear : ∀ g ∈ S, ‖ρ g x - x‖ ≤ δ) :
    ‖ρ w.prod x - x‖ ≤ w.length * δ := by
  induction w with
  | nil => simp
  | cons g w ih =>
      have hgS : g ∈ S := hw g (by simp)
      have hwmem : ∀ a ∈ w, a ∈ S := by
        intro a ha
        exact hw a (by simp [ha])
      have htri : ‖ρ (g * w.prod) x - x‖ ≤
          ‖ρ g (ρ w.prod x) - ρ g x‖ + ‖ρ g x - x‖ := by
        calc
          ‖ρ (g * w.prod) x - x‖ =
              ‖ρ g (ρ w.prod x) - x‖ := by rw [map_mul]; rfl
          _ = ‖(ρ g (ρ w.prod x) - ρ g x) + (ρ g x - x)‖ := by
            congr 1
            abel
          _ ≤ ‖ρ g (ρ w.prod x) - ρ g x‖ + ‖ρ g x - x‖ :=
            norm_add_le _ _
      have hisometry : ‖ρ g (ρ w.prod x) - ρ g x‖ =
          ‖ρ w.prod x - x‖ := by
        rw [← (ρ g).map_sub]
        exact (ρ g).norm_map _
      rw [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        ‖ρ (g * w.prod) x - x‖ ≤
            ‖ρ g (ρ w.prod x) - ρ g x‖ + ‖ρ g x - x‖ := htri
        _ = ‖ρ w.prod x - x‖ + ‖ρ g x - x‖ := by rw [hisometry]
        _ ≤ (w.length : ℝ) * δ + δ := add_le_add (ih hwmem) (hnear g hgS)
        _ = ((w.length : ℝ) + 1) * δ := by ring

/-- Every finite symmetric generating set of a property-`(T)` group admits a
positive Kazhdan tolerance. -/
theorem exists_pair_on_generators
    (hT : HasKazhdanPropertyT.{u, v} G)
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) :
    ∃ δ : ℝ, IsKazhdanPair.{u, v} G S δ := by
  classical
  obtain ⟨Q, ε, hQ⟩ := hT
  let word : G → List G := fun q ↦
    Classical.choose (exists_generator_word (G := G) S hsymm hgen q)
  have hwordMem (q : G) : ∀ g ∈ word q, g ∈ S :=
    (Classical.choose_spec (exists_generator_word (G := G) S hsymm hgen q)).1
  have hwordProd (q : G) : (word q).prod = q :=
    (Classical.choose_spec (exists_generator_word (G := G) S hsymm hgen q)).2
  let L : ℕ := ∑ q : Q, (word q.1).length
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hQ.1 (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro E _ _ _ ρ x hx hnear
  apply hQ.2 E ρ x hx
  intro q hq
  let q' : Q := ⟨q, hq⟩
  have hlength : (word q).length ≤ L := by
    dsimp [L]
    exact Finset.single_le_sum (fun i _ ↦ Nat.zero_le (word i.1).length)
      (Finset.mem_univ q')
  have hnearLe : ∀ g ∈ S, ‖ρ g x - x‖ ≤ δ := by
    intro g hg
    exact (hnear g hg).le
  have hword := word_displacement_le ρ x S δ (word q)
    (hwordMem q) hnearLe
  rw [hwordProd q] at hword
  have hlengthReal : ((word q).length : ℝ) ≤ L := by exact_mod_cast hlength
  have hL : (0 : ℝ) ≤ L := by positivity
  have hbound : (word q).length * δ ≤ L * δ :=
    mul_le_mul_of_nonneg_right hlengthReal hδ.le
  have hstrict : (L : ℝ) * δ < ε := by
    dsimp [δ]
    rw [div_eq_mul_inv]
    have hden : (0 : ℝ) < L + 1 := by positivity
    have hfrac : (L : ℝ) / (L + 1) < 1 := by
      exact (div_lt_one hden).2 (by linarith)
    rw [div_eq_mul_inv] at hfrac
    nlinarith [hQ.1]
  exact hword.trans_lt (hbound.trans_lt hstrict)

end KazhdanGenerators
end NonsoficGroupsExist
