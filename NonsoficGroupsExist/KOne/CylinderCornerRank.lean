import NonsoficGroupsExist.KOne.DegreeShapeBridge

/-!
# Rank certificates for cylinder-sum idempotents

A depth-`n` cylinder sum `f = Σ_{γ ∈ T} p_γ` is represented at every
interface `ℓ ≥ n` by a matrix whose rank is exactly `|T|·2^{ℓ-n}`:
compressing between the words extending `T` exhibits an identity
matrix of that size inside any representing matrix (lower bound),
while the isometry factorizations `p_γ = s_γ·t_γ` bound the rank of
each summand by the width of the middle interface (upper bound).
These are the two halves of the rank bookkeeping in the vanishing of
the rose-graph `K₁`.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- Concatenation of function-words. -/
def appendFun {n r ℓ : ℕ} (h : n + r = ℓ) (γ : Fin n → Fin 2)
    (δ : Fin r → Fin 2) : Fin ℓ → Fin 2 := fun i ↦
  if hi : (i : ℕ) < n then γ ⟨i, hi⟩ else
    δ ⟨(i : ℕ) - n, by omega⟩

theorem ofFn_appendFun {n r ℓ : ℕ} (h : n + r = ℓ)
    (γ : Fin n → Fin 2) (δ : Fin r → Fin 2) :
    List.ofFn (appendFun h γ δ) = List.ofFn γ ++ List.ofFn δ := by
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_append]
    omega
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    rw [List.getElem_append]
    by_cases hi : i < n
    · rw [dif_pos (by simpa [List.length_ofFn] using hi)]
      simp [appendFun, hi]
    · rw [dif_neg (by simpa [List.length_ofFn] using hi)]
      simp [appendFun, hi, List.length_ofFn]

theorem appendFun_injective {n r ℓ : ℕ} (h : n + r = ℓ)
    {γ γ' : Fin n → Fin 2} {δ δ' : Fin r → Fin 2}
    (heq : appendFun h γ δ = appendFun h γ' δ') :
    γ = γ' ∧ δ = δ' := by
  have hl := (ofFn_appendFun h γ δ).symm.trans
    ((congrArg List.ofFn heq).trans (ofFn_appendFun h γ' δ'))
  have h1 : List.ofFn γ = List.ofFn γ' :=
    List.append_inj_left hl (by simp [List.length_ofFn])
  have h2 : List.ofFn δ = List.ofFn δ' :=
    List.append_inj_right hl (by simp [List.length_ofFn])
  exact ⟨List.ofFn_injective h1, List.ofFn_injective h2⟩

/-- The core compression computation: conjugating a cylinder sum by
concatenated words produces Kronecker deltas. -/
theorem wordT_cylSum_wordS {n : ℕ} (T : Finset (Fin n → Fin 2))
    {r : ℕ} (γ γ' : Fin n → Fin 2) (δ δ' : Fin r → Fin 2) :
    L.wordT (List.ofFn γ ++ List.ofFn δ) *
      (∑ α ∈ T, L.cylinder (List.ofFn α)) *
      L.wordS (List.ofFn γ' ++ List.ofFn δ') =
    if γ = γ' ∧ δ = δ' ∧ γ ∈ T then 1 else 0 := by
  classical
  have horthN : ∀ a b : Fin n → Fin 2,
      L.wordT (List.ofFn a) * L.wordS (List.ofFn b) =
        if a = b then 1 else 0 :=
    fun a b ↦ L.prefixCode_orthogonal (fullBinaryCode n) a b
  have horthR : ∀ a b : Fin r → Fin 2,
      L.wordT (List.ofFn a) * L.wordS (List.ofFn b) =
        if a = b then 1 else 0 :=
    fun a b ↦ L.prefixCode_orthogonal (fullBinaryCode r) a b
  rw [Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ α ∈ T,
      L.wordT (List.ofFn γ ++ List.ofFn δ) *
        L.cylinder (List.ofFn α) *
        L.wordS (List.ofFn γ' ++ List.ofFn δ') =
      if α = γ ∧ γ = γ' ∧ δ = δ' then 1 else 0 := by
    intro α _
    rw [L.wordT_append, L.wordS_append, cylinder]
    rw [show L.wordT (List.ofFn δ) * L.wordT (List.ofFn γ) *
        (L.wordS (List.ofFn α) * L.wordT (List.ofFn α)) *
        (L.wordS (List.ofFn γ') * L.wordS (List.ofFn δ')) =
      L.wordT (List.ofFn δ) *
        ((L.wordT (List.ofFn γ) * L.wordS (List.ofFn α)) *
          (L.wordT (List.ofFn α) * L.wordS (List.ofFn γ'))) *
        L.wordS (List.ofFn δ') from by noncomm_ring,
      horthN γ α, horthN α γ']
    by_cases h1 : γ = α
    · by_cases h2 : α = γ'
      · rw [if_pos h1, if_pos h2, one_mul, mul_one, horthR δ δ']
        by_cases h3 : δ = δ'
        · rw [if_pos h3, if_pos ⟨h1.symm, h1.trans h2, h3⟩]
        · rw [if_neg h3, if_neg (fun hc ↦ h3 hc.2.2)]
      · rw [if_pos h1, if_neg h2,
          show L.wordT (List.ofFn δ) * ((1 : A) * 0) *
            L.wordS (List.ofFn δ') = 0 from by noncomm_ring,
          if_neg (fun hc ↦ h2 (hc.1.trans hc.2.1))]
    · rw [if_neg h1,
        show L.wordT (List.ofFn δ) *
          ((0 : A) * (if α = γ' then (1 : A) else 0)) *
          L.wordS (List.ofFn δ') = 0 from by noncomm_ring,
        if_neg (fun hc ↦ h1 hc.1.symm)]
  rw [Finset.sum_congr rfl hterm]
  by_cases hγT : γ ∈ T
  · rw [Finset.sum_eq_single γ]
    · by_cases h2 : γ = γ' ∧ δ = δ'
      · rw [if_pos ⟨rfl, h2.1, h2.2⟩, if_pos ⟨h2.1, h2.2, hγT⟩]
      · rw [if_neg (by tauto), if_neg (by tauto)]
    · intro α _ hα
      rw [if_neg (by tauto)]
    · intro hγ
      exact absurd hγT hγ
  · rw [if_neg (by tauto)]
    refine Finset.sum_eq_zero fun α hα ↦ ?_
    rw [if_neg ?_]
    rintro ⟨rfl, -, -⟩
    exact hγT hα

variable {k : Type*} [Field k] [Algebra k A]

/-- Cylinder sums lie in every square shape span at depth `≥ n`. -/
theorem cylSum_mem_shapeSpan {n : ℕ} (T : Finset (Fin n → Fin 2))
    {m : ℕ} (hm : n ≤ m) :
    (∑ γ ∈ T, L.cylinder (List.ofFn γ)) ∈
      Submodule.span k (L.shapeMonomials m m) := by
  refine Submodule.sum_mem _ fun γ _ ↦ ?_
  have h := L.monomial_mem_shapeSpan (k := k) (List.ofFn γ)
    (List.ofFn γ) (m - n)
  have hlen : (List.ofFn γ).length + (m - n) = m := by
    simp only [List.length_ofFn]
    omega
  rw [hlen] at h
  exact h

/-- **Lower rank certificate**: any matrix representing the cylinder
sum at interface `ℓ` has rank at least `|T|·2^{ℓ-n}`. -/
theorem card_le_rank_of_shapeRep_cylSum [Nontrivial A] {n ℓ : ℕ}
    (T : Finset (Fin n → Fin 2)) (hℓ : n ≤ ℓ)
    {M : Matrix (Fin ℓ → Fin 2) (Fin ℓ → Fin 2) k}
    (hM : L.ShapeRep ℓ ℓ M (∑ γ ∈ T, L.cylinder (List.ofFn γ))) :
    T.card * 2 ^ (ℓ - n) ≤ M.rank := by
  classical
  set ι : Type _ := {γ // γ ∈ T} × (Fin (ℓ - n) → Fin 2) with hι
  have hsum : n + (ℓ - n) = ℓ := by omega
  set wf : ι → (Fin ℓ → Fin 2) :=
    fun p ↦ appendFun hsum p.1.1 p.2 with hwf
  -- entries of M at concatenated words
  have hentry : ∀ p p' : ι, M (wf p) (wf p') =
      if p = p' then 1 else 0 := by
    intro p p'
    apply (algebraMap k A).injective
    rw [← L.shapeRep_entry hM (wf p) (wf p')]
    simp only [hwf]
    rw [ofFn_appendFun, ofFn_appendFun,
      L.wordT_cylSum_wordS T p.1.1 p'.1.1 p.2 p'.2]
    by_cases hp : p = p'
    · rw [if_pos hp, if_pos (by
        refine ⟨?_, ?_, p.1.2⟩ <;> rw [hp]), map_one]
    · rw [if_neg hp, if_neg ?_, map_zero]
      rintro ⟨h1, h2, -⟩
      exact hp (Prod.ext (Subtype.ext h1) h2)
  set U : Matrix ι (Fin ℓ → Fin 2) k :=
    Matrix.of fun p w ↦ if w = wf p then 1 else 0 with hU
  set V : Matrix (Fin ℓ → Fin 2) ι k :=
    Matrix.of fun w p ↦ if w = wf p then 1 else 0 with hV
  have hUMV : U * M * V = 1 := by
    ext p p'
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (wf p')]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (wf p)]
      · rw [hU, hV]
        simp [hentry p p', Matrix.one_apply]
      · intro w _ hw
        rw [hU]
        simp only [Matrix.of_apply, if_neg hw]
        rw [zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · intro w _ hw
      rw [hV]
      simp only [Matrix.of_apply, if_neg hw]
      rw [mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  have hcard : Fintype.card ι = T.card * 2 ^ (ℓ - n) := by
    show Fintype.card ({γ // γ ∈ T} × (Fin (ℓ - n) → Fin 2)) = _
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
  calc (T.card * 2 ^ (ℓ - n) : ℕ)
      = Fintype.card ι := hcard.symm
    _ = (1 : Matrix ι ι k).rank := (Matrix.rank_one).symm
    _ = (U * M * V).rank := by rw [hUMV]
    _ ≤ (U * M).rank := Matrix.rank_mul_le_left _ _
    _ ≤ M.rank := Matrix.rank_mul_le_right _ _

/-- **Upper rank certificate**: any matrix representing the cylinder
sum at interface `m` has rank at most `|T|·2^{m-n}`. -/
theorem rank_le_card_of_shapeRep_cylSum [Nontrivial A] {n m : ℕ}
    (T : Finset (Fin n → Fin 2)) (hm : n ≤ m)
    {M : Matrix (Fin m → Fin 2) (Fin m → Fin 2) k}
    (hM : L.ShapeRep m m M (∑ γ ∈ T, L.cylinder (List.ofFn γ))) :
    M.rank ≤ T.card * 2 ^ (m - n) := by
  classical
  -- per-cylinder isometry factorization
  have hfac : ∀ γ : Fin n → Fin 2, ∃
      (P : Matrix (Fin m → Fin 2) (Fin (m - n) → Fin 2) k)
      (Q : Matrix (Fin (m - n) → Fin 2) (Fin m → Fin 2) k),
      L.ShapeRep m m (P * Q) (L.cylinder (List.ofFn γ)) := by
    intro γ
    have hs : L.wordS (List.ofFn γ) ∈
        Submodule.span k (L.shapeMonomials m (m - n)) := by
      have h := L.monomial_mem_shapeSpan (k := k) (List.ofFn γ) []
        (m - n)
      rw [show L.wordS (List.ofFn γ) * L.wordT [] =
        L.wordS (List.ofFn γ) from by simp] at h
      have hlen : (List.ofFn γ).length + (m - n) = m := by
        simp only [List.length_ofFn]; omega
      rw [hlen] at h
      rw [show ([] : List (Fin 2)).length + (m - n) = m - n from by
        simp] at h
      exact h
    have ht : L.wordT (List.ofFn γ) ∈
        Submodule.span k (L.shapeMonomials (m - n) m) := by
      have h := L.monomial_mem_shapeSpan (k := k) []
        (List.ofFn γ) (m - n)
      rw [show L.wordS [] * L.wordT (List.ofFn γ) =
        L.wordT (List.ofFn γ) from by simp] at h
      have hlen : (List.ofFn γ).length + (m - n) = m := by
        simp only [List.length_ofFn]; omega
      rw [hlen] at h
      rw [show ([] : List (Fin 2)).length + (m - n) = m - n from by
        simp] at h
      exact h
    obtain ⟨P, hP⟩ := L.exists_shapeRep hs
    obtain ⟨Q, hQ⟩ := L.exists_shapeRep ht
    exact ⟨P, Q, by rw [cylinder]; exact L.shapeRep_mul hP hQ⟩
  choose P Q hPQ using hfac
  have hsumrep : L.ShapeRep m m (∑ γ ∈ T, P γ * Q γ)
      (∑ γ ∈ T, L.cylinder (List.ofFn γ)) :=
    L.shapeRep_finsetSum T _ _ fun γ _ ↦ hPQ γ
  have hMe : M = ∑ γ ∈ T, P γ * Q γ :=
    L.shapeRep_unique (algebraMap k A).injective hM hsumrep
  rw [hMe]
  calc (∑ γ ∈ T, P γ * Q γ).rank
      ≤ ∑ γ ∈ T, (P γ * Q γ).rank := rank_finsetSum_le T _
    _ ≤ ∑ _γ ∈ T, 2 ^ (m - n) := by
        refine Finset.sum_le_sum fun γ _ ↦ ?_
        calc (P γ * Q γ).rank ≤ (P γ).rank :=
              Matrix.rank_mul_le_left _ _
          _ ≤ Fintype.card (Fin (m - n) → Fin 2) :=
              Matrix.rank_le_card_width _
          _ = 2 ^ (m - n) := by
              rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    _ = T.card * 2 ^ (m - n) := by
        rw [Finset.sum_const, smul_eq_mul]

end LeavittFamily
end NonsoficGroupsExist
