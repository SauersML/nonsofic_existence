import NonsoficGroupsExist.KOne.GradedComponents
import NonsoficGroupsExist.Leavitt.RankNormalForm
import NonsoficGroupsExist.KOne.CylinderCornerRank
import NonsoficGroupsExist.KOne.NilpotentTailKill

/-!
# The keystone: balanced parts of `[0,1]`-window units are invertible

If `c + ζ` is a unit of the binary Leavitt algebra with `c` balanced
and `ζ` of pure degree `1`, then `c` is invertible.  Otherwise the
rank normal form turns the unit into `e + ζ'` with `e` a proper
cylinder-sum idempotent and `f := 1 - e` a nonempty cylinder sum;
the graded components of the inverse satisfy a two-term recursion
whose downward elimination produces the corner identity
`f = Σ_j (f·ζ'·(-ζ')^j)·(f·(y_{-1-j}·f))`, and at a deep interface the
right side factors through spaces of geometrically decaying dimension:
`|T|·2^{ℓ-n} ≤ Σ_{j<M} |T|·2^{ℓ-n-1-j} < |T|·2^{ℓ-n}` — impossible.
This is the elementary replacement for the `K₁`-vanishing input of
the manuscript.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily

variable (k : Type) [Field k]

/-- Geometric sums of powers of two. -/
private theorem sum_two_pow (m : ℕ) :
    (∑ i ∈ Finset.range m, 2 ^ i) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega

/-- **Balanced parts of `[0,1]`-window units are invertible.** -/
theorem balanced_component_isUnit [Nontrivial (BinaryLeavittAlgebra k)]
    {c ζ : BinaryLeavittAlgebra k}
    (hc : c ∈ Submodule.span k ((family k).degreeMonomials 0 0))
    (hζ : ζ ∈ Submodule.span k ((family k).degreeMonomials 1 1))
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) = c + ζ) : IsUnit c := by
  classical
  by_contra hcu
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  -- rank-normalize the balanced part
  obtain ⟨n, hcn⟩ := L.span_degree_zero_le_levelSpan hc
  obtain ⟨g, h, S, hgv, hgi, hhv, hhi, hgch, hSU⟩ :=
    L.exists_rank_normal_form hcn
  have hSne : S ≠ Finset.univ := fun hS ↦ hcu (hSU hS)
  set T : Finset (Fin n → Fin 2) := Finset.univ \ S with hT
  have hTpos : 0 < T.card := by
    refine Finset.card_pos.mpr (Finset.sdiff_nonempty.mpr ?_)
    intro hsub
    exact hSne (Finset.univ_subset_iff.mp hsub)
  set e : BinaryLeavittAlgebra k := ∑ γ ∈ S, L.cylinder (List.ofFn γ)
    with he
  set f : BinaryLeavittAlgebra k := ∑ γ ∈ T, L.cylinder (List.ofFn γ)
    with hf
  have hef : e + f = 1 := by
    rw [he, hf, hT, add_comm]
    rw [Finset.sum_sdiff (Finset.subset_univ S)]
    exact L.fullBinaryCode_complete n
  -- cylinder orthogonality
  have hcyl : ∀ γ δ : Fin n → Fin 2,
      L.cylinder (List.ofFn γ) * L.cylinder (List.ofFn δ) =
      if γ = δ then L.cylinder (List.ofFn γ) else 0 := by
    intro γ δ
    have horth : L.wordT (List.ofFn γ) * L.wordS (List.ofFn δ) =
        if γ = δ then 1 else 0 :=
      L.prefixCode_orthogonal (fullBinaryCode n) γ δ
    unfold cylinder
    rw [show L.wordS (List.ofFn γ) * L.wordT (List.ofFn γ) *
        (L.wordS (List.ofFn δ) * L.wordT (List.ofFn δ)) =
      L.wordS (List.ofFn γ) *
        (L.wordT (List.ofFn γ) * L.wordS (List.ofFn δ)) *
        L.wordT (List.ofFn δ) from by noncomm_ring,
      horth]
    by_cases hγδ : γ = δ
    · rw [if_pos hγδ, if_pos hγδ, mul_one, hγδ]
    · rw [if_neg hγδ, if_neg hγδ]
      noncomm_ring
  have hfe : f * e = 0 := by
    rw [hf, he, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun γ hγ ↦
      Finset.sum_eq_zero fun δ hδ ↦ ?_
    rw [hcyl γ δ, if_neg ?_]
    rintro rfl
    rw [hT] at hγ
    exact (Finset.mem_sdiff.mp hγ).2 hδ
  have hff : f * f = f := by
    rw [hf, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun γ hγ ↦ ?_
    rw [Finset.sum_eq_single γ]
    · rw [hcyl γ γ, if_pos rfl]
    · intro δ _ hδ
      rw [hcyl γ δ, if_neg (Ne.symm hδ)]
    · intro hγ'
      exact absurd hγ hγ'
  -- the normalized unit
  set w : (BinaryLeavittAlgebra k)ˣ := g * u * h with hw
  set ζ' : BinaryLeavittAlgebra k := (g : BinaryLeavittAlgebra k) * ζ *
    (h : BinaryLeavittAlgebra k) with hζ'def
  have hwv : (w : BinaryLeavittAlgebra k) = e + ζ' := by
    rw [hw]
    show (g : BinaryLeavittAlgebra k) * (u : BinaryLeavittAlgebra k) *
      (h : BinaryLeavittAlgebra k) = e + ζ'
    rw [hu]
    rw [show (g : BinaryLeavittAlgebra k) * (c + ζ) *
        (h : BinaryLeavittAlgebra k) =
      (g : BinaryLeavittAlgebra k) * c * (h : BinaryLeavittAlgebra k) +
      (g : BinaryLeavittAlgebra k) * ζ * (h : BinaryLeavittAlgebra k)
      from by noncomm_ring, hgch, hζ'def, he]
  -- degree memberships
  have hgd : (g : BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.degreeMonomials 0 0) :=
    L.span_levelMonomials_le_degree n hgv
  have hhd : (h : BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.degreeMonomials 0 0) :=
    L.span_levelMonomials_le_degree n hhv
  have hζ'd : ζ' ∈ Submodule.span k (L.degreeMonomials 1 1) := by
    rw [hζ'def]
    have h1 := L.window_mul_mem_span (k := k)
      (L.window_mul_mem_span (k := k) hgd hζ) hhd
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hed : e ∈ Submodule.span k (L.degreeMonomials 0 0) := by
    rw [he]
    refine Submodule.sum_mem _ fun γ _ ↦ Submodule.subset_span
      ⟨List.ofFn γ, List.ofFn γ, by simp, by simp, rfl⟩
  -- graded components of the inverse
  obtain ⟨lo₀, hi₀, hx₀⟩ := exists_mem_span_degreeMonomials k
    ((w⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k)
  set lo : ℤ := min lo₀ (-1) with hlo
  set hi : ℤ := max hi₀ 0 with hhi
  have hlo1 : lo ≤ -1 := min_le_right _ _
  have hhi1 : (0 : ℤ) ≤ hi := le_max_right _ _
  have hx : ((w⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.degreeMonomials lo hi) :=
    L.span_degreeMonomials_mono (min_le_left _ _) (le_max_left _ _) hx₀
  obtain ⟨y, hymem, hysupp, hysum⟩ := exists_components k hx
  set D : Finset ℤ := Finset.Icc lo (hi + 1) with hD
  have h0D : (0 : ℤ) ∈ D := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  -- componentwise unit equations
  have hzmem : ∀ d ∈ D, e * y d + ζ' * y (d - 1) ∈
      Submodule.span k (L.degreeMonomials d d) := by
    intro d _
    refine Submodule.add_mem _ ?_ ?_
    · have := L.window_mul_mem_span (k := k) hed (hymem d)
      refine L.span_degreeMonomials_mono ?_ ?_ this <;> omega
    · have := L.window_mul_mem_span (k := k) hζ'd (hymem (d - 1))
      refine L.span_degreeMonomials_mono ?_ ?_ this <;> omega
  have hz'mem : ∀ d ∈ D,
      (if d = 0 then (1 : BinaryLeavittAlgebra k) else 0) ∈
      Submodule.span k (L.degreeMonomials d d) := by
    intro d _
    by_cases hd : d = 0
    · rw [if_pos hd]
      exact Submodule.subset_span
        ⟨[], [], by simp [hd], by simp [hd], by simp⟩
    · rw [if_neg hd]
      exact Submodule.zero_mem _
  have hshift : ∑ d ∈ D, y (d - 1) =
      ((w⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) := by
    have hmap : D = Finset.map (addRightEmbedding (1 : ℤ))
        (Finset.Icc (lo - 1) hi) := by
      rw [Finset.map_add_right_Icc,
        show lo - 1 + 1 = lo from by ring]
    rw [hmap, Finset.sum_map]
    have hstep : ∀ d ∈ Finset.Icc (lo - 1) hi,
        y (addRightEmbedding (1 : ℤ) d - 1) = y d := by
      intro d _
      congr 1
      simp [addRightEmbedding]
    rw [Finset.sum_congr rfl hstep]
    have hins : Finset.Icc (lo - 1) hi =
        insert (lo - 1) (Finset.Icc lo hi) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega),
      hysupp (lo - 1) (Or.inl (by omega)), zero_add, hysum]
  have hplain : ∑ d ∈ D, y d =
      ((w⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) := by
    have hins : D = insert (hi + 1) (Finset.Icc lo hi) := by
      ext d
      simp only [hD, Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega),
      hysupp (hi + 1) (Or.inr (by omega)), zero_add, hysum]
  have hsum1 : ∑ d ∈ D, (e * y d + ζ' * y (d - 1)) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hplain, hshift]
    calc e * ((w⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k) +
          ζ' * ((w⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k)
        = (e + ζ') * ((w⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k) := by noncomm_ring
      _ = (w : BinaryLeavittAlgebra k) *
          ((w⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k) := by rw [hwv]
      _ = 1 := w.mul_inv
  have hsum2 : ∑ d ∈ D,
      (if d = 0 then (1 : BinaryLeavittAlgebra k) else 0) = 1 := by
    rw [Finset.sum_ite_eq' D (0 : ℤ)
      (fun _ ↦ (1 : BinaryLeavittAlgebra k)), if_pos h0D]
  have heq := components_unique k hzmem hz'mem (hsum1.trans hsum2.symm)
  -- the substitution identity for negative degrees
  have hsubst : ∀ d : ℤ, d ≤ -1 →
      y d = f * y d - ζ' * y (d - 1) := by
    intro d hd
    by_cases hdD : d ∈ D
    · have h1 := heq d hdD
      rw [if_neg (by omega)] at h1
      have h2 : e * y d = -(ζ' * y (d - 1)) :=
        add_eq_zero_iff_eq_neg.mp h1
      calc y d = (e + f) * y d := by rw [hef, one_mul]
        _ = e * y d + f * y d := by noncomm_ring
        _ = f * y d - ζ' * y (d - 1) := by
            rw [h2]
            noncomm_ring
    · have h0 : y d = 0 := hysupp d (by
        rw [hD] at hdD
        simp only [Finset.mem_Icc] at hdD
        omega)
      have h0' : y (d - 1) = 0 := hysupp (d - 1) (by
        rw [hD] at hdD
        simp only [Finset.mem_Icc] at hdD
        omega)
      rw [h0, h0', mul_zero, mul_zero, sub_zero]
  -- the remainder induction
  set GG : ℕ → BinaryLeavittAlgebra k :=
    fun j ↦ f * ζ' * (-ζ') ^ j with hGG
  set YY : ℕ → BinaryLeavittAlgebra k :=
    fun j ↦ f * (y (-1 - (j : ℤ)) * f) with hYY
  have hclaim : ∀ m : ℕ, f =
      (∑ j ∈ Finset.range m, GG j * YY j) +
        f * ζ' * (-ζ') ^ m * y (-1 - (m : ℤ)) * f := by
    intro m
    induction m with
    | zero =>
        have h1 := heq 0 h0D
        rw [if_pos rfl] at h1
        have h2 := congrArg (fun z ↦ f * z * f) h1
        rw [show f * (e * y 0 + ζ' * y (0 - 1)) * f =
            (f * e) * (y 0 * f) + f * ζ' * y (0 - 1) * f from by
              noncomm_ring,
          hfe, zero_mul, zero_add, mul_one, hff] at h2
        rw [Finset.sum_range_zero, zero_add, pow_zero, mul_one]
        rw [show (-1 - ((0 : ℕ) : ℤ)) = 0 - 1 from by omega]
        exact h2.symm
    | succ m ih =>
        refine ih.trans ?_
        rw [Finset.sum_range_succ]
        have hexp := hsubst (-1 - (m : ℤ)) (by omega)
        have h3 := congrArg
          (fun z ↦ f * ζ' * (-ζ') ^ m * z * f) hexp
        have hpow0 : (-ζ') ^ (m + 1) + (-ζ') ^ m * ζ' = 0 := by
          rw [pow_succ, ← mul_add, neg_add_cancel, mul_zero]
        have hzero : f * ζ' * (-ζ') ^ (m + 1) *
              y (-1 - ((m + 1 : ℕ) : ℤ)) * f +
            f * ζ' * (-ζ') ^ m * (ζ' * y (-1 - (m : ℤ) - 1)) * f = 0
            := by
          rw [show (-1 - ((m + 1 : ℕ) : ℤ)) = -1 - (m : ℤ) - 1 from by
            omega]
          calc f * ζ' * (-ζ') ^ (m + 1) * y (-1 - (m : ℤ) - 1) * f +
                f * ζ' * (-ζ') ^ m * (ζ' * y (-1 - (m : ℤ) - 1)) * f
              = f * ζ' * ((-ζ') ^ (m + 1) + (-ζ') ^ m * ζ') *
                  y (-1 - (m : ℤ) - 1) * f := by noncomm_ring
            _ = 0 := by rw [hpow0, mul_zero, zero_mul, zero_mul]
        have hrem : f * ζ' * (-ζ') ^ (m + 1) *
            y (-1 - ((m + 1 : ℕ) : ℤ)) * f =
            -(f * ζ' * (-ζ') ^ m * (ζ' * y (-1 - (m : ℤ) - 1)) * f)
            := eq_neg_of_add_eq_zero_left hzero
        have hstep : f * ζ' * (-ζ') ^ m * y (-1 - (m : ℤ)) * f =
            GG m * YY m -
            f * ζ' * (-ζ') ^ m * (ζ' * y (-1 - (m : ℤ) - 1)) * f := by
          rw [h3]
          simp only [hGG, hYY]
          rw [mul_sub, sub_mul]
          congr 1
          noncomm_ring
        rw [hstep, hrem]
        abel
  -- termination of the expansion
  set M : ℕ := (-lo).toNat with hM
  have hstar : f = ∑ j ∈ Finset.range M, GG j * YY j := by
    have h1 := hclaim M
    rw [hysupp (-1 - (M : ℤ)) (Or.inl (by omega)), mul_zero,
      zero_mul, add_zero] at h1
    exact h1
  -- degree memberships of the corner factors
  have hfd : f ∈ Submodule.span k (L.degreeMonomials 0 0) := by
    rw [hf]
    refine Submodule.sum_mem _ fun γ _ ↦ Submodule.subset_span
      ⟨List.ofFn γ, List.ofFn γ, by simp, by simp, rfl⟩
  have hGGd : ∀ j : ℕ, GG j ∈
      Submodule.span k (L.degreeMonomials ((j : ℤ) + 1) ((j : ℤ) + 1))
      := by
    intro j
    rw [hGG]
    have hpow : (-ζ') ^ j ∈
        Submodule.span k (L.degreeMonomials (j : ℤ) (j : ℤ)) :=
      L.pow_mem_window (Submodule.neg_mem _ hζ'd) j
    have h1 := L.window_mul_mem_span (k := k)
      (L.window_mul_mem_span (k := k) hfd hζ'd) hpow
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hYYd : ∀ j : ℕ, YY j ∈
      Submodule.span k
        (L.degreeMonomials (-1 - (j : ℤ)) (-1 - (j : ℤ))) := by
    intro j
    rw [hYY]
    have h1 := L.window_mul_mem_span (k := k) hfd
      (L.window_mul_mem_span (k := k) (hymem (-1 - (j : ℤ))) hfd)
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  -- choose a deep uniform interface
  have hGsh : ∀ j : ℕ, ∃ n₀ : ℕ, ∀ p q : ℕ, n₀ ≤ q →
      (p : ℤ) = (q : ℤ) + ((j : ℤ) + 1) →
      GG j ∈ Submodule.span k (L.shapeMonomials p q) :=
    fun j ↦ L.exists_shapeSpan_of_degreeSpan (hGGd j)
  have hRsh : ∀ j : ℕ, ∃ n₀ : ℕ, ∀ p q : ℕ, n₀ ≤ q →
      (p : ℤ) = (q : ℤ) + (-1 - (j : ℤ)) →
      y (-1 - (j : ℤ)) * f ∈
        Submodule.span k (L.shapeMonomials p q) := by
    intro j
    refine L.exists_shapeSpan_of_degreeSpan ?_
    have h1 := L.window_mul_mem_span (k := k)
      (hymem (-1 - (j : ℤ))) hfd
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  choose nG hnG using hGsh
  choose nR hnR using hRsh
  set B : ℕ := (Finset.range M).sup fun j ↦ max (nG j) (nR j) with hB
  set ℓ : ℕ := n + M + 1 + B with hℓ
  set K : ℕ := ℓ - n - 1 with hK
  have hKM : M ≤ K := by omega
  -- shape representations at the uniform interface
  have hreps : ∀ j ∈ Finset.range M, ∃
      (MG : Matrix (Fin ℓ → Fin 2) (Fin (ℓ - 1 - j) → Fin 2) k)
      (Mf : Matrix (Fin (ℓ - 1 - j) → Fin 2)
        (Fin (ℓ - 1 - j) → Fin 2) k)
      (Mr : Matrix (Fin (ℓ - 1 - j) → Fin 2) (Fin ℓ → Fin 2) k),
      L.ShapeRep ℓ ℓ (MG * (Mf * Mr)) (GG j * YY j) ∧
      L.ShapeRep (ℓ - 1 - j) (ℓ - 1 - j) Mf f := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hjB : max (nG j) (nR j) ≤ B :=
      Finset.le_sup (f := fun j ↦ max (nG j) (nR j)) hj
    have hq : n ≤ ℓ - 1 - j := by omega
    have hGmem : GG j ∈
        Submodule.span k (L.shapeMonomials ℓ (ℓ - 1 - j)) := by
      refine hnG j ℓ (ℓ - 1 - j) (by omega) ?_
      omega
    have hfmem : f ∈ Submodule.span k
        (L.shapeMonomials (ℓ - 1 - j) (ℓ - 1 - j)) := by
      rw [hf]
      exact L.cylSum_mem_shapeSpan T hq
    have hrmem : y (-1 - (j : ℤ)) * f ∈
        Submodule.span k (L.shapeMonomials (ℓ - 1 - j) ℓ) := by
      refine hnR j (ℓ - 1 - j) ℓ (by omega) ?_
      omega
    obtain ⟨MG, hMG⟩ := L.exists_shapeRep hGmem
    obtain ⟨Mf, hMf⟩ := L.exists_shapeRep hfmem
    obtain ⟨Mr, hMr⟩ := L.exists_shapeRep hrmem
    refine ⟨MG, Mf, Mr, ?_, hMf⟩
    have hYrep : L.ShapeRep (ℓ - 1 - j) ℓ (Mf * Mr) (YY j) := by
      rw [hYY]
      exact L.shapeRep_mul hMf hMr
    exact L.shapeRep_mul hMG hYrep
  choose MG Mf Mr hprod hMfrep using hreps
  -- the total representing matrix
  set Mtot : Matrix (Fin ℓ → Fin 2) (Fin ℓ → Fin 2) k :=
    ∑ j ∈ (Finset.range M).attach,
      MG j.1 j.2 * (Mf j.1 j.2 * Mr j.1 j.2) with hMtot
  have hMtotrep : L.ShapeRep ℓ ℓ Mtot f := by
    rw [hstar, hMtot]
    have hsum := L.shapeRep_finsetSum (Finset.range M).attach
      (fun j ↦ MG j.1 j.2 * (Mf j.1 j.2 * Mr j.1 j.2))
      (fun j ↦ GG j.1 * YY j.1)
      (fun j _ ↦ hprod j.1 j.2)
    rwa [Finset.sum_attach (Finset.range M)
      (fun j ↦ GG j * YY j)] at hsum
  -- rank bounds
  have hlower : T.card * 2 ^ (ℓ - n) ≤ Mtot.rank := by
    refine L.card_le_rank_of_shapeRep_cylSum T (by omega) ?_
    rw [← hf]
    exact hMtotrep
  have hupper : Mtot.rank ≤
      ∑ j ∈ (Finset.range M).attach, T.card * 2 ^ (ℓ - 1 - j.1 - n)
      := by
    rw [hMtot]
    refine le_trans (rank_finsetSum_le _ _) ?_
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have h1 : (MG j.1 j.2 * (Mf j.1 j.2 * Mr j.1 j.2)).rank ≤
        (Mf j.1 j.2 * Mr j.1 j.2).rank :=
      Matrix.rank_mul_le_right _ _
    have h2 : (Mf j.1 j.2 * Mr j.1 j.2).rank ≤ (Mf j.1 j.2).rank :=
      Matrix.rank_mul_le_left _ _
    have h3 : (Mf j.1 j.2).rank ≤ T.card * 2 ^ (ℓ - 1 - j.1 - n) := by
      refine L.rank_le_card_of_shapeRep_cylSum T (by
        have := Finset.mem_range.mp j.2
        omega) ?_
      rw [← hf]
      exact hMfrep j.1 j.2
    exact le_trans h1 (le_trans h2 h3)
  -- the numerical contradiction
  have hgeom : ∑ j ∈ (Finset.range M).attach,
      T.card * 2 ^ (ℓ - 1 - j.1 - n) < T.card * 2 ^ (ℓ - n) := by
    rw [Finset.sum_attach (Finset.range M)
      (fun j ↦ T.card * 2 ^ (ℓ - 1 - j - n))]
    have hexp : ∀ j ∈ Finset.range M,
        T.card * 2 ^ (ℓ - 1 - j - n) = T.card * 2 ^ (K - j) := by
      intro j hj
      have := Finset.mem_range.mp hj
      congr 2
      omega
    rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum]
    have hrefl : ∑ j ∈ Finset.range M, 2 ^ (K - j) =
        ∑ i ∈ Finset.range M, 2 ^ (K - M + 1 + i) := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have := Finset.mem_range.mp hi
      congr 1
      omega
    rw [hrefl]
    have hfact : ∑ i ∈ Finset.range M, 2 ^ (K - M + 1 + i) =
        2 ^ (K - M + 1) * ∑ i ∈ Finset.range M, 2 ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [pow_add]
    rw [hfact]
    have hgs := sum_two_pow M
    have hKn : (2 : ℕ) ^ (K - M + 1) * 2 ^ M = 2 ^ (ℓ - n) := by
      rw [← pow_add]
      congr 1
      omega
    have h2pos : 0 < (2 : ℕ) ^ (K - M + 1) := pow_pos (by omega) _
    calc T.card * (2 ^ (K - M + 1) * ∑ i ∈ Finset.range M, 2 ^ i)
        < T.card * (2 ^ (K - M + 1) * 2 ^ M) :=
          mul_lt_mul_of_pos_left
            (mul_lt_mul_of_pos_left (by omega) h2pos) hTpos
      _ = T.card * 2 ^ (ℓ - n) := by rw [hKn]
  exact absurd (lt_of_le_of_lt (hlower.trans hupper) hgeom)
    (lt_irrefl _)

end BinaryLeavitt
end NonsoficGroupsExist
