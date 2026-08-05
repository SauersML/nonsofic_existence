import NonsoficGroupsExist.KazhdanFixedSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Almost-minimal displacement vectors

The crucial tool in Shalom's finite-presentability theorem: an orthogonal
representation of a discrete group with almost-invariant vectors but no
nonzero invariant vectors admits, for every `M`, a vector of displacement
exactly one whose entire radius-`M` neighbourhood has displacement more
than one half.  The halving recursion of Bekka–de la Harpe–Valette's
Lemma 3.2.5 terminates because a non-terminating run would converge to a
nonzero invariant vector.
-/

namespace NonsoficGroupsExist
namespace AlmostMinimal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {G : Type*} [Group G]

/-- The maximal displacement of a vector over a finite set of group
elements. -/
noncomputable def displacement (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ : E) : ℝ :=
  Q.sup' hQ (fun g ↦ ‖ρ g ξ - ξ‖)

theorem norm_le_displacement (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ : E) {g : G} (hg : g ∈ Q) :
    ‖ρ g ξ - ξ‖ ≤ displacement ρ Q hQ ξ := by
  unfold displacement
  exact Finset.le_sup' (fun g ↦ ‖ρ g ξ - ξ‖) hg

theorem displacement_le (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ : E) {r : ℝ}
    (h : ∀ g ∈ Q, ‖ρ g ξ - ξ‖ ≤ r) :
    displacement ρ Q hQ ξ ≤ r :=
  Finset.sup'_le hQ _ h

theorem displacement_nonneg (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ : E) : 0 ≤ displacement ρ Q hQ ξ := by
  obtain ⟨g, hg⟩ := id hQ
  exact le_trans (norm_nonneg _) (norm_le_displacement ρ Q hQ ξ hg)

theorem displacement_smul (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (c : ℝ) (ξ : E) :
    displacement ρ Q hQ (c • ξ) = |c| * displacement ρ Q hQ ξ := by
  unfold displacement
  rw [show (fun g ↦ ‖ρ g (c • ξ) - c • ξ‖) =
    (fun g ↦ |c| * ‖ρ g ξ - ξ‖) from by
    funext g
    rw [map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]]
  exact (Finset.apply_sup'_eq_sup'_comp hQ (fun r ↦ |c| * r)
    (fun x y ↦ mul_max_of_nonneg x y (abs_nonneg c))).symm

theorem displacement_le_add (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ η : E) :
    displacement ρ Q hQ ξ ≤ displacement ρ Q hQ η + 2 * ‖ξ - η‖ := by
  apply displacement_le
  intro g hg
  have h1 : ρ g ξ - ξ = (ρ g η - η) + (ρ g (ξ - η) - (ξ - η)) := by
    rw [map_sub]
    abel
  calc
    ‖ρ g ξ - ξ‖ ≤ ‖ρ g η - η‖ + ‖ρ g (ξ - η) - (ξ - η)‖ := by
      rw [h1]
      exact norm_add_le _ _
    _ ≤ ‖ρ g η - η‖ + (‖ρ g (ξ - η)‖ + ‖ξ - η‖) :=
      add_le_add_left (norm_sub_le _ _) _
    _ = ‖ρ g η - η‖ + 2 * ‖ξ - η‖ := by
      rw [(ρ g).norm_map]
      ring
    _ ≤ displacement ρ Q hQ η + 2 * ‖ξ - η‖ :=
      add_le_add (norm_le_displacement ρ Q hQ η hg) le_rfl

theorem displacement_lipschitz (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ η : E) :
    |displacement ρ Q hQ ξ - displacement ρ Q hQ η| ≤ 2 * ‖ξ - η‖ := by
  rw [abs_le]
  constructor
  · have := displacement_le_add ρ Q hQ η ξ
    rw [show ‖η - ξ‖ = ‖ξ - η‖ from norm_sub_rev η ξ] at this
    linarith
  · have := displacement_le_add ρ Q hQ ξ η
    linarith

theorem displacement_line_continuous (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (Q : Finset G) (hQ : Q.Nonempty) (ξ η : E) :
    Continuous (fun t : ℝ ↦ displacement ρ Q hQ (ξ + t • (η - ξ))) := by
  have hlip : LipschitzWith (2 * ‖η - ξ‖).toNNReal
      (fun t : ℝ ↦ displacement ρ Q hQ (ξ + t • (η - ξ))) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.dist_eq, Real.dist_eq]
    have h1 := displacement_lipschitz ρ Q hQ (ξ + s • (η - ξ))
      (ξ + t • (η - ξ))
    have h2 : ‖(ξ + s • (η - ξ)) - (ξ + t • (η - ξ))‖ =
        |s - t| * ‖η - ξ‖ := by
      rw [show (ξ + s • (η - ξ)) - (ξ + t • (η - ξ)) =
        (s - t) • (η - ξ) from by
        rw [sub_smul]
        abel]
      rw [norm_smul, Real.norm_eq_abs]
    rw [h2] at h1
    have h3 : ((2 * ‖η - ξ‖).toNNReal : ℝ) = 2 * ‖η - ξ‖ :=
      Real.coe_toNNReal _ (by positivity)
    rw [h3]
    calc
      |displacement ρ Q hQ (ξ + s • (η - ξ)) -
          displacement ρ Q hQ (ξ + t • (η - ξ))| ≤
          2 * (|s - t| * ‖η - ξ‖) := h1
      _ = 2 * ‖η - ξ‖ * |s - t| := by ring
  exact hlip.continuous

theorem eq_zero_of_displacement_eq_zero (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (Q : Finset G) (hQ : Q.Nonempty)
    (hgen : Subgroup.closure (Q : Set G) = ⊤)
    (hnoinv : ∀ ξ : E, (∀ g : G, ρ g ξ = ξ) → ξ = 0)
    {ξ : E} (hξ : displacement ρ Q hQ ξ = 0) : ξ = 0 := by
  apply hnoinv
  have hfix : ∀ g ∈ Q, ρ g ξ = ξ := by
    intro g hg
    have h1 := norm_le_displacement ρ Q hQ ξ hg
    rw [hξ] at h1
    have h2 : ‖ρ g ξ - ξ‖ = 0 := le_antisymm h1 (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h2)
  exact KazhdanFixedSpace.invariant_of_fixed_generators ρ
    (Q : Set G) hgen ξ hfix

/-- The displacement function is continuous (indeed `2`-Lipschitz). -/
theorem displacement_continuous (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) : Continuous (displacement ρ Q hQ) := by
  have hlip : LipschitzWith 2 (displacement ρ Q hQ) := by
    apply LipschitzWith.of_dist_le_mul
    intro ξ η
    have h : dist (displacement ρ Q hQ ξ) (displacement ρ Q hQ η) ≤
        2 * dist ξ η := by
      rw [Real.dist_eq, dist_eq_norm]
      exact displacement_lipschitz ρ Q hQ ξ η
    exact_mod_cast h
  exact hlip.continuous

/-- **Almost-minimal displacement vectors** (Bekka–de la Harpe–Valette,
Lemma 3.2.5, discrete case), from a single witness.  If an orthogonal
representation of a group generated by the finite set `Q` has no nonzero
invariant vectors but has one unit vector of displacement below
`1 / (4 * M)`, then there is a vector of displacement exactly one all of
whose `M`-neighbours have displacement more than one half.  A
counterexample would halve displacement within a scale-invariant
distance; iterating from the witness produces a geometric Cauchy
sequence whose limit is a nonzero invariant vector.  Requiring only one
witness rather than almost-invariant vectors of every tolerance
strengthens the cited lemma and lets each finite quotient in Shalom's
argument supply its own witness representation directly. -/
theorem exists_displacement_one_of_witness [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G) (hQ : Q.Nonempty)
    (hgen : Subgroup.closure (Q : Set G) = ⊤)
    (hnoinv : ∀ ξ : E, (∀ g : G, ρ g ξ = ξ) → ξ = 0)
    (M : ℝ) (hM : 0 < M) {ξ₀ : E} (hξ₀norm : ‖ξ₀‖ = 1)
    (hξ₀disp : displacement ρ Q hQ ξ₀ < 1 / (4 * M)) :
    ∃ ξ : E, displacement ρ Q hQ ξ = 1 ∧
      ∀ η : E, ‖η - ξ‖ ≤ M → 1 / 2 < displacement ρ Q hQ η := by
  by_contra hcon
  push Not at hcon
  -- The scale-invariant halving step: any vector of positive displacement
  -- admits a vector at controlled distance with exactly half its
  -- displacement, by normalizing, applying the counterexample, and
  -- passing to the segment via the intermediate value theorem.
  have step : ∀ ζ : E, 0 < displacement ρ Q hQ ζ →
      ∃ η : E, ‖η - ζ‖ ≤ M * displacement ρ Q hQ ζ ∧
        displacement ρ Q hQ η = displacement ρ Q hQ ζ / 2 := by
    intro ζ hζ
    set d := displacement ρ Q hQ ζ with hd
    have hd0 : d ≠ 0 := ne_of_gt hζ
    have hξ' : displacement ρ Q hQ (d⁻¹ • ζ) = 1 := by
      rw [displacement_smul, ← hd, abs_of_pos (inv_pos.mpr hζ),
        inv_mul_cancel₀ hd0]
    obtain ⟨η', hη'M, hη'd⟩ := hcon (d⁻¹ • ζ) hξ'
    have hend1 : displacement ρ Q hQ
        (d⁻¹ • ζ + (1 : ℝ) • (η' - d⁻¹ • ζ)) =
        displacement ρ Q hQ η' := by
      rw [one_smul, show d⁻¹ • ζ + (η' - d⁻¹ • ζ) = η' from by abel]
    have hend0 : displacement ρ Q hQ
        (d⁻¹ • ζ + (0 : ℝ) • (η' - d⁻¹ • ζ)) = 1 := by
      rw [zero_smul, add_zero, hξ']
    have hmem : (1 / 2 : ℝ) ∈ Set.Icc
        (displacement ρ Q hQ (d⁻¹ • ζ + (1 : ℝ) • (η' - d⁻¹ • ζ)))
        (displacement ρ Q hQ (d⁻¹ • ζ + (0 : ℝ) • (η' - d⁻¹ • ζ))) :=
      Set.mem_Icc.mpr ⟨by rw [hend1]; exact hη'd, by rw [hend0]; norm_num⟩
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc' zero_le_one
      ((displacement_line_continuous ρ Q hQ (d⁻¹ • ζ) η').continuousOn)
      hmem
    have hFt' : displacement ρ Q hQ
        (d⁻¹ • ζ + t • (η' - d⁻¹ • ζ)) = 1 / 2 := hFt
    refine ⟨d • (d⁻¹ • ζ + t • (η' - d⁻¹ • ζ)), ?_, ?_⟩
    · have hkey : d • (d⁻¹ • ζ + t • (η' - d⁻¹ • ζ)) - ζ =
          d • (t • (η' - d⁻¹ • ζ)) := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hd0, one_smul]
        abel
      rw [hkey, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hζ]
      have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have h5 : |t| * ‖η' - d⁻¹ • ζ‖ ≤ 1 * M :=
        mul_le_mul ht1 hη'M (norm_nonneg _) zero_le_one
      calc d * (|t| * ‖η' - d⁻¹ • ζ‖) ≤ d * (1 * M) :=
            mul_le_mul_of_nonneg_left h5 hζ.le
        _ = M * d := by ring
    · rw [displacement_smul, abs_of_pos hζ, hFt']
      ring
  -- The witness has positive displacement since it is not zero.
  set δ := displacement ρ Q hQ ξ₀ with hδ
  have hδpos : 0 < δ := by
    rcases (displacement_nonneg ρ Q hQ ξ₀).lt_or_eq with h | h
    · rw [hδ]
      exact h
    · exfalso
      have h0 := eq_zero_of_displacement_eq_zero ρ Q hQ hgen hnoinv h.symm
      rw [h0, norm_zero] at hξ₀norm
      exact zero_ne_one hξ₀norm
  -- Totalize the halving step so that iteration is a plain function.
  have step' : ∀ ζ : E, ∃ η : E, 0 < displacement ρ Q hQ ζ →
      ‖η - ζ‖ ≤ M * displacement ρ Q hQ ζ ∧
        displacement ρ Q hQ η = displacement ρ Q hQ ζ / 2 := by
    intro ζ
    by_cases h : 0 < displacement ρ Q hQ ζ
    · obtain ⟨η, h1, h2⟩ := step ζ h
      exact ⟨η, fun _ ↦ ⟨h1, h2⟩⟩
    · exact ⟨0, fun hc ↦ absurd hc h⟩
  choose g hg using step'
  have hdisp : ∀ i : ℕ,
      displacement ρ Q hQ (g^[i] ξ₀) = δ / 2 ^ i := by
    intro i
    induction i with
    | zero => rw [Function.iterate_zero_apply, ← hδ, pow_zero, div_one]
    | succ i ih =>
      have hpos : 0 < displacement ρ Q hQ (g^[i] ξ₀) := by
        rw [ih]
        exact div_pos hδpos (pow_pos (by norm_num) i)
      rw [Function.iterate_succ_apply', (hg _ hpos).2, ih, pow_succ]
      ring
  have hdist : ∀ i : ℕ,
      dist (g^[i] ξ₀) (g^[i + 1] ξ₀) ≤ M * δ * (1 / 2) ^ i := by
    intro i
    have hpos : 0 < displacement ρ Q hQ (g^[i] ξ₀) := by
      rw [hdisp i]
      exact div_pos hδpos (pow_pos (by norm_num) i)
    have h1 := (hg _ hpos).1
    rw [hdisp i] at h1
    rw [dist_eq_norm, norm_sub_rev, Function.iterate_succ_apply']
    calc ‖g (g^[i] ξ₀) - g^[i] ξ₀‖ ≤ M * (δ / 2 ^ i) := h1
      _ = M * δ * (1 / 2) ^ i := by
        rw [one_div, inv_pow]
        ring
  -- The iterates form a geometric Cauchy sequence; the limit has zero
  -- displacement, hence vanishes, yet stays close to the unit vector.
  have hcauchy : CauchySeq (fun i : ℕ ↦ g^[i] ξ₀) :=
    cauchySeq_of_le_geometric (r := 1 / 2) (C := M * δ) (by norm_num) hdist
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcauchy
  have htend0 : Filter.Tendsto
      (fun i : ℕ ↦ displacement ρ Q hQ (g^[i] ξ₀))
      Filter.atTop (nhds 0) := by
    simp only [hdisp]
    rw [show (fun i : ℕ ↦ δ / 2 ^ i) =
        fun i : ℕ ↦ δ * (1 / 2 : ℝ) ^ i from by
      funext i
      rw [one_div, inv_pow]
      ring]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul δ
  have htend : Filter.Tendsto
      (fun i : ℕ ↦ displacement ρ Q hQ (g^[i] ξ₀))
      Filter.atTop (nhds (displacement ρ Q hQ ℓ)) :=
    ((displacement_continuous ρ Q hQ).tendsto ℓ).comp hℓ
  have hℓ0 : ℓ = 0 := eq_zero_of_displacement_eq_zero ρ Q hQ hgen hnoinv
    (tendsto_nhds_unique htend htend0)
  have hbound := dist_le_of_le_geometric_of_tendsto₀ (r := 1 / 2)
    (C := M * δ) (by norm_num) hdist hℓ
  have hb2 : dist ξ₀ ℓ ≤ M * δ / (1 - 1 / 2) := hbound
  rw [hℓ0, dist_zero_right, hξ₀norm,
    show M * δ / (1 - 1 / 2 : ℝ) = 2 * (M * δ) from by
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 from by norm_num,
        div_eq_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      ring] at hb2
  have h4 : M * δ < 1 / 4 := by
    have hlt : M * δ < M * (1 / (4 * M)) :=
      mul_lt_mul_of_pos_left hξ₀disp hM
    have hM4 : M * (1 / (4 * M)) = 1 / 4 := by
      rw [mul_one_div, mul_comm (4 : ℝ) M, ← div_div, div_self hM.ne']
    linarith
  linarith

/-- The cited form of Bekka–de la Harpe–Valette Lemma 3.2.5: with
almost-invariant unit vectors of every tolerance, every isolation radius
is realized by some displacement-one vector. -/
theorem exists_displacement_one_of_almost_invariant [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G) (hQ : Q.Nonempty)
    (hgen : Subgroup.closure (Q : Set G) = ⊤)
    (hnoinv : ∀ ξ : E, (∀ g : G, ρ g ξ = ξ) → ξ = 0)
    (halmost : ∀ ε : ℝ, 0 < ε →
      ∃ ξ : E, ‖ξ‖ = 1 ∧ displacement ρ Q hQ ξ < ε)
    (M : ℝ) (hM : 0 < M) :
    ∃ ξ : E, displacement ρ Q hQ ξ = 1 ∧
      ∀ η : E, ‖η - ξ‖ ≤ M → 1 / 2 < displacement ρ Q hQ η := by
  obtain ⟨ξ₀, hξ₀norm, hξ₀disp⟩ := halmost (1 / (4 * M))
    (div_pos one_pos (by linarith))
  exact exists_displacement_one_of_witness ρ Q hQ hgen hnoinv M hM
    hξ₀norm hξ₀disp

end AlmostMinimal
end NonsoficGroupsExist
