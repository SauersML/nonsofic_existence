import NonsoficGroupsExist.Kazhdan.UltralimitGeometry
import NonsoficGroupsExist.Kazhdan.AlmostMinimalDisplacement
import NonsoficGroupsExist.Kazhdan.DelormeFixedPoint
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Shalom's theorem: finitely presented Kazhdan covers

Every finitely generated group with Kazhdan's property `(T)` is a
quotient of a finitely presented group with property `(T)`
(Shalom; Bekka–de la Harpe–Valette, Theorem 3.4.5).  The proof here is
leaner than the cited one.  Present `G = F/N` and exhaust `N` by
finitely many normal generators at a time.  If every finite stage failed
property `(T)`, each stage would provide a witness representation with a
single almost-invariant unit vector and no invariant vectors, so the
single-witness halving lemma (`exists_displacement_one_of_witness`)
yields displacement-one vectors `ξ_k` whose radius-`(k+1)`
neighbourhoods have displacement above `1/2`.  The orbit cocycles
`b_k(g) = σ_k(g)ξ_k - ξ_k` have hyperreal-bounded norms, their Gaussian
kernels are positive-definite at every stage, and the standard-part
calculus (`UltralimitGeometry`) passes both facts to the ultralimit
`ψ̄(g) = st ‖b_k(g)‖²`, which descends to `G` because the relators die
eventually.  The Gaussian boundedness principle
(`bounded_of_gaussian_isPositiveDefinite`) bounds `ψ̄`, the
approximate-circumcenter estimate produces a sequence almost fixed by
every generator, and transfer to a single large index `k` contradicts
the isolation of `ξ_k`.
-/

namespace NonsoficGroupsExist
namespace Shalom

universe u

open KazhdanFiniteModel Ultralimit AlmostMinimal Delorme

/-- Subsingleton groups have property `(T)` with the empty Kazhdan
set. -/
theorem hasKazhdanPropertyT_of_subsingleton {Γ : Type v} [Group Γ]
    [Subsingleton Γ] : HasKazhdanPropertyT.{v, w} Γ := by
  refine ⟨∅, 1, one_pos, ?_⟩
  intro E _ _ _ ρ x hx _
  refine ⟨x, ?_, fun g ↦ ?_⟩
  · intro h0
    rw [h0, norm_zero] at hx
    exact zero_ne_one hx
  · rw [Subsingleton.elim g 1, map_one]
    rfl

/-- The free group on an empty type is trivial. -/
theorem freeGroup_subsingleton_of_isEmpty {α : Type*} [IsEmpty α] :
    Subsingleton (FreeGroup α) := by
  constructor
  intro x y
  have hone : ∀ z : FreeGroup α, z = 1 := by
    intro z
    refine FreeGroup.induction_on z rfl
      (fun i ↦ (IsEmpty.false i).elim)
      (fun i _ ↦ (IsEmpty.false i).elim)
      (fun a b ha hb ↦ by rw [ha, hb, one_mul])
  rw [hone x, hone y]

/-- The finset of free generators. -/
noncomputable def generatorSet (n : ℕ) : Finset (FreeGroup (Fin n)) := by
  classical
  exact Finset.univ.image FreeGroup.of

theorem generatorSet_nonempty {n : ℕ} (hn : n ≠ 0) :
    (generatorSet n).Nonempty := by
  classical
  exact ⟨FreeGroup.of ⟨0, Nat.pos_of_ne_zero hn⟩, by
    simp [generatorSet]⟩

theorem coe_generatorSet (n : ℕ) :
    ((generatorSet n : Finset (FreeGroup (Fin n))) : Set (FreeGroup (Fin n))) =
      Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)) := by
  classical
  simp [generatorSet]

theorem closure_generatorSet (n : ℕ) :
    Subgroup.closure
      ((generatorSet n : Finset (FreeGroup (Fin n))) : Set (FreeGroup (Fin n))) = ⊤ := by
  rw [coe_generatorSet]
  exact FreeGroup.closure_range_of (Fin n)

/-- **The ultralimit contradiction.**  A sequence of representations of
the free group whose stage-`k` member kills every kernel element
eventually, carries a displacement-one vector isolated at radius
`k + 1`, cannot exist over a Kazhdan base group. -/
theorem core_contradiction {G : Type u} [Group G] {n : ℕ} (hn : n ≠ 0)
    (β : FreeGroup (Fin n) →* G) (hβ : Function.Surjective β)
    {Q : Finset G} {ε' : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε')
    (E : ℕ → Type) (instN : ∀ k, NormedAddCommGroup (E k))
    (instI : ∀ k, @InnerProductSpace ℝ (E k) _
      (instN k).toSeminormedAddCommGroup)
    (σ : ∀ k, FreeGroup (Fin n) →* (E k ≃ₗᵢ[ℝ] E k))
    (hkill : ∀ w ∈ β.ker, ∃ j : ℕ, ∀ k, j ≤ k → σ k w = 1)
    (ξ : ∀ k, E k)
    (hdisp1 : ∀ k,
      displacement (σ k) (generatorSet n) (generatorSet_nonempty hn)
        (ξ k) = 1)
    (hiso : ∀ k, ∀ η : E k, ‖η - ξ k‖ ≤ (k : ℝ) + 1 →
      1 / 2 < displacement (σ k) (generatorSet n)
        (generatorSet_nonempty hn) η) :
    False := by
  classical
  letI := instN
  letI := instI
  -- The orbit cocycles and their hyperreal boundedness.
  set bseq : FreeGroup (Fin n) → ∀ k, E k :=
    fun g k ↦ σ k g (ξ k) - ξ k with hbseq
  have hcoc : ∀ k, IsCocycle (σ k) (fun g ↦ σ k g (ξ k) - ξ k) :=
    fun k ↦ isCocycle_orbit (σ k) (ξ k)
  have hgenbound : ∀ i : Fin n, ∀ k, ‖bseq (FreeGroup.of i) k‖ ≤ 1 := by
    intro i k
    have hle := norm_le_displacement (σ k) (generatorSet n)
      (generatorSet_nonempty hn) (ξ k)
      (g := FreeGroup.of i) (by simp [generatorSet])
    rw [hdisp1 k] at hle
    exact hle
  have hbound : ∀ g : FreeGroup (Fin n), IsBoundedSeq (bseq g) := by
    intro g
    refine FreeGroup.induction_on g ?_ ?_ ?_ ?_
    · exact ⟨0, fun k ↦ by simp [hbseq]⟩
    · intro i
      exact ⟨1, hgenbound i⟩
    · intro i hi
      obtain ⟨C, hC⟩ := hi
      refine ⟨C, fun k ↦ ?_⟩
      have hinv := (hcoc k).apply_inv (FreeGroup.of i)
      calc ‖bseq (FreeGroup.of i)⁻¹ k‖ =
          ‖σ k (FreeGroup.of i)⁻¹ (bseq (FreeGroup.of i) k)‖ := by
            rw [show bseq (FreeGroup.of i)⁻¹ k =
              -(σ k (FreeGroup.of i)⁻¹ (bseq (FreeGroup.of i) k)) from
                hinv, norm_neg]
        _ = ‖bseq (FreeGroup.of i) k‖ := (σ k _).norm_map _
        _ ≤ C := hC k
    · intro a b ha hb
      obtain ⟨C, hC⟩ := ha
      obtain ⟨D, hD⟩ := hb
      refine ⟨C + D, fun k ↦ ?_⟩
      have hmul := hcoc k a b
      calc ‖bseq (a * b) k‖ =
          ‖bseq a k + σ k a (bseq b k)‖ := by rw [show bseq (a * b) k =
            bseq a k + σ k a (bseq b k) from hmul]
        _ ≤ ‖bseq a k‖ + ‖σ k a (bseq b k)‖ := norm_add_le _ _
        _ = ‖bseq a k‖ + ‖bseq b k‖ := by rw [(σ k a).norm_map]
        _ ≤ C + D := add_le_add (hC k) (hD k)
  -- The ultralimit function and its descent to the base group.
  set ψ : FreeGroup (Fin n) → ℝ := fun g ↦ seqNormSq (bseq g) with hψ
  have hψnn : ∀ g, 0 ≤ ψ g := by
    intro g
    show 0 ≤ seqNormSq (bseq g)
    rw [seqNormSq_eq_sq (hbound g)]
    exact sq_nonneg _
  have hψone : ψ 1 = 0 := by
    have hzero : bseq (1 : FreeGroup (Fin n)) = fun k ↦ 0 := by
      funext k
      simp [hbseq]
    rw [hψ]
    show seqNormSq (bseq 1) = 0
    rw [hzero]
    have hconst : (Hyperreal.ofSeq fun k ↦ ‖(0 : E k)‖ ^ 2) =
        ((0 : ℝ) : Hyperreal) := by
      have : (fun k ↦ ‖(0 : E k)‖ ^ 2) = fun _ : ℕ ↦ (0 : ℝ) := by
        funext k
        simp
      rw [this]
      rfl
    rw [seqNormSq, hconst, stdPart_coe]
  have hψsymm : ∀ g h : FreeGroup (Fin n), ψ (g⁻¹ * h) = ψ (h⁻¹ * g) := by
    intro g h
    rw [hψ]
    show seqNormSq (bseq (g⁻¹ * h)) = seqNormSq (bseq (h⁻¹ * g))
    unfold seqNormSq
    congr 1
    apply congrArg Hyperreal.ofSeq
    funext k
    rw [show ‖bseq (g⁻¹ * h) k‖ = ‖bseq h k - bseq g k‖ from
      (hcoc k).norm_inv_mul g h,
      show ‖bseq (h⁻¹ * g) k‖ = ‖bseq g k - bseq h k‖ from
      (hcoc k).norm_inv_mul h g, norm_sub_rev]
  have hdescend : ∀ g w, w ∈ β.ker → ψ (g * w) = ψ g := by
    intro g w hw
    obtain ⟨j, hj⟩ := hkill w hw
    rw [hψ]
    show seqNormSq (bseq (g * w)) = seqNormSq (bseq g)
    unfold seqNormSq
    congr 1
    have hev : (fun k ↦ ‖bseq (g * w) k‖ ^ 2) =ᶠ[↑(Filter.hyperfilter ℕ)]
        fun k ↦ ‖bseq g k‖ ^ 2 := by
      filter_upwards [eventually_le_id j] with k hk
      have hkw := hj k hk
      have : bseq (g * w) k = bseq g k := by
        simp only [hbseq]
        rw [map_mul, hkw]
        rfl
      rw [this]
    exact Filter.Germ.coe_eq.mpr hev
  -- Gaussians of the ultralimit are positive-definite.
  have hgauss : ∀ t : ℝ, 0 < t → ∀ g : FreeGroup (Fin n),
      Real.exp (-t * ψ g) = ArchimedeanClass.stdPart
        (Hyperreal.ofSeq fun k ↦ Real.exp (-t * ‖bseq g k‖ ^ 2)) := by
    intro t ht g
    obtain ⟨C, hC⟩ := hbound g
    have hCk : ∀ k, -t * ‖bseq g k‖ ^ 2 ≤ 0 := by
      intro k
      have := sq_nonneg ‖bseq g k‖
      nlinarith
    have hCk' : ∀ k, -t * (C ^ 2) ≤ -t * ‖bseq g k‖ ^ 2 := by
      intro k
      have h0 : 0 ≤ ‖bseq g k‖ := norm_nonneg _
      have hsq : ‖bseq g k‖ ^ 2 ≤ C ^ 2 := by nlinarith [hC k]
      nlinarith
    have hstd := stdPart_exp (s := fun k ↦ -t * ‖bseq g k‖ ^ 2)
      hCk' hCk
    rw [hstd]
    congr 1
    have hmul : (Hyperreal.ofSeq fun k ↦ -t * ‖bseq g k‖ ^ 2) =
        ((-t : ℝ) : Hyperreal) *
          (Hyperreal.ofSeq fun k ↦ ‖bseq g k‖ ^ 2) := by
      rw [show ((-t : ℝ) : Hyperreal) =
        Hyperreal.ofSeq (fun _ : ℕ ↦ (-t : ℝ)) from rfl, ← ofSeq_mul]
    rw [hmul, ArchimedeanClass.stdPart_mul (hyperreal_coe_finite (-t))
      (ofSeq_norm_sq_finite (hbound g)), stdPart_coe]
    have hq : ψ g = ArchimedeanClass.stdPart
        (Hyperreal.ofSeq fun k ↦ ‖bseq g k‖ ^ 2) :=
      seqNormSq_def (bseq g)
    rw [hq]
  have hpdF : ∀ t : ℝ, 0 < t →
      IsPositiveDefinite (fun g : FreeGroup (Fin n) ↦
        Real.exp (-t * ψ g)) := by
    intro t ht
    constructor
    · intro g h
      show Real.exp (-t * ψ (g⁻¹ * h)) = Real.exp (-t * ψ (h⁻¹ * g))
      rw [hψsymm g h]
    · intro F c
      have hentry : ∀ g : FreeGroup (Fin n),
          Real.exp (-t * ψ g) = ArchimedeanClass.stdPart
            (Hyperreal.ofSeq fun k ↦
              Real.exp (-t * ‖bseq g k‖ ^ 2)) := hgauss t ht
      have hfinentry : ∀ g : FreeGroup (Fin n),
          0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq fun k ↦
            Real.exp (-t * ‖bseq g k‖ ^ 2)) := by
        intro g
        refine ofSeq_finite_of_bounds
          (fun k ↦ (Real.exp_pos _).le) (b := 1) fun k ↦ ?_
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
        apply Real.exp_le_exp.mpr
        have := sq_nonneg ‖bseq g k‖
        nlinarith
      have hterm : ∀ i j : FreeGroup (Fin n),
          c i * c j * Real.exp (-t * ψ (i⁻¹ * j)) =
            ArchimedeanClass.stdPart
              (((c i * c j : ℝ) : Hyperreal) *
                Hyperreal.ofSeq fun k ↦
                  Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2)) := by
        intro i j
        rw [ArchimedeanClass.stdPart_mul
          (hyperreal_coe_finite (c i * c j)) (hfinentry (i⁻¹ * j)),
          stdPart_coe, hentry (i⁻¹ * j)]
      have hsum : ∑ i ∈ F, ∑ j ∈ F,
          c i * c j * Real.exp (-t * ψ (i⁻¹ * j)) =
          ArchimedeanClass.stdPart (∑ i ∈ F, ∑ j ∈ F,
            ((c i * c j : ℝ) : Hyperreal) *
              Hyperreal.ofSeq fun k ↦
                Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2)) := by
        rw [stdPart_finset_sum F _ (fun i _ ↦
          hyperreal_finset_sum_finite F _ (fun j _ ↦
            hyperreal_mul_finite (hyperreal_coe_finite _)
              (hfinentry _)))]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [stdPart_finset_sum F _ (fun j _ ↦
          hyperreal_mul_finite (hyperreal_coe_finite _) (hfinentry _))]
        exact Finset.sum_congr rfl fun j _ ↦ hterm i j
      rw [hsum]
      have hofseq : ∑ i ∈ F, ∑ j ∈ F,
          ((c i * c j : ℝ) : Hyperreal) *
            (Hyperreal.ofSeq fun k ↦
              Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2)) =
          Hyperreal.ofSeq fun k ↦ ∑ i ∈ F, ∑ j ∈ F,
            c i * c j * Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2) := by
        rw [show (Hyperreal.ofSeq fun k ↦ ∑ i ∈ F, ∑ j ∈ F,
            c i * c j * Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2)) =
          ofSeqRingHom (fun k ↦ ∑ i ∈ F, ∑ j ∈ F,
            c i * c j * Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2)) from
          rfl]
        rw [show (fun k ↦ ∑ i ∈ F, ∑ j ∈ F,
            c i * c j * Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2)) =
          ∑ i ∈ F, ∑ j ∈ F, (fun k ↦
            c i * c j * Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2)) from by
          funext k
          simp]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [show ((fun k ↦ c i * c j *
            Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2))) =
          (fun _ : ℕ ↦ (c i * c j : ℝ)) * (fun k ↦
            Real.exp (-t * ‖bseq (i⁻¹ * j) k‖ ^ 2)) from by
          funext k
          simp]
        rw [map_mul]
        rfl
      rw [hofseq]
      apply ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom
      · rw [← hofseq]
        exact hyperreal_finset_sum_finite F _ (fun i _ ↦
          hyperreal_finset_sum_finite F _ (fun j _ ↦
            hyperreal_mul_finite (hyperreal_coe_finite _)
              (hfinentry _)))
      · rw [map_zero]
        change Hyperreal.ofSeq (fun _ : ℕ ↦ (0 : ℝ)) ≤ _
        rw [Hyperreal.ofSeq_le_ofSeq]
        apply Filter.Eventually.of_forall
        intro k
        exact (GaussianKernel.isPositiveDefinite_exp_neg_norm_sq
          (fun g ↦ bseq g k) (fun g h ↦ (hcoc k).norm_inv_mul g h)
          ht.le).2 F c
  -- Descend to the base group and bound the ultralimit.
  set s : G → FreeGroup (Fin n) := Function.surjInv hβ
  set ψG : G → ℝ := fun γ ↦ ψ (s γ) with hψG
  have hcomp : ∀ g : FreeGroup (Fin n), ψG (β g) = ψ g := by
    intro g
    rw [hψG]
    show ψ (s (β g)) = ψ g
    have hker : (s (β g))⁻¹ * g ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv,
        Function.surjInv_eq hβ (β g)]
      simp
    have := hdescend (s (β g)) ((s (β g))⁻¹ * g) hker
    rw [← mul_assoc, mul_inv_cancel, one_mul] at this
    exact this.symm
  have hpdG : ∀ t : ℝ, 0 < t →
      IsPositiveDefinite (fun γ : G ↦ Real.exp (-t * ψG γ)) := by
    intro t ht
    apply GaussianKernel.isPositiveDefinite_of_comp_surjective β hβ
      (χ := fun γ ↦ Real.exp (-t * ψG γ))
    have heq : (fun g : FreeGroup (Fin n) ↦
        Real.exp (-t * ψG (β g))) =
        fun g ↦ Real.exp (-t * ψ g) := by
      funext g
      rw [hcomp g]
    rw [heq]
    exact hpdF t ht
  obtain ⟨R, hR⟩ := Delorme.bounded_of_gaussian_isPositiveDefinite hQ
    ψG (by
      have h1 : ψG 1 = ψ 1 := by
        rw [show (1 : G) = β 1 from (map_one β).symm]
        exact hcomp 1
      rw [h1]
      exact hψone)
    (fun γ ↦ by rw [hψG]; exact hψnn (s γ)) hpdG
  have hψR : ∀ g : FreeGroup (Fin n), ψ g ≤ R := by
    intro g
    rw [← hcomp g]
    exact hR (β g)
  -- The orbit is seminorm-bounded; run the approximate circumcenter.
  set D : ℝ := Real.sqrt R
  have hR0 : 0 ≤ R := le_trans (hψnn 1) (hψR 1)
  have hOD : ∀ g : FreeGroup (Fin n), seqNorm (bseq g) ≤ D := by
    intro g
    have h1 : seqNorm (bseq g) ^ 2 ≤ R := by
      rw [← seqNormSq_eq_sq (hbound g)]
      exact hψR g
    have h2 : Real.sqrt (seqNorm (bseq g) ^ 2) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (seqNorm_nonneg (hbound g))] at h2
  have hc0 : 0 ≤ centerRadius bseq := by
    refine le_csInf ⟨orbitRadius bseq (bseq 1), bseq 1, hbound 1, rfl⟩ ?_
    rintro r ⟨v, hv, rfl⟩
    exact orbitRadius_nonneg ⟨1⟩ hbound hOD hv
  have hcD : centerRadius bseq ≤ D := by
    refine le_trans (centerRadius_le ⟨1⟩ hbound hOD (hbound 1)) ?_
    apply orbitRadius_le ⟨1⟩
    intro g
    have : seqNorm (fun k ↦ bseq 1 k - bseq g k) =
        seqNorm (bseq g) := by
      have hz : (fun k ↦ bseq 1 k - bseq g k) =
          fun k ↦ -(bseq g k) := by
        funext k
        simp [hbseq]
      rw [hz, seqNorm_neg]
    rw [this]
    exact hOD g
  -- Choose the tolerance and the near-center.
  set c := centerRadius bseq with hcdef
  set δ : ℝ := 1 / (100 * (D + 1)) with hδdef
  have hD0 : 0 ≤ D := Real.sqrt_nonneg R
  have hδ0 : 0 < δ := by
    rw [hδdef]
    apply div_pos one_pos
    nlinarith
  obtain ⟨v, hvb, hvr⟩ := exists_near_center ⟨1⟩ hbound hOD hδ0
  -- Every generator moves the near-center little.
  have hsmall : ∀ i : Fin n,
      seqNormSq (fun k ↦ v k -
        (σ k (FreeGroup.of i) (v k) + bseq (FreeGroup.of i) k)) ≤
      4 * ((c + δ) ^ 2 - c ^ 2) := by
    intro i
    set w : ∀ k, E k :=
      fun k ↦ σ k (FreeGroup.of i) (v k) + bseq (FreeGroup.of i) k
      with hw
    have hwb : IsBoundedSeq w := by
      obtain ⟨Cv, hCv⟩ := id hvb
      refine ⟨Cv + 1, fun k ↦ ?_⟩
      calc ‖w k‖ ≤ ‖σ k (FreeGroup.of i) (v k)‖ +
          ‖bseq (FreeGroup.of i) k‖ := norm_add_le _ _
        _ = ‖v k‖ + ‖bseq (FreeGroup.of i) k‖ := by
            rw [(σ k _).norm_map]
        _ ≤ Cv + 1 := add_le_add (hCv k) (hgenbound i k)
    have hwr : orbitRadius bseq w ≤ c + δ := by
      apply orbitRadius_le ⟨1⟩
      intro g
      have hshift : seqNorm (fun k ↦ w k - bseq g k) =
          seqNorm (fun k ↦ v k - bseq ((FreeGroup.of i)⁻¹ * g) k) := by
        apply seqNorm_congr_norm
        intro k
        have hcoceq : bseq g k = bseq (FreeGroup.of i) k +
            σ k (FreeGroup.of i)
              (bseq ((FreeGroup.of i)⁻¹ * g) k) := by
          have := hcoc k (FreeGroup.of i) ((FreeGroup.of i)⁻¹ * g)
          rw [← mul_assoc, mul_inv_cancel, one_mul] at this
          exact this
        rw [hw]
        show ‖σ k (FreeGroup.of i) (v k) +
          bseq (FreeGroup.of i) k - bseq g k‖ = _
        rw [hcoceq, show σ k (FreeGroup.of i) (v k) +
          bseq (FreeGroup.of i) k -
          (bseq (FreeGroup.of i) k +
            σ k (FreeGroup.of i)
              (bseq ((FreeGroup.of i)⁻¹ * g) k)) =
          σ k (FreeGroup.of i)
            (v k - bseq ((FreeGroup.of i)⁻¹ * g) k) from by
          have hms := map_sub (σ k (FreeGroup.of i)) (v k)
            (bseq ((FreeGroup.of i)⁻¹ * g) k)
          rw [hms]
          abel]
        exact (σ k _).norm_map _
      rw [hshift]
      exact le_trans (le_orbitRadius hbound hOD hvb _) hvr.le
    have := seqNormSq_sub_le_of_near_center ⟨1⟩ hbound hOD hvb hwb
      (ρ := c + δ) hvr.le hwr
    rw [hcdef] at this ⊢
    exact this
  -- Numerical smallness of the displacement bound.
  have hnum : 4 * ((c + δ) ^ 2 - c ^ 2) < (1 / 3) ^ 2 := by
    have hcle : c ≤ D := hcD
    have hδle : δ * (100 * (D + 1)) = 1 := by
      rw [hδdef]
      field_simp
    nlinarith [hc0, hD0, hδ0]
  -- Transfer to a single large stage and contradict the isolation.
  obtain ⟨Cv, hCv⟩ := id hvb
  have hevsmall : ∀ i : Fin n, ∀ᶠ k in ↑(Filter.hyperfilter ℕ),
      ‖σ k (FreeGroup.of i) (ξ k + v k) - (ξ k + v k)‖ < 1 / 3 := by
    intro i
    have h1 : seqNorm (fun k ↦ v k -
        (σ k (FreeGroup.of i) (v k) + bseq (FreeGroup.of i) k)) <
        1 / 3 := by
      have hsq := hsmall i
      have hb : IsBoundedSeq (fun k ↦ v k -
          (σ k (FreeGroup.of i) (v k) + bseq (FreeGroup.of i) k)) := by
        refine hvb.sub ?_
        obtain ⟨Cv', hCv'⟩ := hvb
        refine ⟨Cv' + 1, fun k ↦ ?_⟩
        calc ‖σ k (FreeGroup.of i) (v k) + bseq (FreeGroup.of i) k‖ ≤
            ‖σ k (FreeGroup.of i) (v k)‖ +
              ‖bseq (FreeGroup.of i) k‖ := norm_add_le _ _
          _ = ‖v k‖ + ‖bseq (FreeGroup.of i) k‖ := by
              rw [(σ k _).norm_map]
          _ ≤ Cv' + 1 := add_le_add (hCv' k) (hgenbound i k)
      have heq := seqNormSq_eq_sq hb
      have h0 := seqNorm_nonneg hb
      nlinarith [hsq, hnum, heq]
    have hev := eventually_norm_lt_of_seqNorm_lt (by
      refine hvb.sub ?_
      obtain ⟨Cv', hCv'⟩ := hvb
      refine ⟨Cv' + 1, fun k ↦ ?_⟩
      calc ‖σ k (FreeGroup.of i) (v k) + bseq (FreeGroup.of i) k‖ ≤
          ‖σ k (FreeGroup.of i) (v k)‖ +
            ‖bseq (FreeGroup.of i) k‖ := norm_add_le _ _
        _ = ‖v k‖ + ‖bseq (FreeGroup.of i) k‖ := by
            rw [(σ k _).norm_map]
        _ ≤ Cv' + 1 := add_le_add (hCv' k) (hgenbound i k)) h1
    filter_upwards [hev] with k hk
    have hpt : σ k (FreeGroup.of i) (ξ k + v k) - (ξ k + v k) =
        -(v k - (σ k (FreeGroup.of i) (v k) +
          bseq (FreeGroup.of i) k)) := by
      simp only [hbseq]
      rw [map_add]
      abel
    rw [hpt, norm_neg]
    exact hk
  have hevall : ∀ᶠ k in ↑(Filter.hyperfilter ℕ), ∀ i : Fin n,
      ‖σ k (FreeGroup.of i) (ξ k + v k) - (ξ k + v k)‖ < 1 / 3 :=
    Filter.eventually_all.mpr hevsmall
  have hevnorm : ∀ᶠ k : ℕ in ↑(Filter.hyperfilter ℕ),
      (Cv : ℝ) ≤ (k : ℝ) := by
    filter_upwards [eventually_le_id ⌈Cv⌉₊] with k hk
    calc Cv ≤ (⌈Cv⌉₊ : ℝ) := Nat.le_ceil Cv
      _ ≤ (k : ℝ) := by exact_mod_cast hk
  have hfinal := (hevall.and hevnorm).exists
  obtain ⟨k, hkall, hknorm⟩ := hfinal
  have hζdisp : displacement (σ k) (generatorSet n)
      (generatorSet_nonempty hn) (ξ k + v k) ≤ 1 / 3 := by
    apply displacement_le
    intro q hq
    have hq' : ∃ i : Fin n, FreeGroup.of i = q := by
      simp only [generatorSet, Finset.mem_image, Finset.mem_univ,
        true_and] at hq
      obtain ⟨i, hi⟩ := hq
      exact ⟨i, hi⟩
    obtain ⟨i, rfl⟩ := hq'
    exact (hkall i).le
  have hζnear : ‖(ξ k + v k) - ξ k‖ ≤ (k : ℝ) + 1 := by
    rw [show (ξ k + v k) - ξ k = v k from by abel]
    calc ‖v k‖ ≤ Cv := hCv k
      _ ≤ (k : ℝ) := hknorm
      _ ≤ (k : ℝ) + 1 := by linarith
  have hcontra := hiso k (ξ k + v k) hζnear
  linarith

/-- **Shalom's theorem, presentation form** (Bekka–de la Harpe–Valette,
Theorem 3.4.5): every finitely generated group with Kazhdan's property
`(T)` is a quotient of a group presented by finitely many generators
and relators with property `(T)`.  The concrete presentation is exposed
so that further finite sets of relators can be imposed downstream. -/
theorem exists_presented_kazhdan_cover
    {G : Type u} [Group G] (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hT : HasKazhdanPropertyT.{u, u} G) :
    ∃ (n : ℕ) (rels : Finset (FreeGroup (Fin n)))
      (φ : PresentedGroup ((rels : Finset (FreeGroup (Fin n))) :
        Set (FreeGroup (Fin n))) →* G),
      Function.Surjective φ ∧
        HasKazhdanPropertyT.{0, 0}
          (PresentedGroup ((rels : Finset (FreeGroup (Fin n))) :
            Set (FreeGroup (Fin n)))) := by
  classical
  by_cases hS : S.card = 0
  · -- The trivial group covers itself.
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hS
    have htriv : ∀ g : G, g = 1 := by
      intro g
      have hmem : g ∈ Subgroup.closure ((S : Set G)) := by
        rw [hgen]
        exact Subgroup.mem_top g
      rw [hSempty] at hmem
      simpa using hmem
    haveI : Subsingleton (FreeGroup (Fin 0)) :=
      freeGroup_subsingleton_of_isEmpty
    haveI : Subsingleton (PresentedGroup
        ((∅ : Finset (FreeGroup (Fin 0))) : Set (FreeGroup (Fin 0)))) :=
      (PresentedGroup.mk_surjective _).subsingleton
    refine ⟨0, ∅, 1, ?_, hasKazhdanPropertyT_of_subsingleton⟩
    intro g
    exact ⟨1, by rw [htriv g]; rfl⟩
  · set n := S.card
    have hn0 : n ≠ 0 := hS
    set gens : Fin n → G := fun i ↦ (S.equivFin.symm i : G) with hgens
    set β : FreeGroup (Fin n) →* G := FreeGroup.lift gens with hβdef
    have hβ : Function.Surjective β := by
      rw [← MonoidHom.range_eq_top, ← top_le_iff, ← hgen,
        Subgroup.closure_le]
      intro g hg
      refine ⟨FreeGroup.of (S.equivFin ⟨g, hg⟩), ?_⟩
      rw [hβdef, FreeGroup.lift_apply_of, hgens]
      simp
    haveI : Nonempty ↥β.ker := ⟨⟨1, β.ker.one_mem⟩⟩
    obtain ⟨e, he⟩ := exists_surjective_nat ↥β.ker
    set rels : ℕ → Finset (FreeGroup (Fin n)) := fun k ↦
      (Finset.range (k + 1)).image fun j ↦
        ((e j : ↥β.ker) : FreeGroup (Fin n)) with hrels
    suffices hstage : ∃ k, HasKazhdanPropertyT.{0, 0}
        (PresentedGroup ((rels k : Finset (FreeGroup (Fin n))) :
          Set (FreeGroup (Fin n)))) by
      obtain ⟨k, hk⟩ := hstage
      have hkillrel : ∀ r ∈ ((rels k : Finset (FreeGroup (Fin n))) :
          Set (FreeGroup (Fin n))), FreeGroup.lift gens r = 1 := by
        intro r hr
        simp only [hrels, Finset.coe_image, Set.mem_image,
          Finset.mem_coe, Finset.mem_range] at hr
        obtain ⟨j, -, rfl⟩ := hr
        exact (e j).2
      have hcompeq : ∀ w : FreeGroup (Fin n),
          PresentedGroup.toGroup hkillrel (PresentedGroup.mk _ w) =
            FreeGroup.lift gens w := by
        intro w
        refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
        · rw [map_one, map_one, map_one]
        · intro i
          rw [show PresentedGroup.mk
              ((rels k : Finset (FreeGroup (Fin n))) :
                Set (FreeGroup (Fin n))) (FreeGroup.of i) =
              PresentedGroup.of i from rfl,
            PresentedGroup.toGroup.of, FreeGroup.lift_apply_of]
        · intro i hi
          rw [map_inv, map_inv, hi, ← map_inv]
        · intro a b ha hb
          rw [map_mul, map_mul, ha, hb, ← map_mul]
      refine ⟨n, rels k, PresentedGroup.toGroup hkillrel, ?_, hk⟩
      intro g
      obtain ⟨w, hw⟩ := hβ g
      refine ⟨PresentedGroup.mk _ w, ?_⟩
      rw [hcompeq w, ← hβdef, hw]
    by_contra hnostage
    push Not at hnostage
    have hfailpair : ∀ k : ℕ, ¬ IsKazhdanPair.{0, 0}
        (PresentedGroup ((rels k : Finset (FreeGroup (Fin n))) :
          Set (FreeGroup (Fin n))))
        ((Finset.univ : Finset (Fin n)).image fun i ↦
          PresentedGroup.of i)
        (1 / (4 * ((k : ℝ) + 1))) := by
      intro k hpair
      exact hnostage k ⟨_, _, hpair⟩
    have hwitness : ∀ k : ℕ, ∃ (E : Type)
        (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E),
        CompleteSpace E ∧ ∃ (ρ : PresentedGroup
          ((rels k : Finset (FreeGroup (Fin n))) :
            Set (FreeGroup (Fin n))) →* (E ≃ₗᵢ[ℝ] E)) (x : E),
        ‖x‖ = 1 ∧
          (∀ q ∈ (Finset.univ : Finset (Fin n)).image fun i ↦
            PresentedGroup.of i,
            ‖ρ q x - x‖ < 1 / (4 * ((k : ℝ) + 1))) ∧
          ∀ y : E, y ≠ 0 → ∃ γ, ρ γ y ≠ y := by
      intro k
      have h := hfailpair k
      simp only [IsKazhdanPair] at h
      push Not at h
      exact h (by positivity)
    choose Ek instNk instIk instCk ρ x hxnorm hxnear hxmoved
      using hwitness
    letI := instNk
    letI := instIk
    letI := instCk
    set σ : ∀ k, FreeGroup (Fin n) →* (Ek k ≃ₗᵢ[ℝ] Ek k) := fun k ↦
      (ρ k).comp (PresentedGroup.mk _)
    have hnoinv : ∀ k, ∀ y : Ek k, (∀ g, σ k g y = y) → y = 0 := by
      intro k y hy
      by_contra h0
      obtain ⟨γ, hγ⟩ := hxmoved k y h0
      obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ γ
      exact hγ (hy w)
    have hseed : ∀ k, displacement (σ k) (generatorSet n)
        (generatorSet_nonempty hn0) (x k) <
        1 / (4 * ((k : ℝ) + 1)) := by
      intro k
      have hsup : ∀ q ∈ generatorSet n,
          ‖σ k q (x k) - x k‖ < 1 / (4 * ((k : ℝ) + 1)) := by
        intro q hq
        simp only [generatorSet, Finset.mem_image, Finset.mem_univ,
          true_and] at hq
        obtain ⟨i, rfl⟩ := hq
        exact hxnear k (PresentedGroup.of i)
          (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      simp only [displacement]
      rw [Finset.sup'_lt_iff]
      intro q hq
      exact hsup q hq
    have hξpack := fun k ↦ exists_displacement_one_of_witness (σ k)
      (generatorSet n) (generatorSet_nonempty hn0)
      (closure_generatorSet n) (hnoinv k) ((k : ℝ) + 1)
      (by positivity) (hxnorm k) (hseed k)
    choose ξ hξ1 hξiso using hξpack
    have hkill : ∀ w ∈ β.ker, ∃ j : ℕ, ∀ k, j ≤ k → σ k w = 1 := by
      intro w hw
      obtain ⟨j, hj⟩ := he ⟨w, hw⟩
      refine ⟨j, fun k hk ↦ ?_⟩
      have hwmem : w ∈ rels k := by
        simp only [hrels]
        refine Finset.mem_image.mpr
          ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
        rw [hj]
      show (ρ k).comp (PresentedGroup.mk _) w = 1
      rw [MonoidHom.comp_apply,
        PresentedGroup.one_of_mem (Finset.mem_coe.mpr hwmem), map_one]
    obtain ⟨Q, ε', hQpair⟩ := hT
    exact core_contradiction hn0 β hβ hQpair Ek instNk instIk σ hkill ξ
      hξ1 (fun k η hη ↦ hξiso k η hη)

/-- **Shalom's theorem** (Bekka–de la Harpe–Valette, Theorem 3.4.5):
every finitely generated group with Kazhdan's property `(T)` is a
quotient of a finitely presented group with property `(T)`. -/
theorem exists_finitelyPresented_kazhdan_cover
    {G : Type u} [Group G] (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hT : HasKazhdanPropertyT.{u, u} G) :
    ∃ (Γ : Type) (_ : Group Γ) (φ : Γ →* G),
      Function.Surjective φ ∧ Group.IsFinitelyPresented Γ ∧
        HasKazhdanPropertyT.{0, 0} Γ := by
  obtain ⟨n, rels, φ, hsurj, hT'⟩ :=
    exists_presented_kazhdan_cover S hgen hT
  exact ⟨_, inferInstance, φ, hsurj, inferInstance, hT'⟩

end Shalom
end NonsoficGroupsExist
