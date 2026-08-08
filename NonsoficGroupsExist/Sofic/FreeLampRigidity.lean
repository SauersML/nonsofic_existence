import NonsoficGroupsExist.Sofic.FreeLampReduction
import NonsoficGroupsExist.Criterion.CommutantRigidity

/-!
# Finite-dimensional representations kill the free-lamp witness

The confinement half of the free-lamp story, unconditionally.  For an
infranormal pair — the compressors of `Γ` generate `G` — every
finite-dimensional representation of the amalgam `H_K = G *_Γ (Γ × K)`, over
any field, by any invertible operators, kills the witness commutator
`lampWitness t γ k`.  Combined with `lampWitness_ne_one` this says the
free-lamp groups admit no faithful finite-dimensional representation at all:
any hyperlinear model, if one exists, must be genuinely approximate — it
cannot arise from honest finite-dimensional representations that remain
faithful on the witness.

The mechanism is the co-Hopfian rigidity already formalized in
`CommutantRigidity`: in finite dimension the commutant of `π(Γ)` does not
grow under compression, so each compressor — and hence, by generation, every
element of `G` — stabilizes it.  The lamp lies in the commutant because it
centralizes `Γ`; its `t`-conjugate therefore stays in the commutant and
commutes with `π(γ)`, and the witness dies.  No property `(T)`, no trace, no
unitarity: only the finite dimension.

This is exactly what fails in a `II₁` factor, which is not co-Hopfian — and
that failure is the entire remaining hope of the hyperlinear side of the
free-lamp program.  What is proved here confines that hope to genuinely
non-liftable models; the operator-ultraproduct sharpenings of the same
confinement are not formalized and not claimed.
-/

namespace NonsoficGroupsExist

variable {G : Type} {k V : Type*} [Group G] [Field k] [AddCommGroup V]
  [Module k V]

/-! ## The commutant stabilizer -/

/-- Composition law for the adjoint action, in applied form. -/
theorem adjointRep_mul_apply (ρ : G →* (V ≃ₗ[k] V)) (a b : G)
    (y : V →ₗ[k] V) :
    adjointRep ρ (a * b) y = adjointRep ρ a (adjointRep ρ b y) := by
  rw [map_mul, LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply]

/-- The identity acts trivially, in applied form. -/
theorem adjointRep_one_apply (ρ : G →* (V ≃ₗ[k] V)) (y : V →ₗ[k] V) :
    adjointRep ρ (1 : G) y = y := by
  rw [map_one]
  rfl

/-- The elements whose adjoint action preserves the commutant of `ρ(Γ)`, in
both directions, as a subgroup. -/
def commutantStabilizer (ρ : G →* (V ≃ₗ[k] V)) (Γ : Subgroup G) :
    Subgroup G where
  carrier := {g | ∀ x : V →ₗ[k] V,
    (∀ δ ∈ Γ, adjointRep ρ δ (adjointRep ρ g x) = adjointRep ρ g x)
      ↔ ∀ δ ∈ Γ, adjointRep ρ δ x = x}
  one_mem' := by
    intro x
    rw [adjointRep_one_apply]
  mul_mem' := by
    intro a b ha hb x
    have h2 := ha (adjointRep ρ b x)
    have h1 := hb x
    rw [adjointRep_mul_apply]
    exact h2.trans h1
  inv_mem' := by
    intro a ha x
    have h := ha (adjointRep ρ a⁻¹ x)
    have hcancel : adjointRep ρ a (adjointRep ρ a⁻¹ x) = x := by
      rw [← adjointRep_mul_apply, mul_inv_cancel, adjointRep_one_apply]
    rw [hcancel] at h
    exact h.symm

/-- Conjugating the adjoint fixed-point equation: `Ad (sδs⁻¹)` fixes `x`
exactly when `Ad δ` fixes `Ad (s⁻¹) x`. -/
theorem adjointRep_conj_fixed_iff (ρ : G →* (V ≃ₗ[k] V)) (s δ : G)
    (x : V →ₗ[k] V) :
    adjointRep ρ (s * δ * s⁻¹) x = x
      ↔ adjointRep ρ δ (adjointRep ρ s⁻¹ x) = adjointRep ρ s⁻¹ x := by
  constructor
  · intro h
    have h2 := congrArg (adjointRep ρ s⁻¹) h
    have h3 : adjointRep ρ s⁻¹ (adjointRep ρ (s * δ * s⁻¹) x)
        = adjointRep ρ δ (adjointRep ρ s⁻¹ x) := by
      rw [← adjointRep_mul_apply, ← adjointRep_mul_apply]
      have harr : s⁻¹ * (s * δ * s⁻¹) = δ * s⁻¹ := by group
      rw [harr]
    rw [h3] at h2
    exact h2
  · intro h
    have h2 := congrArg (adjointRep ρ s) h
    have h3 : adjointRep ρ s (adjointRep ρ δ (adjointRep ρ s⁻¹ x))
        = adjointRep ρ (s * δ * s⁻¹) x := by
      rw [adjointRep_mul_apply ρ (s * δ) s⁻¹,
        adjointRep_mul_apply ρ s δ]
    have h4 : adjointRep ρ s (adjointRep ρ s⁻¹ x) = x := by
      rw [← adjointRep_mul_apply, mul_inv_cancel, adjointRep_one_apply]
    rw [h3, h4] at h2
    exact h2

/-- **Compressors stabilize the commutant.**  In finite dimension, the
commutant rigidity of `CommutantRigidity` says exactly that the inverse of a
compressor of `Γ` lies in the stabilizer. -/
theorem inv_compressor_mem_commutantStabilizer [FiniteDimensional k V]
    (ρ : G →* (V ≃ₗ[k] V)) (Γ : Subgroup G) {s : G}
    (hs : ∀ δ ∈ Γ, s * δ * s⁻¹ ∈ Γ) :
    s⁻¹ ∈ commutantStabilizer ρ Γ := by
  intro x
  have hcng := commutant_no_growth ρ Γ hs x
  constructor
  · intro h
    refine hcng.mp fun δ hδ ↦ ?_
    exact (adjointRep_conj_fixed_iff ρ s δ x).mpr (h δ hδ)
  · intro h δ hδ
    exact (adjointRep_conj_fixed_iff ρ s δ x).mp (hcng.mpr h δ hδ)

/-- If the compressors of `Γ` generate `G`, every element stabilizes the
commutant. -/
theorem commutantStabilizer_eq_top [FiniteDimensional k V]
    (ρ : G →* (V ≃ₗ[k] V)) (Γ : Subgroup G) (S : Set G)
    (hS : ∀ s ∈ S, ∀ δ ∈ Γ, s * δ * s⁻¹ ∈ Γ)
    (hgen : Subgroup.closure S = ⊤) :
    commutantStabilizer ρ Γ = ⊤ := by
  rw [← top_le_iff, ← hgen, Subgroup.closure_le]
  intro s hsS
  have hmem := inv_compressor_mem_commutantStabilizer ρ Γ (hS s hsS)
  simpa using (commutantStabilizer ρ Γ).inv_mem hmem

/-! ## The collapse -/

variable (G) (Γ' : Subgroup G) (K : Type) [Group K]

/-- **Every finite-dimensional representation kills the witness.**  For an
infranormal pair — compressors of `Γ` generating `G` — and any
representation of the free-lamp amalgam by invertible operators on a
finite-dimensional space, over any field, the witness commutator dies. -/
theorem freeLampRep_kills_witness [FiniteDimensional k V]
    (S : Set G) (hS : ∀ s ∈ S, ∀ δ ∈ Γ', s * δ * s⁻¹ ∈ Γ')
    (hgen : Subgroup.closure S = ⊤)
    (π : FreeLamp G Γ' K →* (V ≃ₗ[k] V)) (t γ : G) (hγ : γ ∈ Γ')
    (k' : K) : π (lampWitness G Γ' K t γ k') = 1 := by
  classical
  have hinv : ∀ e : V ≃ₗ[k] V, (e⁻¹ : V ≃ₗ[k] V) = e.symm := by
    intro e
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [LinearEquiv.mul_eq_trans, LinearEquiv.self_trans_symm]
    rfl
  set ρ : G →* (V ≃ₗ[k] V) := π.comp (inAmbient G Γ' K) with hρ
  set x : V →ₗ[k] V := (π (inLamp G Γ' K k') : V →ₗ[k] V) with hx
  -- the lamp lies in the commutant of `ρ(Γ)`
  have hcomm : ∀ δ ∈ Γ', adjointRep ρ δ x = x := by
    intro δ hδ
    rw [adjointRep_fixed_iff_commute]
    have hc := ((inLamp_commute_inAmbient G Γ' K k' hδ).map π).symm.eq
    ext v
    have hv := congrArg (fun e : V ≃ₗ[k] V ↦ e v) hc
    simp only [hρ, hx, MonoidHom.comp_apply]
    simpa [LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe] using hv
  -- every element of `G` stabilizes the commutant
  have htop := commutantStabilizer_eq_top ρ Γ' S hS hgen
  have hts : t ∈ commutantStabilizer ρ Γ' := by
    rw [htop]
    trivial
  have hty := ((hts x).mpr hcomm) γ hγ
  rw [adjointRep_fixed_iff_commute] at hty
  simp only [hρ, hx, MonoidHom.comp_apply, adjointRep_apply] at hty
  -- the transported lamp commutes with `π (inAmbient γ)`
  have hkey : ∀ a b : V ≃ₗ[k] V, a * b = b * a → a * b * a⁻¹ * b⁻¹ = 1 := by
    intro a b hab
    rw [hab]
    group
  have hcommute : π (inAmbient G Γ' K t) * π (inLamp G Γ' K k')
        * (π (inAmbient G Γ' K t))⁻¹ * π (inAmbient G Γ' K γ)
      = π (inAmbient G Γ' K γ) * (π (inAmbient G Γ' K t)
        * π (inLamp G Γ' K k') * (π (inAmbient G Γ' K t))⁻¹) := by
    refine LinearEquiv.ext fun v ↦ ?_
    have hpt := congrArg (fun f : V →ₗ[k] V ↦ f v) hty
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hpt
    rw [hinv (π (inAmbient G Γ' K t))]
    simp only [LinearEquiv.mul_eq_trans, LinearEquiv.trans_apply]
    exact hpt.symm
  simp only [lampWitness, map_mul, map_inv]
  exact hkey _ _ hcommute

/-- **The free-lamp amalgam has no faithful finite-dimensional
representation** over any field, once the witness data exists: a nontrivial
lamp and a `γ ∈ Γ` moved out of `Γ` by some `t⁻¹ · t`.  In particular it is
not maximally almost periodic, and no hyperlinear model of it can consist of
genuine finite-dimensional representations faithful on the witness. -/
theorem freeLampRep_not_injective [FiniteDimensional k V]
    (S : Set G) (hS : ∀ s ∈ S, ∀ δ ∈ Γ', s * δ * s⁻¹ ∈ Γ')
    (hgen : Subgroup.closure S = ⊤)
    (π : FreeLamp G Γ' K →* (V ≃ₗ[k] V)) {t γ : G} (hγ : γ ∈ Γ')
    (hesc : t⁻¹ * γ * t ∉ Γ') {k' : K} (hk : k' ≠ 1) :
    ¬ Function.Injective π := by
  intro hinj
  refine lampWitness_ne_one G Γ' K hesc hk (hinj ?_)
  rw [freeLampRep_kills_witness G Γ' K S hS hgen π t γ hγ k', map_one]

end NonsoficGroupsExist
