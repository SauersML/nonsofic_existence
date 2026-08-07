import NonsoficGroupsExist.Criterion.ExactCompression

/-!
# The commutant does not grow under compression

`ExactCompression` shows that a one-sided compression `tΓt⁻¹ ≤ Γ` acts *onto*
the `Γ`-fixed points of a finite set or a finite-dimensional space.  The form
the approximation-theoretic literature consumes is about *commutants*: for a
genuine finite-dimensional representation `π` and a compressor `t`, does the
commutant grow when `Γ` is replaced by its compressed copy?

  `π(tΓt⁻¹)′ = π(Γ)′ ?`

It does not, and the proof is not a new argument.  The commutant of `π(Γ)`
inside `End V` is exactly the fixed-point space of the *adjoint* representation
`Ad π : G → GL(End V)`, `g ↦ (x ↦ π g ∘ x ∘ π g⁻¹)`.  So commutant rigidity is
`fixedSubmodule_compressed_eq` applied to `Ad π` rather than to `π`, and the
same co-Hopfian step closes it: a subspace inside its own injective image
equals it.

## Why this is the statement that matters

Write `𝓜 = ∏_𝒰 M_{d_n}` and let `ρ : Λ → U(𝓜)` be a hyperlinear embedding of
a wreath product `(⊕_{G/Γ} ℤ/2) ⋊ G`.  The lamp at the base coset commutes with
`ρ(Γ)`, so it lies in the relative commutant `N₀ = ρ(Γ)′ ∩ 𝓜`.  A compressor
carries `N₀` into `ρ(tΓt⁻¹)′ ∩ 𝓜 ⊇ N₀`, and if that inclusion were an
equality for the compressors generating `G`, then `ρ(G)` would normalize `N₀`,
forcing two distinct lamps to have equal image and contradicting trace
separation.  The entire question is whether the inclusion is strict.

`commutant_no_growth` says it is *not* strict in finite dimension.  That is why
the argument closes for genuine finite-dimensional representations, and -- via
a flexible-stability lifting -- for any hyperlinear embedding that is a
pointwise limit of them.  It is also exactly where the argument stops: a `II₁`
factor is not co-Hopfian, so the same inclusion may be strict there, with the
trace, being preserved, counting nothing.
-/

namespace NonsoficGroupsExist

variable {G k V : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]

/-- The adjoint representation on endomorphisms, `x ↦ π g ∘ x ∘ π g⁻¹`. -/
def adjointRep (π : G →* (V ≃ₗ[k] V)) : G →* ((V →ₗ[k] V) ≃ₗ[k] (V →ₗ[k] V)) where
  toFun g :=
    { toFun := fun x ↦ (π g : V →ₗ[k] V) ∘ₗ x ∘ₗ ((π g).symm : V →ₗ[k] V)
      map_add' := by intro x y; ext v; simp
      map_smul' := by intro c x; ext v; simp
      invFun := fun x ↦ ((π g).symm : V →ₗ[k] V) ∘ₗ x ∘ₗ (π g : V →ₗ[k] V)
      left_inv := by intro x; ext v; simp
      right_inv := by intro x; ext v; simp }
  map_one' := by
    ext x v
    simp [LinearEquiv.one_eq_refl]
  map_mul' := by
    intro g h
    ext x v
    simp [LinearEquiv.mul_eq_trans]

@[simp] theorem adjointRep_apply (π : G →* (V ≃ₗ[k] V)) (g : G) (x : V →ₗ[k] V) :
    adjointRep π g x = (π g : V →ₗ[k] V) ∘ₗ x ∘ₗ ((π g).symm : V →ₗ[k] V) := rfl

/-- Being fixed by the adjoint action of `γ` is commuting with `π γ`.  This is
the identification that turns commutant rigidity into `ExactCompression`. -/
theorem adjointRep_fixed_iff_commute (π : G →* (V ≃ₗ[k] V)) (γ : G)
    (x : V →ₗ[k] V) :
    adjointRep π γ x = x ↔
      (π γ : V →ₗ[k] V) ∘ₗ x = x ∘ₗ (π γ : V →ₗ[k] V) := by
  constructor
  · intro h
    ext v
    have hv := congrArg (fun f : V →ₗ[k] V ↦ f ((π γ) v)) h
    simpa using hv
  · intro h
    ext v
    have hv := congrArg (fun f : V →ₗ[k] V ↦ f ((π γ).symm v)) h
    simpa using hv

/-- **Commutant rigidity.**  For a genuine representation on a
finite-dimensional space, an endomorphism commuting with the compressed copy
`π(tΓt⁻¹)` already commutes with `π(Γ)`: the commutant does not grow.  No
expansion, no property `(T)`, no trace -- only the co-Hopfianity of finite
dimension. -/
theorem commutant_no_growth [FiniteDimensional k V] (π : G →* (V ≃ₗ[k] V))
    (Γ : Subgroup G) {t : G} (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) (x : V →ₗ[k] V) :
    (∀ γ ∈ Γ, adjointRep π (t * γ * t⁻¹) x = x) ↔
      ∀ γ ∈ Γ, adjointRep π γ x = x :=
  fixedSubmodule_compressed_eq (adjointRep π) Γ ht x

/-- The same, written with commutators rather than through the adjoint
representation. -/
theorem commutant_no_growth' [FiniteDimensional k V] (π : G →* (V ≃ₗ[k] V))
    (Γ : Subgroup G) {t : G} (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) (x : V →ₗ[k] V) :
    (∀ γ ∈ Γ, (π (t * γ * t⁻¹) : V →ₗ[k] V) ∘ₗ x
        = x ∘ₗ (π (t * γ * t⁻¹) : V →ₗ[k] V))
      ↔ ∀ γ ∈ Γ, (π γ : V →ₗ[k] V) ∘ₗ x = x ∘ₗ (π γ : V →ₗ[k] V) := by
  constructor
  · intro hx γ hγ
    rw [← adjointRep_fixed_iff_commute]
    refine (commutant_no_growth π Γ ht x).mp (fun δ hδ ↦ ?_) γ hγ
    rw [adjointRep_fixed_iff_commute]
    exact hx δ hδ
  · intro hx γ hγ
    exact hx _ (ht γ hγ)

end NonsoficGroupsExist
