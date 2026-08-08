import NonsoficGroupsExist.Criterion.FiniteQuotientBlindness

/-!
# The profinite closure of a compressed subgroup

Two facts about the profinite closure `Γ*` of a subgroup `Γ` — the elements
that every homomorphism to a finite group maps into the image of `Γ` — both
of which the free-lamp analysis leans on, and which together decide a
question the August 2026 discussions contested.

* **The closure swallows the normal closure**
  (`normalClosure_le_profiniteClosure`): when the compressors of `Γ`
  generate the ambient group, every finite quotient makes the image of `Γ`
  normal — the blindness theorem of `FiniteQuotientBlindness` — so the
  profinite closure contains the entire normal closure of `Γ`.  For a
  non-normal `Γ` the containment `Γ ⊊ ⟨⟨Γ⟩⟩ ≤ Γ*` is strict: `Γ` is not
  separable, which is why the separability-based amalgam theorems of 2026
  cannot reach the free-lamp groups.

* **A single separating quotient certifies exclusion**
  (`not_mem_profiniteClosure_of_kills`): an element with a finite quotient
  killing `Γ` but not it lies outside `Γ*`, however completely the closure
  swallows the normal closure.  For the explicit Kun--Thom pairs
  `EL_r(𝔽_q[x̄^{±1}]) ⋊ SL_d(ℤ)` this settles where the compressors live:
  they sit in the `SL_d(ℤ)`-factor, the projection to `SL_d(ℤ/N)` kills
  `Γ = EL_r(𝔽_q[x̄])` and keeps a compressor alive, so **compressors are
  not in the profinite closure** — the closure is confined to the Laurent
  factor.  (The instantiation to those explicit groups is paper-level; what
  is formalized here is the criterion that makes it a one-line check.)
-/

namespace NonsoficGroupsExist

variable {G : Type*} [Group G]

/-- The profinite closure of a subgroup: the elements that every
homomorphism to a finite group maps into the image of the subgroup. -/
def profiniteClosure (Γ : Subgroup G) : Subgroup G where
  carrier := {g | ∀ (Q : Type) [Group Q] [Finite Q] (ψ : G →* Q),
    ψ g ∈ Γ.map ψ}
  one_mem' := by
    intro Q _ _ ψ
    rw [map_one]
    exact Subgroup.one_mem _
  mul_mem' := by
    intro a b ha hb Q _ _ ψ
    rw [map_mul]
    exact Subgroup.mul_mem _ (ha Q ψ) (hb Q ψ)
  inv_mem' := by
    intro a ha Q _ _ ψ
    rw [map_inv]
    exact Subgroup.inv_mem _ (ha Q ψ)

theorem le_profiniteClosure (Γ : Subgroup G) : Γ ≤ profiniteClosure Γ :=
  fun _ hg _ _ _ ψ => Subgroup.mem_map_of_mem ψ hg

/-- Positive control: the closure of everything is everything. -/
theorem profiniteClosure_top : profiniteClosure (⊤ : Subgroup G) = ⊤ :=
  top_le_iff.mp (le_profiniteClosure ⊤)

/-- **A separating finite quotient certifies exclusion**: if some finite
quotient maps `t` outside the image of `Γ`, then `t` is not in the
profinite closure. -/
theorem not_mem_profiniteClosure {Q : Type} [Group Q] [Finite Q]
    (Γ : Subgroup G) (ψ : G →* Q) {t : G} (hsep : ψ t ∉ Γ.map ψ) :
    t ∉ profiniteClosure Γ :=
  fun hmem => hsep (hmem Q ψ)

/-- The kernel form: a finite quotient killing `Γ` but not `t` places `t`
outside the profinite closure.  This is the shape in which the criterion
applies to split pairs: project away the factor containing `Γ` and separate
`t` in a finite quotient of what remains. -/
theorem not_mem_profiniteClosure_of_kills {Q : Type} [Group Q] [Finite Q]
    (Γ : Subgroup G) (ψ : G →* Q) (hΓ : ∀ γ ∈ Γ, ψ γ = 1) {t : G}
    (ht : ψ t ≠ 1) : t ∉ profiniteClosure Γ := by
  refine not_mem_profiniteClosure Γ ψ ?_
  rintro ⟨γ, hγ, hψγ⟩
  exact ht (hψγ ▸ hΓ γ hγ)

/-- **The closure swallows the normal closure.**  When the compressors of
`Γ` generate `G`, every finite quotient normalizes the image of `Γ` — the
blindness theorem — so the whole normal closure of `Γ` lies in the
profinite closure.  For non-normal `Γ` this is exactly the failure of
separability. -/
theorem normalClosure_le_profiniteClosure (Γ : Subgroup G) (S : Set G)
    (hS : ∀ s ∈ S, ∀ γ ∈ Γ, s * γ * s⁻¹ ∈ Γ)
    (hgen : Subgroup.closure S = ⊤) :
    Subgroup.normalClosure (Γ : Set G) ≤ profiniteClosure Γ := by
  intro g hg Q _ _ ψ
  -- every element of `G` maps into the normalizer of the image of `Γ`
  have hnormalize : ∀ x : G,
      ψ x ∈ Subgroup.normalizer ((Γ.map ψ : Set Q)) := by
    have hle : Subgroup.closure S
        ≤ (Subgroup.normalizer ((Γ.map ψ : Set Q))).comap ψ := by
      rw [Subgroup.closure_le]
      intro s hsS
      have hmem : ψ s ∈ Subgroup.normalizer ((Γ.map ψ : Set Q)) := by
        rw [Subgroup.mem_set_normalizer_iff]
        intro q
        constructor
        · intro hq
          exact compressorImage_normalizes ψ Γ (hS s hsS) q hq
        · intro hq
          have h2 := compressorImage_normalizes_inv ψ Γ (hS s hsS) _ hq
          have h3 : (ψ s)⁻¹ * (ψ s * q * (ψ s)⁻¹) * ψ s = q := by
            group
          rwa [h3] at h2
      exact hmem
    intro x
    have hx : x ∈ Subgroup.closure S := by
      rw [hgen]
      trivial
    exact hle hx
  -- so the comap of the image is a normal subgroup containing `Γ`
  haveI : ((Γ.map ψ).comap ψ).Normal := by
    refine ⟨fun x hx g' => ?_⟩
    have hx' : ψ x ∈ Γ.map ψ := hx
    have hmem := (Subgroup.mem_set_normalizer_iff.mp (hnormalize g')
      (ψ x)).mp hx'
    show ψ (g' * x * g'⁻¹) ∈ Γ.map ψ
    rw [map_mul, map_mul, map_inv]
    exact hmem
  have hsub : (Γ : Set G) ⊆ ((Γ.map ψ).comap ψ : Set G) :=
    fun γ hγ => Subgroup.mem_map_of_mem ψ hγ
  exact Subgroup.normalClosure_le_normal hsub hg

end NonsoficGroupsExist
