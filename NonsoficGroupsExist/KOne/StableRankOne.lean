import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Stable rank one for matrices over a field

If the ranges of two endomorphisms of a finite-dimensional vector
space jointly span, some perturbation `f + g∘t` is invertible: choose
a complement `W` of `range f`, note `dim W = dim (ker f)` by
rank–nullity, and send `ker f` through `W`-covering preimages of `g`.
In matrix form: `A·Z₀ + B·Z₁ = 1` implies `A + B·T` is invertible for
some `T`.  This is the pivot-producing engine for the residual-class
endgame of the rose-graph `K₁` computation.
-/

namespace NonsoficGroupsExist

open Module LinearMap

theorem exists_isUnit_add_comp_of_sup_range {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f g : Module.End k V)
    (hsup : LinearMap.range f ⊔ LinearMap.range g = ⊤) :
    ∃ t : Module.End k V, IsUnit (f + g * t) := by
  classical
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range f)
  -- the projection onto W along range f
  set πW := Submodule.projectionOnto W (LinearMap.range f) hW.symm with hπW
  -- πW ∘ g is surjective onto W
  have hsurj : Function.Surjective (πW ∘ₗ g) := by
    intro w
    have hw : (w : V) ∈ LinearMap.range f ⊔ LinearMap.range g := by
      rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
    obtain ⟨u, rfl⟩ := hb
    refine ⟨u, ?_⟩
    have h1 : πW (g u) = πW (w : V) - πW a := by
      rw [← map_sub]
      congr 1
      rw [← hab]
      abel
    have h2 : πW a = 0 := by
      rw [hπW]
      exact Submodule.projectionOnto_apply_right hW.symm ⟨a, ha⟩
    have h3 : πW (w : V) = w := by
      rw [hπW]
      exact Submodule.projectionOnto_apply_left hW.symm w
    simp only [LinearMap.comp_apply]
    rw [h1, h2, h3, sub_zero]
  -- a linear section of πW ∘ g
  obtain ⟨s, hs⟩ := (πW ∘ₗ g).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  -- ker f ≃ W by rank–nullity
  have hdim : finrank k (LinearMap.ker f) = finrank k W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    omega
  obtain ⟨φ⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hdim
  -- the projection onto ker f along K'
  set πK := Submodule.projectionOnto (LinearMap.ker f) K' hK with hπK
  set t : Module.End k V := s ∘ₗ (φ : LinearMap.ker f →ₗ[k] W) ∘ₗ πK
    with ht
  refine ⟨t, ?_⟩
  rw [Module.End.isUnit_iff]
  rw [show f + g * t = f + g ∘ₗ t from rfl]
  have hinj : Function.Injective (f + g ∘ₗ t) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.comp_apply]
      at hv
    -- apply πW to the relation
    have h0 := congrArg πW hv
    rw [map_add, map_zero] at h0
    have hfv : πW (f v) = 0 := by
      rw [hπW]
      exact Submodule.projectionOnto_apply_right hW.symm
        ⟨f v, LinearMap.mem_range_self f v⟩
    have hgt : πW (g (t v)) = φ (πK v) := by
      have h4 := LinearMap.congr_fun hs (φ (πK v))
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h4
      rw [ht]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      exact h4
    rw [hfv, hgt, zero_add] at h0
    -- so φ (πK v) = 0, hence πK v = 0, hence t v = 0, hence f v = 0
    have hφ0 : φ (πK v) = 0 := by
      exact_mod_cast h0
    have hπK0 : πK v = 0 := by
      have := congrArg φ.symm hφ0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this
    have htv : t v = 0 := by
      rw [ht]
      simp only [LinearMap.comp_apply, hπK0, map_zero]
    rw [htv, map_zero, add_zero] at hv
    -- v ∈ ker f and πK v = 0 force v = 0
    have hvker : v ∈ LinearMap.ker f := LinearMap.mem_ker.mpr hv
    have hfix : πK v = ⟨v, hvker⟩ := by
      rw [hπK]
      exact Submodule.projectionOnto_apply_left hK ⟨v, hvker⟩
    rw [hπK0] at hfix
    have h5 : (⟨v, hvker⟩ : LinearMap.ker f) = 0 := hfix.symm
    exact congrArg (fun z : LinearMap.ker f ↦ (z : V)) h5
  exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

/-- **Stable rank one for matrix algebras over a field**: a
right-unimodular pair admits an invertible perturbation. -/
theorem exists_isUnit_add_mul_of_unimodular {k : Type*} [Field k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B Z₀ Z₁ : Matrix ι ι k) (h : A * Z₀ + B * Z₁ = 1) :
    ∃ T : Matrix ι ι k, IsUnit (A + B * T) := by
  classical
  set e := Matrix.toLinAlgEquiv' (n := ι) (R := k) with he
  have hsup : LinearMap.range (e A) ⊔ LinearMap.range (e B) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = (e A) ((e Z₀) v) + (e B) ((e Z₁) v) := by
      have h1 := congrArg e h
      rw [map_add, map_mul, map_mul, map_one] at h1
      have h2 := LinearMap.congr_fun h1 v
      simpa using h2.symm
    rw [hv]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (LinearMap.mem_range_self _ _)
  obtain ⟨t, hunit⟩ := exists_isUnit_add_comp_of_sup_range (e A) (e B)
    hsup
  refine ⟨e.symm t, ?_⟩
  have hmap : e (A + B * e.symm t) = e A + e B * t := by
    rw [map_add, map_mul, AlgEquiv.apply_symm_apply]
  have hu2 := hunit
  rw [← hmap] at hu2
  have hfinal := hu2.map e.symm
  rwa [AlgEquiv.symm_apply_apply] at hfinal

/-- Rectangular refinement: the perturbing map may have any
finite-dimensional source. -/
theorem exists_bijective_add_comp_of_sup_range' {k V W : Type*}
    [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] V) (g : W →ₗ[k] V)
    (hsup : LinearMap.range f ⊔ LinearMap.range g = ⊤) :
    ∃ t : V →ₗ[k] W, Function.Bijective (f + g ∘ₗ t) := by
  classical
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  obtain ⟨W', hW⟩ := Submodule.exists_isCompl (LinearMap.range f)
  set πW := Submodule.projectionOnto W' (LinearMap.range f) hW.symm
    with hπW
  have hsurj : Function.Surjective (πW ∘ₗ g) := by
    intro w
    have hw : (w : V) ∈ LinearMap.range f ⊔ LinearMap.range g := by
      rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
    obtain ⟨u, rfl⟩ := hb
    refine ⟨u, ?_⟩
    have h1 : πW (g u) = πW (w : V) - πW a := by
      rw [← map_sub]
      congr 1
      rw [← hab]
      abel
    have h2 : πW a = 0 := by
      rw [hπW]
      exact Submodule.projectionOnto_apply_right hW.symm ⟨a, ha⟩
    have h3 : πW (w : V) = w := by
      rw [hπW]
      exact Submodule.projectionOnto_apply_left hW.symm w
    simp only [LinearMap.comp_apply]
    rw [h1, h2, h3, sub_zero]
  obtain ⟨s, hs⟩ := (πW ∘ₗ g).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  have hdim : finrank k (LinearMap.ker f) = finrank k W' := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    omega
  obtain ⟨φ⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hdim
  set πK := Submodule.projectionOnto (LinearMap.ker f) K' hK with hπK
  set t : V →ₗ[k] W := s ∘ₗ (φ : LinearMap.ker f →ₗ[k] W') ∘ₗ πK
    with ht
  refine ⟨t, ?_⟩
  have hinj : Function.Injective (f + g ∘ₗ t) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.comp_apply]
      at hv
    have h0 := congrArg πW hv
    rw [map_add, map_zero] at h0
    have hfv : πW (f v) = 0 := by
      rw [hπW]
      exact Submodule.projectionOnto_apply_right hW.symm
        ⟨f v, LinearMap.mem_range_self f v⟩
    have hgt : πW (g (t v)) = φ (πK v) := by
      have h4 := LinearMap.congr_fun hs (φ (πK v))
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h4
      rw [ht]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      exact h4
    rw [hfv, hgt, zero_add] at h0
    have hφ0 : φ (πK v) = 0 := by
      exact_mod_cast h0
    have hπK0 : πK v = 0 := by
      have := congrArg φ.symm hφ0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this
    have htv : t v = 0 := by
      rw [ht]
      simp only [LinearMap.comp_apply, hπK0, map_zero]
    rw [htv, map_zero, add_zero] at hv
    have hvker : v ∈ LinearMap.ker f := LinearMap.mem_ker.mpr hv
    have hfix : πK v = ⟨v, hvker⟩ := by
      rw [hπK]
      exact Submodule.projectionOnto_apply_left hK ⟨v, hvker⟩
    rw [hπK0] at hfix
    have h5 : (⟨v, hvker⟩ : LinearMap.ker f) = 0 := hfix.symm
    exact congrArg (fun z : LinearMap.ker f ↦ (z : V)) h5
  exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩

/-- **Rectangular stable rank one for matrices over a field**. -/
theorem exists_isUnit_add_mul_of_unimodular' {k : Type*} [Field k]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A Z₀ : Matrix ι ι k) (B : Matrix ι κ k)
    (Z₁ : Matrix κ ι k) (h : A * Z₀ + B * Z₁ = 1) :
    ∃ T : Matrix κ ι k, IsUnit (A + B * T) := by
  classical
  have hsup : LinearMap.range (Matrix.toLin' A) ⊔
      LinearMap.range (Matrix.toLin' B) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = Matrix.toLin' A (Matrix.toLin' Z₀ v) +
        Matrix.toLin' B (Matrix.toLin' Z₁ v) := by
      have h1 := congrArg Matrix.toLin' h
      rw [map_add, Matrix.toLin'_mul, Matrix.toLin'_mul,
        Matrix.toLin'_one] at h1
      have h2 := LinearMap.congr_fun h1 v
      simpa using h2.symm
    rw [hv]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (LinearMap.mem_range_self _ _)
  obtain ⟨t, hbij⟩ := exists_bijective_add_comp_of_sup_range'
    (Matrix.toLin' A) (Matrix.toLin' B) hsup
  refine ⟨LinearMap.toMatrix' t, ?_⟩
  have hmap : Matrix.toLin' (A + B * LinearMap.toMatrix' t) =
      Matrix.toLin' A + Matrix.toLin' B ∘ₗ t := by
    rw [map_add, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  have hunit : IsUnit (Matrix.toLinAlgEquiv'
      (A + B * LinearMap.toMatrix' t)) := by
    rw [Module.End.isUnit_iff]
    have hsame : (Matrix.toLinAlgEquiv'
        (A + B * LinearMap.toMatrix' t) :
        (ι → k) →ₗ[k] (ι → k)) =
        Matrix.toLin' (A + B * LinearMap.toMatrix' t) := rfl
    rw [hsame, hmap]
    exact hbij
  have hfinal := hunit.map Matrix.toLinAlgEquiv'.symm
  rwa [AlgEquiv.symm_apply_apply] at hfinal


end NonsoficGroupsExist
