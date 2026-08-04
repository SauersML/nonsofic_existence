import NonsoficGroupsExist.HilbertEpsilonOrthogonality
import NonsoficGroupsExist.KazhdanFixedSpace

/-!
# The normal-edge local codistance estimate

This file proves the `1/2` half of the local estimate in the EJZ six-vertex
argument.  It uses only normality of the central subgroup and of one edge
subgroup; the harder class-two `1 / sqrt 2` estimate is separate.
-/

namespace NonsoficGroupsExist

universe u v

namespace NormalEdgeCodistance

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Four vectors fixed by the two central edge groups and their two root
groups satisfy the local codistance-`1/2` norm inequality. -/
theorem four_fixed_norm_sq_le
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y Z : Subgroup G)
    (hXnorm : X ≤ Subgroup.normalizer (Z : Set G))
    (hYnorm : Y ≤ Subgroup.normalizer (Z : Set G))
    (hedgeOrtho :
      KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z) ⟂
        KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z))
    {a b c d : E}
    (ha : a ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z))
    (hb : b ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z))
    (hc : c ∈ KazhdanFixedSpace.fixedSubspace rho X)
    (hd : d ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    ‖a + b + c + d‖ ^ 2 ≤
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  let U := KazhdanFixedSpace.fixedSubspace rho Z
  letI : CompleteSpace U :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho Z).completeSpace_coe
  let cL : E := KazhdanFixedSpace.fixedProjection rho Z c
  let dL : E := KazhdanFixedSpace.fixedProjection rho Z d
  let cN : E := c - cL
  let dN : E := d - dL
  have hcLZ : cL ∈ U := by
    exact (KazhdanFixedSpace.fixedProjection rho Z c).property
  have hdLZ : dL ∈ U := by
    exact (KazhdanFixedSpace.fixedProjection rho Z d).property
  have hcLX : cL ∈ KazhdanFixedSpace.fixedSubspace rho X := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    have hcx : rho x c = c :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho X c).mp hc x hx
    calc
      rho x cL = (KazhdanFixedSpace.fixedProjection rho Z (rho x c) : E) :=
        (KazhdanFixedSpace.fixedProjection_equivariant_of_mem_normalizer
          rho Z (hXnorm hx) c).symm
      _ = cL := by rw [hcx]
  have hdLY : dL ∈ KazhdanFixedSpace.fixedSubspace rho Y := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    have hdy : rho y d = d :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y d).mp hd y hy
    calc
      rho y dL = (KazhdanFixedSpace.fixedProjection rho Z (rho y d) : E) :=
        (KazhdanFixedSpace.fixedProjection_equivariant_of_mem_normalizer
          rho Z (hYnorm hy) d).symm
      _ = dL := by rw [hdy]
  have hcLH : cL ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z) := by
    rw [KazhdanFixedSpace.fixedSubspace_sup]
    exact ⟨hcLX, hcLZ⟩
  have hdLK : dL ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z) := by
    rw [KazhdanFixedSpace.fixedSubspace_sup]
    exact ⟨hdLY, hdLZ⟩
  have haZ : a ∈ U := KazhdanFixedSpace.antitone rho le_sup_right ha
  have hbZ : b ∈ U := KazhdanFixedSpace.antitone rho le_sup_right hb
  have hcNOrth : cN ∈ Uᗮ := by
    exact U.sub_starProjection_mem_orthogonal c
  have hdNOrth : dN ∈ Uᗮ := by
    exact U.sub_starProjection_mem_orthogonal d
  have hleft : a + cL ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z) :=
    (KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z)).add_mem ha hcLH
  have hright : b + dL ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z) :=
    (KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z)).add_mem hb hdLK
  have hlr : inner ℝ (a + cL) (b + dL) = 0 :=
    hedgeOrtho.inner_eq hleft hright
  have hheadZ : (a + cL) + (b + dL) ∈ U := U.add_mem (U.add_mem haZ hcLZ)
    (U.add_mem hbZ hdLZ)
  have htailOrth : cN + dN ∈ Uᗮ := Uᗮ.add_mem hcNOrth hdNOrth
  have hheadTail : inner ℝ ((a + cL) + (b + dL)) (cN + dN) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hheadZ htailOrth
  have hhead : ‖(a + cL) + (b + dL)‖ ^ 2 =
      ‖a + cL‖ ^ 2 + ‖b + dL‖ ^ 2 :=
    by simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hlr
  have htotal : a + b + c + d = ((a + cL) + (b + dL)) + (cN + dN) := by
    dsimp [cN, dN]
    abel
  have hpyth : ‖a + b + c + d‖ ^ 2 =
      ‖(a + cL) + (b + dL)‖ ^ 2 + ‖cN + dN‖ ^ 2 := by
    rw [htotal]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hheadTail
  have hleftBound := HilbertEpsilonOrthogonality.norm_add_sq_le_two a cL
  have hrightBound := HilbertEpsilonOrthogonality.norm_add_sq_le_two b dL
  have htailBound := HilbertEpsilonOrthogonality.norm_add_sq_le_two cN dN
  have hcOrth : inner ℝ cL cN = 0 :=
    Submodule.inner_right_of_mem_orthogonal hcLZ hcNOrth
  have hdOrth : inner ℝ dL dN = 0 :=
    Submodule.inner_right_of_mem_orthogonal hdLZ hdNOrth
  have hcSplit : ‖c‖ ^ 2 = ‖cL‖ ^ 2 + ‖cN‖ ^ 2 := by
    calc
      ‖c‖ ^ 2 = ‖cL + cN‖ ^ 2 := by congr 2; dsimp [cN]; abel
      _ = ‖cL‖ ^ 2 + ‖cN‖ ^ 2 :=
        by simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hcOrth
  have hdSplit : ‖d‖ ^ 2 = ‖dL‖ ^ 2 + ‖dN‖ ^ 2 := by
    calc
      ‖d‖ ^ 2 = ‖dL + dN‖ ^ 2 := by congr 2; dsimp [dN]; abel
      _ = ‖dL‖ ^ 2 + ‖dN‖ ^ 2 :=
        by simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hdOrth
  rw [hpyth, hhead]
  nlinarith

/-- The quantitative form of `four_fixed_norm_sq_le`.  If the two root
fixed spaces make angle at most `epsilon`, the part of the two root vectors
orthogonal to the central fixed space produces an explicit deficit from the
borderline constant `2`. -/
theorem four_fixed_norm_sq_le_with_defect
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y Z : Subgroup G) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hXnorm : X ≤ Subgroup.normalizer (Z : Set G))
    (hYnorm : Y ≤ Subgroup.normalizer (Z : Set G))
    (hedgeOrtho :
      KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z) ⟂
        KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z))
    (hXY : HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho X)
      (KazhdanFixedSpace.fixedSubspace rho Y) epsilon)
    {a b c d : E}
    (ha : a ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z))
    (hb : b ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z))
    (hc : c ∈ KazhdanFixedSpace.fixedSubspace rho X)
    (hd : d ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    let cN := c - KazhdanFixedSpace.fixedProjection rho Z c
    let dN := d - KazhdanFixedSpace.fixedProjection rho Z d
    ‖a + b + c + d‖ ^ 2 ≤
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) -
        (1 - epsilon) * (‖cN‖ ^ 2 + ‖dN‖ ^ 2) := by
  let U := KazhdanFixedSpace.fixedSubspace rho Z
  letI : CompleteSpace U :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho Z).completeSpace_coe
  let cL : E := KazhdanFixedSpace.fixedProjection rho Z c
  let dL : E := KazhdanFixedSpace.fixedProjection rho Z d
  let cN : E := c - cL
  let dN : E := d - dL
  have hcLZ : cL ∈ U :=
    (KazhdanFixedSpace.fixedProjection rho Z c).property
  have hdLZ : dL ∈ U :=
    (KazhdanFixedSpace.fixedProjection rho Z d).property
  have hcLX : cL ∈ KazhdanFixedSpace.fixedSubspace rho X := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    have hcx : rho x c = c :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho X c).mp hc x hx
    calc
      rho x cL = (KazhdanFixedSpace.fixedProjection rho Z (rho x c) : E) :=
        (KazhdanFixedSpace.fixedProjection_equivariant_of_mem_normalizer
          rho Z (hXnorm hx) c).symm
      _ = cL := by rw [hcx]
  have hdLY : dL ∈ KazhdanFixedSpace.fixedSubspace rho Y := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    have hdy : rho y d = d :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y d).mp hd y hy
    calc
      rho y dL = (KazhdanFixedSpace.fixedProjection rho Z (rho y d) : E) :=
        (KazhdanFixedSpace.fixedProjection_equivariant_of_mem_normalizer
          rho Z (hYnorm hy) d).symm
      _ = dL := by rw [hdy]
  have hcLH : cL ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z) := by
    rw [KazhdanFixedSpace.fixedSubspace_sup]
    exact ⟨hcLX, hcLZ⟩
  have hdLK : dL ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z) := by
    rw [KazhdanFixedSpace.fixedSubspace_sup]
    exact ⟨hdLY, hdLZ⟩
  have haZ : a ∈ U := KazhdanFixedSpace.antitone rho le_sup_right ha
  have hbZ : b ∈ U := KazhdanFixedSpace.antitone rho le_sup_right hb
  have hcNOrth : cN ∈ Uᗮ := U.sub_starProjection_mem_orthogonal c
  have hdNOrth : dN ∈ Uᗮ := U.sub_starProjection_mem_orthogonal d
  have hcNX : cN ∈ KazhdanFixedSpace.fixedSubspace rho X :=
    (KazhdanFixedSpace.fixedSubspace rho X).sub_mem hc hcLX
  have hdNY : dN ∈ KazhdanFixedSpace.fixedSubspace rho Y :=
    (KazhdanFixedSpace.fixedSubspace rho Y).sub_mem hd hdLY
  have hleft : a + cL ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z) :=
    (KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z)).add_mem ha hcLH
  have hright : b + dL ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z) :=
    (KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z)).add_mem hb hdLK
  have hlr : inner ℝ (a + cL) (b + dL) = 0 :=
    hedgeOrtho.inner_eq hleft hright
  have hheadZ : (a + cL) + (b + dL) ∈ U :=
    U.add_mem (U.add_mem haZ hcLZ) (U.add_mem hbZ hdLZ)
  have htailOrth : cN + dN ∈ Uᗮ := Uᗮ.add_mem hcNOrth hdNOrth
  have hheadTail : inner ℝ ((a + cL) + (b + dL)) (cN + dN) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hheadZ htailOrth
  have hhead : ‖(a + cL) + (b + dL)‖ ^ 2 =
      ‖a + cL‖ ^ 2 + ‖b + dL‖ ^ 2 := by
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hlr
  have htotal : a + b + c + d = ((a + cL) + (b + dL)) + (cN + dN) := by
    dsimp [cN, dN]
    abel
  have hpyth : ‖a + b + c + d‖ ^ 2 =
      ‖(a + cL) + (b + dL)‖ ^ 2 + ‖cN + dN‖ ^ 2 := by
    rw [htotal]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hheadTail
  have hleftBound := HilbertEpsilonOrthogonality.norm_add_sq_le_two a cL
  have hrightBound := HilbertEpsilonOrthogonality.norm_add_sq_le_two b dL
  have htailBound := HilbertEpsilonOrthogonality.norm_add_sq_le
    hepsilon hXY hcNX hdNY
  have hcOrth : inner ℝ cL cN = 0 :=
    Submodule.inner_right_of_mem_orthogonal hcLZ hcNOrth
  have hdOrth : inner ℝ dL dN = 0 :=
    Submodule.inner_right_of_mem_orthogonal hdLZ hdNOrth
  have hcSplit : ‖c‖ ^ 2 = ‖cL‖ ^ 2 + ‖cN‖ ^ 2 := by
    calc
      ‖c‖ ^ 2 = ‖cL + cN‖ ^ 2 := by congr 2; dsimp [cN]; abel
      _ = ‖cL‖ ^ 2 + ‖cN‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hcOrth
  have hdSplit : ‖d‖ ^ 2 = ‖dL‖ ^ 2 + ‖dN‖ ^ 2 := by
    calc
      ‖d‖ ^ 2 = ‖dL + dN‖ ^ 2 := by congr 2; dsimp [dN]; abel
      _ = ‖dL‖ ^ 2 + ‖dN‖ ^ 2 := by
        simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hdOrth
  change ‖a + b + c + d‖ ^ 2 ≤
    2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) -
      (1 - epsilon) * (‖cN‖ ^ 2 + ‖dN‖ ^ 2)
  rw [hpyth, hhead]
  nlinarith

omit [CompleteSpace E] in
/-- On the component with no central fixed vectors, the two edge-fixed
vectors vanish and the four-vector estimate reduces exactly to quantitative
orthogonality of the two root fixed spaces. -/
theorem four_fixed_norm_sq_le_of_center_fixed_eq_bot
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y Z : Subgroup G) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hcenter : KazhdanFixedSpace.fixedSubspace rho Z = ⊥)
    (hXY : HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho X)
      (KazhdanFixedSpace.fixedSubspace rho Y) epsilon)
    {a b c d : E}
    (ha : a ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z))
    (hb : b ∈ KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z))
    (hc : c ∈ KazhdanFixedSpace.fixedSubspace rho X)
    (hd : d ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    ‖a + b + c + d‖ ^ 2 ≤
      (1 + epsilon) *
        (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have haZ : a ∈ KazhdanFixedSpace.fixedSubspace rho Z :=
    KazhdanFixedSpace.antitone rho le_sup_right ha
  have hbZ : b ∈ KazhdanFixedSpace.fixedSubspace rho Z :=
    KazhdanFixedSpace.antitone rho le_sup_right hb
  have ha0 : a = 0 := by
    rw [hcenter] at haZ
    simpa using haZ
  have hb0 : b = 0 := by
    rw [hcenter] at hbZ
    simpa using hbZ
  subst a
  subst b
  simpa using HilbertEpsilonOrthogonality.norm_add_sq_le
    hepsilon hXY hc hd

end NormalEdgeCodistance
end NonsoficGroupsExist
