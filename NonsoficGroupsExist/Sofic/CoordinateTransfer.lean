import NonsoficGroupsExist.Sofic.Sofic
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Coordinate reverse transfer: a lamp chart is a coordinate chart

An external referee audit (August 2026) observed that the action-level route to
hyperlinearity of a generalized wreath product cannot help a candidate whose
coordinate action is not already sofic, because the lamp data *contains* the
coordinate data.  This file formalizes that observation.

The proof in the audit is written against two papers' definitions, but its
content does not depend on either: it is the remark that if one encodes a
coordinate `x` as the lamp `δ_x(k₀)` for a fixed `k₀ ≠ 1`, then the encoding is
injective and equivariant, so charts for the lamp action restrict along it to
charts for the coordinate action, and the covariance identity transports
verbatim.  Both facts are isolated here as the hypotheses they are.

* `OrbitChartData` is the shape both definitions share: a finite site with a
  permutation model, a large good set, and injective charts on a finite window
  satisfying the covariance identity.
* `OrbitChartData.comap` is the transfer: an injective equivariant map pulls
  chart data back.  Nothing about the target of the charts is used.
* `lampEmbedding_injective` and `lampEmbedding_equivariant` supply the two
  hypotheses for the coordinate action on `⊕_X A`, so
  `OrbitChartData.comapLamp` is the audit's statement in the concrete case.

The reading is the audit's: if the coordinate action is not sofic, no chart
system for the lamp action exists either, whatever class the charts take values
in.  This closes a route to hyperlinearity; it does not bear on whether the
wreath product is hyperlinear by other means, and nothing here says it is.
-/

namespace NonsoficGroupsExist

/-! ## Chart data -/

/-- The data an orbit approximation carries, in the shape shared by the
set-action and automorphism-action definitions: a finite site, a permutation
model of the group, a large good subset, and charts on a finite window that are
injective on it and satisfy the covariance identity. -/
structure OrbitChartData (H : Type*) [Group H] (X : Type*) [MulAction H X]
    (F : Finset H) (E : Finset X) (ε : ℝ) where
  site : Type
  siteFintype : Fintype site
  siteDecidableEq : DecidableEq site
  perm : H → Equiv.Perm site
  good : Finset site
  good_large : (1 - ε) * Fintype.card site < good.card
  target : Type
  chart : site → X → target
  chart_injOn : ∀ s ∈ good, ∀ x ∈ E, ∀ y ∈ E, chart s x = chart s y → x = y
  covariance : ∀ g ∈ F, ∀ s ∈ good, perm g s ∈ good → ∀ x ∈ E,
    g⁻¹ • x ∈ E → chart (perm g s) x = chart s (g⁻¹ • x)

/-- A closed inhabitant, so `OrbitChartData` is not a certificate nothing
satisfies: the one-point action with its identity chart. -/
instance punitMulAction (H : Type) [Group H] : MulAction H PUnit where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- A closed inhabitant, so `OrbitChartData` is not a certificate nothing
satisfies: the one-point action with its identity chart. -/
def trivialOrbitChartData (H : Type) [Group H] (F : Finset H)
    (E : Finset PUnit) : OrbitChartData H PUnit F E 1 where
  site := PUnit
  siteFintype := inferInstance
  siteDecidableEq := inferInstance
  perm := fun _ ↦ 1
  good := Finset.univ
  good_large := by norm_num
  target := PUnit
  chart := fun _ x ↦ x
  chart_injOn := fun _ _ _ _ _ _ h ↦ h
  covariance := fun _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _

namespace OrbitChartData

/-- **The transfer.**  An injective equivariant map pulls chart data back along
itself.  Nothing about the target of the charts is used, so this holds for
charts valued in any class whatever. -/
def comap {H : Type*} [Group H] {X D : Type*} [MulAction H X] [MulAction H D]
    {F : Finset H} {E : Finset X} {ε : ℝ}
    (emb : X → D) (hinj : Function.Injective emb)
    (hequiv : ∀ (g : H) (x : X), emb (g • x) = g • emb x)
    [DecidableEq D]
    (C : OrbitChartData H D F (E.image emb) ε) :
    OrbitChartData H X F E ε where
  site := C.site
  siteFintype := C.siteFintype
  siteDecidableEq := C.siteDecidableEq
  perm := C.perm
  good := C.good
  good_large := C.good_large
  target := C.target
  chart := fun s x ↦ C.chart s (emb x)
  chart_injOn := by
    intro s hs x hx y hy hxy
    exact hinj (C.chart_injOn s hs (emb x) (Finset.mem_image_of_mem emb hx)
      (emb y) (Finset.mem_image_of_mem emb hy) hxy)
  covariance := by
    intro g hg s hs hgs x hx hgx
    have h := C.covariance g hg s hs hgs (emb x)
      (Finset.mem_image_of_mem emb hx)
      (by rw [← hequiv]; exact Finset.mem_image_of_mem emb hgx)
    rw [h, hequiv]

end OrbitChartData

/-! ## The lamp encoding -/

section Lamps

variable {H : Type*} [Group H] {X : Type*} [MulAction H X] [DecidableEq X]
variable {A : Type*} [AddCommGroup A]

/-- The lamp group `⊕_X A`, with the coordinate action of `H`. -/
abbrev Lamps (X A : Type*) [AddCommGroup A] := X →₀ A

/-- The coordinate action: `H` permutes the sites. -/
noncomputable instance lampAction : MulAction H (Lamps X A) where
  smul g f := Finsupp.mapDomain (fun x : X ↦ g • x) f
  one_smul f := by
    show Finsupp.mapDomain (fun x : X ↦ (1 : H) • x) f = f
    simp only [one_smul]
    exact Finsupp.mapDomain_id
  mul_smul g h f := by
    show Finsupp.mapDomain (fun x : X ↦ (g * h) • x) f
      = Finsupp.mapDomain (fun x : X ↦ g • x)
        (Finsupp.mapDomain (fun x : X ↦ h • x) f)
    rw [← Finsupp.mapDomain_comp]
    congr 1
    funext x
    exact mul_smul g h x

/-- The encoding of a coordinate as a single lit lamp. -/
noncomputable def lampEmbedding (a : A) (x : X) : Lamps X A :=
  Finsupp.single x a

omit [DecidableEq X] in
/-- **The encoding is injective**, for any nonzero lamp value. -/
theorem lampEmbedding_injective {a : A} (ha : a ≠ 0) :
    Function.Injective (lampEmbedding (X := X) a) :=
  fun _ _ h ↦ Finsupp.single_left_injective ha h

omit [DecidableEq X] in
/-- **The encoding is equivariant.** -/
theorem lampEmbedding_equivariant (a : A) (g : H) (x : X) :
    lampEmbedding a (g • x) = g • lampEmbedding (X := X) a x := by
  show Finsupp.single (g • x) a
    = Finsupp.mapDomain (fun y : X ↦ g • y) (Finsupp.single x a)
  rw [Finsupp.mapDomain_single]

/-- **Coordinate reverse transfer.**  Chart data for the lamp action restricts
to chart data for the coordinate action.  So if the coordinate action admits no
chart system, neither does the lamp action -- whatever class the lamp charts
take their values in. -/
noncomputable def OrbitChartData.comapLamp {F : Finset H} {E : Finset X}
    {ε : ℝ} {a : A} (ha : a ≠ 0) [DecidableEq (Lamps X A)]
    (C : OrbitChartData H (Lamps X A) F (E.image (lampEmbedding a)) ε) :
    OrbitChartData H X F E ε :=
  OrbitChartData.comap (lampEmbedding a) (lampEmbedding_injective ha)
    (fun g x ↦ lampEmbedding_equivariant a g x) C

end Lamps

end NonsoficGroupsExist
