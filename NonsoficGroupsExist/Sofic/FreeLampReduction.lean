import NonsoficGroupsExist.Sofic.SoficUltraproduct
import NonsoficGroupsExist.Sofic.SoficSequential
import Mathlib.GroupTheory.PushoutI

/-!
# The free-lamp reduction: one centralizing element against one cited theorem

Kun--Thom (arXiv:2608.06222v1, Theorem 4.1) prove: *let `Γ` be an infranormal
subgroup of `G`, and suppose that both `Γ` and `G` have Kazhdan's property (T);
if `σ : G → 𝒮_𝒰` is a sofic representation, then `C_{𝒮_𝒰}(σ(Γ))` is
normalized by `σ(G)`.*  The theorem quantifies over arbitrary sofic
representations of `G`, and that generality has a striking consequence,
observed in the August 2026 discussions: the *commuting lamps* of their wreath
products are unnecessary.  A single new element centralizing `Γ` — with its
conjugates free rather than commuting — already contradicts
centralizer normalization.  Concretely, for any nontrivial group `K`, the
amalgam `H_K = G *_Γ (Γ × K)` is nonsofic: a sofic embedding of `H_K`
restricts to a sofic representation of `G`; the image of `k ∈ K` centralizes
the image of `Γ`; normalization drags `t k t⁻¹` into the centralizer for every
`t`; and the commutator `[t k t⁻¹, γ]` — nontrivial in `H_K` by the normal
form of the amalgam whenever `t⁻¹ γ t ∉ Γ` — dies, contradicting injectivity.

This file formalizes **everything in that argument except the cited
theorem**.  `CentralizerNormalization G Γ` is the named transcription of
Kun--Thom's Theorem 4.1 for the pair, stated against this development's
metric ultraproduct `UniversalSofic`; it is a hypothesis here, not a theorem,
and nothing in this file proves or claims it.  What is proved
unconditionally:

* the free-lamp amalgam `FreeLamp G Γ K`, built on Mathlib's `PushoutI`, with
  its two canonical embeddings `inAmbient` and `inLamp`;
* the centralizing relation: `inLamp k` commutes with `inAmbient g` for every
  `g ∈ Γ` (`inLamp_commute_inAmbient`);
* the normal-form nontriviality: the witness commutator `lampWitness t γ k`
  is nontrivial whenever `γ ∈ Γ`, `t⁻¹ γ t ∉ Γ`, and `k ≠ 1`
  (`lampWitness_ne_one`), through the reduced-word theorem for pushouts;
* metric faithfulness of the embedding a sofic approximation induces into the
  universal sofic group (`SoficApproximation.toUniversal`), the normalization
  Kun--Thom's sofic representations carry, preserved under restriction;
* **the reduction** (`freeLamp_not_isSofic`): if the pair `(G, Γ)` satisfies
  `CentralizerNormalization` — as Kun--Thom's Theorem 4.1 asserts whenever
  `Γ` is infranormal and both groups are Kazhdan — and there exist `γ ∈ Γ`,
  `t` with `t⁻¹ γ t ∉ Γ`, then `FreeLamp G Γ K` is not sofic for any
  nontrivial countable `K`.

The infranormality and property-(T) hypotheses of the cited theorem do not
appear in the reduction: they are what make the named hypothesis *true* for
Kun--Thom's explicit pairs, not what the reduction consumes.  For `K = ℤ`
the amalgam is free-by-`G`, and its hyperlinearity is equivalent to the
Connes-embeddability of one amalgamated free product — the sharpest currently
known route to a negative answer to Question 3.4.
-/

namespace NonsoficGroupsExist

open Monoid

/-! ## The free-lamp amalgam -/

variable (G : Type) [Group G] (Γ : Subgroup G) (K : Type) [Group K]

/-- The two factors of the free-lamp amalgam: the ambient group and the
lamp-augmented copy `Γ × K` of the amalgamation subgroup. -/
abbrev LampFactor : Bool → Type := fun b => bif b then G else ↥Γ × K

instance lampFactorGroup : ∀ b, Group (LampFactor G Γ K b)
  | true => inferInstanceAs (Group G)
  | false => inferInstanceAs (Group (↥Γ × K))

/-- The amalgamation maps: `Γ` into `G` by inclusion, and into `Γ × K` as the
first coordinate. -/
def lampMap : ∀ b, ↥Γ →* LampFactor G Γ K b
  | true => Γ.subtype
  | false => MonoidHom.inl ↥Γ K

theorem lampMap_injective : ∀ b, Function.Injective (lampMap G Γ K b)
  | true => Γ.subtype_injective
  | false => fun _ _ hxy => congrArg Prod.fst hxy

/-- The free-lamp amalgam `G *_Γ (Γ × K)`.  Reducible, so that every use
elaborates against the pushout's own group structure. -/
abbrev FreeLamp : Type := PushoutI (lampMap G Γ K)

/-- The ambient group inside the amalgam. -/
def inAmbient : G →* FreeLamp G Γ K :=
  PushoutI.of (φ := lampMap G Γ K) true

/-- The lamp group inside the amalgam. -/
def inLamp : K →* FreeLamp G Γ K :=
  (PushoutI.of (φ := lampMap G Γ K) false).comp (MonoidHom.inr ↥Γ K)

@[simp] theorem inAmbient_apply (g : G) :
    inAmbient G Γ K g = PushoutI.of (φ := lampMap G Γ K) true g := rfl

@[simp] theorem inLamp_apply (k : K) :
    inLamp G Γ K k
      = PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k) := rfl

theorem inAmbient_injective : Function.Injective (inAmbient G Γ K) :=
  PushoutI.of_injective (lampMap_injective G Γ K) true

/-- **The lamp centralizes the amalgamation subgroup.**  The relation that
replaces all of the commuting-lamp structure of a wreath product. -/
theorem inLamp_commute_inAmbient (k : K) {g : G} (hg : g ∈ Γ) :
    Commute (inLamp G Γ K k) (inAmbient G Γ K g) := by
  have hbase : inAmbient G Γ K g
      = PushoutI.of (φ := lampMap G Γ K) false ((⟨g, hg⟩ : ↥Γ), (1 : K)) := by
    have h1 : inAmbient G Γ K g
        = PushoutI.of (φ := lampMap G Γ K) true
            (lampMap G Γ K true ⟨g, hg⟩) := rfl
    rw [h1, PushoutI.of_apply_eq_base,
      ← PushoutI.of_apply_eq_base (φ := lampMap G Γ K) false]
    rfl
  rw [inLamp_apply, hbase]
  have hcomm : Commute (((1 : ↥Γ), k) : ↥Γ × K) ((⟨g, hg⟩ : ↥Γ), (1 : K)) := by
    show ((1 : ↥Γ), k) * (⟨g, hg⟩, (1 : K))
      = ((⟨g, hg⟩ : ↥Γ), (1 : K)) * (1, k)
    simp
  exact hcomm.map (PushoutI.of (φ := lampMap G Γ K) false)

/-! ## The witness commutator and its nontriviality -/

/-- The witness: the commutator of the transported lamp `t k t⁻¹` against
`γ`.  Kun--Thom normalization forces its image to die in every sofic
representation; the amalgam normal form keeps it alive in the group. -/
def lampWitness (t γ : G) (k : K) : FreeLamp G Γ K :=
  (inAmbient G Γ K t * inLamp G Γ K k * (inAmbient G Γ K t)⁻¹)
    * inAmbient G Γ K γ
    * (inAmbient G Γ K t * inLamp G Γ K k * (inAmbient G Γ K t)⁻¹)⁻¹
    * (inAmbient G Γ K γ)⁻¹

/-- **The core nontriviality.**  If `s ∉ Γ` and `k ≠ 1`, the commutator of
`inLamp k` and `inAmbient s` is nontrivial: the four-letter word alternates
between the two factors with every letter outside the amalgamation image, so
the reduced-word theorem applies. -/
theorem lampCore_ne_one {s : G} (hs : s ∉ Γ) {k : K} (hk : k ≠ 1) :
    inLamp G Γ K k * inAmbient G Γ K s * (inLamp G Γ K k)⁻¹
      * (inAmbient G Γ K s)⁻¹ ≠ 1 := by
  classical
  intro hcon
  have hs1 : s ≠ 1 := fun h => by
    rw [h] at hs
    exact hs (one_mem Γ)
  set w : CoprodI.Word (LampFactor G Γ K) := {
    toList := [⟨false, ((1 : ↥Γ), k)⟩, ⟨true, s⟩,
      ⟨false, ((1 : ↥Γ), k⁻¹)⟩, ⟨true, s⁻¹⟩]
    ne_one := by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · intro h
        exact hk (congrArg Prod.snd h)
      · exact hs1
      · intro h
        exact hk (inv_eq_one.mp (congrArg Prod.snd h))
      · exact inv_ne_one.mpr hs1
    chain_ne := .cons_cons (by simp) (.cons_cons (by simp)
      (.cons_cons (by simp) (.singleton _))) } with hw
  have hred : PushoutI.Reduced (lampMap G Γ K) w := by
    intro l hl
    simp only [hw, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · rintro ⟨x, hx⟩
      exact hk ((congrArg Prod.snd hx : (1 : K) = k)).symm
    · rintro ⟨x, hx⟩
      apply hs
      have hx' : (x : G) = s := hx
      rw [← hx']
      exact x.2
    · rintro ⟨x, hx⟩
      exact hk (inv_eq_one.mp ((congrArg Prod.snd hx : (1 : K) = k⁻¹)).symm)
    · rintro ⟨x, hx⟩
      apply hs
      have hx' : (x : G) = s⁻¹ := hx
      have hmem : s⁻¹ ∈ Γ := by
        rw [← hx']
        exact x.2
      have h2 := inv_mem hmem
      rwa [inv_inv] at h2
  have e3 : PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k⁻¹)
      = (inLamp G Γ K k)⁻¹ := by
    rw [inLamp_apply]
    calc PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k⁻¹)
        = PushoutI.of (φ := lampMap G Γ K) false (((1 : ↥Γ), k)⁻¹) :=
          congrArg _ (by
            show (((1 : ↥Γ), k⁻¹) : ↥Γ × K) = (((1 : ↥Γ), k) : ↥Γ × K)⁻¹
            rw [Prod.inv_mk, inv_one])
      _ = (PushoutI.of (φ := lampMap G Γ K) false ((1 : ↥Γ), k))⁻¹ :=
          map_inv _ _
  have e4 : PushoutI.of (φ := lampMap G Γ K) true s⁻¹
      = (inAmbient G Γ K s)⁻¹ := map_inv _ _
  have hprod : PushoutI.ofCoprodI w.prod
      = inLamp G Γ K k * inAmbient G Γ K s * (inLamp G Γ K k)⁻¹
        * (inAmbient G Γ K s)⁻¹ := by
    simp only [hw, CoprodI.Word.prod, List.map_cons, List.prod_cons,
      List.map_nil, List.prod_nil, mul_one, map_mul, PushoutI.ofCoprodI_of]
    rw [e3, e4, ← inLamp_apply, ← inAmbient_apply]
    simp only [mul_assoc]
  have hmem : PushoutI.ofCoprodI w.prod
      ∈ (PushoutI.base (lampMap G Γ K)).range := by
    rw [hprod, hcon]
    exact ⟨1, map_one _⟩
  have hempty := hred.eq_empty_of_mem_range (lampMap_injective G Γ K) hmem
  have hlist := congrArg CoprodI.Word.toList hempty
  simp [hw, CoprodI.Word.empty] at hlist

/-- **The witness is nontrivial** whenever `γ` escapes the compressed copy —
`t⁻¹ γ t ∉ Γ` — and the lamp is nontrivial.  Membership of `γ` in `Γ` is not
needed here; it is what makes the centralizer argument bite. -/
theorem lampWitness_ne_one {t γ : G} (hs : t⁻¹ * γ * t ∉ Γ)
    {k : K} (hk : k ≠ 1) : lampWitness G Γ K t γ k ≠ 1 := by
  intro hcon
  refine lampCore_ne_one G Γ K hs hk ?_
  have hconj : lampWitness G Γ K t γ k
      = inAmbient G Γ K t
        * (inLamp G Γ K k * inAmbient G Γ K (t⁻¹ * γ * t)
            * (inLamp G Γ K k)⁻¹ * (inAmbient G Γ K (t⁻¹ * γ * t))⁻¹)
        * (inAmbient G Γ K t)⁻¹ := by
    simp only [lampWitness, map_mul, map_inv]
    group
  rw [hconj] at hcon
  calc inLamp G Γ K k * inAmbient G Γ K (t⁻¹ * γ * t)
        * (inLamp G Γ K k)⁻¹ * (inAmbient G Γ K (t⁻¹ * γ * t))⁻¹
      = (inAmbient G Γ K t)⁻¹
          * (inAmbient G Γ K t
            * (inLamp G Γ K k * inAmbient G Γ K (t⁻¹ * γ * t)
                * (inLamp G Γ K k)⁻¹ * (inAmbient G Γ K (t⁻¹ * γ * t))⁻¹)
            * (inAmbient G Γ K t)⁻¹)
          * inAmbient G Γ K t := by group
    _ = 1 := by rw [hcon]; group

/-! ## Countability -/

instance lampFactorCountable [Countable G] [Countable K] :
    ∀ b, Countable (LampFactor G Γ K b)
  | true => inferInstanceAs (Countable G)
  | false => inferInstanceAs (Countable (↥Γ × K))

instance freeLampCountable [Countable G] [Countable K] :
    Countable (FreeLamp G Γ K) := by
  haveI h0 : Countable (FreeMonoid (Σ b, LampFactor G Γ K b)) :=
    inferInstanceAs (Countable (List (Σ b, LampFactor G Γ K b)))
  haveI h1 : Countable (CoprodI (LampFactor G Γ K)) :=
    Con.mk'_surjective.countable
  haveI h2 : Countable (FreeMonoid (CoprodI (LampFactor G Γ K) ⊕ ↥Γ)) :=
    inferInstanceAs (Countable (List (CoprodI (LampFactor G Γ K) ⊕ ↥Γ)))
  haveI h3 : Countable (Coprod (CoprodI (LampFactor G Γ K)) ↥Γ) :=
    Con.mk'_surjective.countable
  exact Con.mk'_surjective.countable

/-! ## Metric faithfulness: the sofic-representation normalization -/

variable {ι : Type*}

/-- A homomorphism into the universal sofic group is *metrically faithful*
when every nontrivial element keeps Hamming length at least `1 - ε`
eventually, on every representative sequence — the normalization carried by
the sofic representations Kun--Thom quantify over. -/
def IsMetricallyFaithful (𝒰 : Ultrafilter ι) (X : ι → FiniteModel)
    {H : Type*} [Group H] (σ : H →* UniversalSofic 𝒰 X) : Prop :=
  ∀ g : H, g ≠ 1 → ∀ τ : ∀ i, Equiv.Perm (X i),
    (QuotientGroup.mk τ : UniversalSofic 𝒰 X) = σ g →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (𝒰 : Filter ι), 1 - ε ≤ hammingLength (X i) (τ i)

/-- Metric faithfulness forces injectivity: the identity sequence represents
the image of a kernel element and has length zero. -/
theorem IsMetricallyFaithful.injective {𝒰 : Ultrafilter ι}
    {X : ι → FiniteModel} {H : Type*} [Group H]
    {σ : H →* UniversalSofic 𝒰 X} (h : IsMetricallyFaithful 𝒰 X σ) :
    Function.Injective σ := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  have hev := h g hne 1 (by rw [hg]; rfl) (1 / 2) (by norm_num)
  obtain ⟨i, hi⟩ := hev.exists
  have hzero : hammingLength (X i) ((1 : ∀ j, Equiv.Perm (X j)) i) = 0 := by
    show hammingLength (X i) 1 = 0
    exact hammingLength_one (X i)
  rw [hzero] at hi
  linarith

/-- Metric faithfulness restricts along injective homomorphisms: a sofic
representation of a group is a sofic representation of every subgroup. -/
theorem IsMetricallyFaithful.comp {𝒰 : Ultrafilter ι} {X : ι → FiniteModel}
    {H H' : Type*} [Group H] [Group H'] {σ : H →* UniversalSofic 𝒰 X}
    (h : IsMetricallyFaithful 𝒰 X σ) {j : H' →* H}
    (hj : Function.Injective j) : IsMetricallyFaithful 𝒰 X (σ.comp j) := by
  intro g hg τ hτ ε hε
  refine h (j g) (fun hc => hg (hj ?_)) τ hτ ε hε
  rw [hc, map_one]

/-- A closed witness, so `IsMetricallyFaithful` is not a certificate nothing
satisfies: the trivial homomorphism of the trivial group, vacuously. -/
theorem isMetricallyFaithful_trivial (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel) :
    IsMetricallyFaithful 𝒰 X (1 : PUnit →* UniversalSofic 𝒰 X) := by
  intro g hg
  exact absurd (Subsingleton.elim g 1) hg

/-- The canonical homomorphism into the universal sofic group over the models
of a sofic approximation, along any nonprincipal ultrafilter. -/
noncomputable def SoficApproximation.toUniversal {H : Type*} [Group H]
    (S : SoficApproximation H) (𝒰 : Ultrafilter ℕ)
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    H →* UniversalSofic 𝒰 S.model :=
  MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ S.map n g)) (by
    intro g h
    rw [← QuotientGroup.mk_mul]
    refine (QuotientGroup.eq.mpr ?_).symm
    intro ε hε
    obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative g h ε hε
    refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
    have hval : hammingLength (S.model n)
        ((((fun m ↦ S.map m g) * fun m ↦ S.map m h)⁻¹
          * fun m ↦ S.map m (g * h)) n)
        = hammingDistance (S.model n) (S.map n (g * h))
            (S.map n g * S.map n h) :=
      hammingLength_inv_mul (S.model n) (S.map n (g * h))
        (S.map n g * S.map n h)
    rw [hval]
    exact hN n hn)

@[simp] theorem SoficApproximation.toUniversal_apply {H : Type*} [Group H]
    (S : SoficApproximation H) (𝒰 : Ultrafilter ℕ)
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) (g : H) :
    S.toUniversal 𝒰 hcof g
      = (QuotientGroup.mk (fun n ↦ S.map n g) : UniversalSofic 𝒰 S.model) :=
  rfl

/-- **The induced embedding is metrically faithful**: asymptotic faithfulness
of the approximation survives any null perturbation of the representative. -/
theorem SoficApproximation.toUniversal_metricallyFaithful {H : Type*}
    [Group H] (S : SoficApproximation H) (𝒰 : Ultrafilter ℕ)
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    IsMetricallyFaithful 𝒰 S.model (S.toUniversal 𝒰 hcof) := by
  intro g hg τ hτ ε hε
  have hν : τ⁻¹ * (fun n ↦ S.map n g) ∈ nullSubgroup 𝒰 S.model :=
    QuotientGroup.eq.mp hτ
  obtain ⟨N, hN⟩ := S.asymptoticallyFaithful g hg (ε / 2) (by linarith)
  have hfar := eventually_of_atTop hcof N hN
  filter_upwards [hν (ε / 2) (by linarith), hfar] with n hn hf
  have hsplit : S.map n g = τ n * ((τ⁻¹ * fun m ↦ S.map m g) n) := by
    show S.map n g = τ n * ((τ n)⁻¹ * S.map n g)
    group
  have hlen : hammingLength (S.model n) (S.map n g)
      ≤ hammingLength (S.model n) (τ n)
        + hammingLength (S.model n) ((τ⁻¹ * fun m ↦ S.map m g) n) := by
    rw [hsplit]
    exact hammingLength_mul_le (S.model n) _ _
  have hlow : 1 - ε / 2 < hammingLength (S.model n) (S.map n g) := by
    rw [hammingLength]
    exact hf
  linarith

/-! ## The named hypothesis: Kun--Thom Theorem 4.1 for a pair -/

/-- **The Kun--Thom centralizer normalization for the pair `Γ ≤ G`.**  The
verbatim shape of arXiv:2608.06222v1, Theorem 4.1, against this development's
universal sofic group: for every metrically faithful homomorphism
`σ : G →* UniversalSofic 𝒰 X` along a nonprincipal ultrafilter on `ℕ`,
every element commuting with `σ(Γ)` has all of its `σ(G)`-conjugates
commuting with `σ(Γ)`.  Kun--Thom prove this whenever `Γ` is infranormal in
`G` and both groups have property (T); here it is a **named hypothesis**,
cited and not proved, and `freeLamp_not_isSofic` consumes it. -/
def CentralizerNormalization (G : Type) [Group G] (Γ : Subgroup G) : Prop :=
  ∀ (𝒰 : Ultrafilter ℕ) (X : ℕ → FiniteModel),
    (𝒰 : Filter ℕ) ≤ Filter.cofinite →
    ∀ σ : G →* UniversalSofic 𝒰 X, IsMetricallyFaithful 𝒰 X σ →
      ∀ q : UniversalSofic 𝒰 X, (∀ g ∈ Γ, Commute q (σ g)) →
        ∀ h : G, ∀ g ∈ Γ, Commute (σ h * q * (σ h)⁻¹) (σ g)

/-- Positive control: the normalization holds unconditionally at `Γ = ⊤`,
where the centralizer is central and conjugation fixes it elementwise. -/
theorem centralizerNormalization_top (G : Type) [Group G] :
    CentralizerNormalization G ⊤ := by
  intro 𝒰 X hcof σ hσ q hq h g hg
  have hfix : σ h * q * (σ h)⁻¹ = q := by
    rw [(hq h trivial).symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  rw [hfix]
  exact hq g hg

/-! ## The reduction -/

/-- **The free-lamp reduction.**  If the pair `(G, Γ)` satisfies the
Kun--Thom centralizer normalization, and some `γ ∈ Γ` has `t⁻¹ γ t ∉ Γ`,
then the free-lamp amalgam `G *_Γ (Γ × K)` is not sofic, for every
nontrivial countable `K`.  Everything here is unconditional except the named
hypothesis: the restriction of a sofic embedding is metrically faithful, the
lamp centralizes `σ(Γ)`, normalization kills the witness commutator, and the
amalgam normal form keeps it alive. -/
theorem freeLamp_not_isSofic [Countable G] [Countable K]
    (hcn : CentralizerNormalization G Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hs : t⁻¹ * γ * t ∉ Γ) {k : K} (hk : k ≠ 1) :
    ¬ IsSofic (FreeLamp G Γ K) := by
  intro hsofic
  obtain ⟨S⟩ := soficApproximation_of_isSofic hsofic
  have hcof : ((Ultrafilter.of Filter.cofinite : Ultrafilter ℕ) : Filter ℕ)
      ≤ Filter.cofinite := Ultrafilter.of_le _
  set ρ := S.toUniversal (Ultrafilter.of Filter.cofinite) hcof with hρ
  have hfaithful := S.toUniversal_metricallyFaithful
    (Ultrafilter.of Filter.cofinite) hcof
  have hσ := hfaithful.comp (inAmbient_injective G Γ K)
  have hq : ∀ g ∈ Γ, Commute (ρ (inLamp G Γ K k))
      ((ρ.comp (inAmbient G Γ K)) g) := by
    intro g hg
    exact (inLamp_commute_inAmbient G Γ K k hg).map ρ
  have hc := hcn (Ultrafilter.of Filter.cofinite) S.model hcof
    (ρ.comp (inAmbient G Γ K)) hσ (ρ (inLamp G Γ K k)) hq t γ hγ
  have key : ∀ a b : UniversalSofic (Ultrafilter.of Filter.cofinite) S.model,
      a * b = b * a → a * b * a⁻¹ * b⁻¹ = 1 := by
    intro a b hab
    rw [hab]
    group
  have hone : ρ (lampWitness G Γ K t γ k) = 1 := by
    have hcomm : ρ (inAmbient G Γ K t) * ρ (inLamp G Γ K k)
          * (ρ (inAmbient G Γ K t))⁻¹ * ρ (inAmbient G Γ K γ)
        = ρ (inAmbient G Γ K γ)
          * (ρ (inAmbient G Γ K t) * ρ (inLamp G Γ K k)
            * (ρ (inAmbient G Γ K t))⁻¹) := by
      simpa [MonoidHom.comp_apply] using hc.eq
    simp only [lampWitness, map_mul, map_inv]
    exact key _ _ hcomm
  have hinj : Function.Injective ρ := hfaithful.injective
  refine lampWitness_ne_one G Γ K hs hk (hinj ?_)
  rw [hone, map_one]

end NonsoficGroupsExist
