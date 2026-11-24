import IdelicHeckeZeroChart
import HeckeUniformZeroCounts
import IdelicConductorBounds

open Bornology Filter Function Ideal IsDedekindDomain MeasureTheory MeromorphicOn NumberField Set
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev K := normOneIdeleClass F
private abbrev Place := HeightOneSpectrum (𝓞 F)

local instance : CompactSpace (K F) := normOneIdeleClass_compact F
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance (v : Place F) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Place F) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance : SecondCountableTopology (IdeleClass F) := ideleClass_secondCountable F

/-- A chart for the actual completed Euler continuation of a norm-one character. -/
structure CompletedHeckeChart (ω : PontryaginDual (K F)) where
  stage : Finset (Place F)
  surj : Surjective (sIdeleClassInclusion F stage)
  unramified : globalNormOneCharacter F ω ∈ (sUnramified F stage : Set (QuasiCharacter (IdeleClass F)))
  inverseUnramified : globalNormOneCharacter F ω⁻¹ ∈ (sUnramified F stage : Set (QuasiCharacter (IdeleClass F)))
  differentSupported : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ stage
  continuation : ℂ → ℂ
  meromorphic : MeromorphicOn continuation univ
  agrees : EqOn continuation (globalCompletedHeckeEuler F ω stage surj unramified) {z | 1 < z.re}
  order_outside : ∀ z : ℂ, z.re < 0 ∨ 1 < z.re → meromorphicOrderAt continuation z = 0

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include μ hν in
theorem completedHeckeChart_nonempty (ω : PontryaginDual (K F)) :
    Nonempty (CompletedHeckeChart F ω) := by
  obtain ⟨S, hs, hu, hu', hD⟩ := exists_globalHeckeTateStage F ω
  obtain ⟨_, L, he, hm, _, ho, _, _⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  exact ⟨⟨S, hs, hu, hu', hD, L, hm, he, ho⟩⟩

private abbrev Charts := ∀ ω : PontryaginDual (K F), CompletedHeckeChart F ω

def completedHeckeZeroOrder (E : Charts F) (ω : PontryaginDual (K F)) (z : ℂ) : ℤ :=
  divisor (E ω).continuation univ z

/-- Completed zeros are indexed once per norm-one component and complex zero. -/
def CompletedHeckeZeros (E : Charts F) :=
  Σ ω : PontryaginDual (K F), {z : ℂ // 0 < completedHeckeZeroOrder F E ω z}

def completedZeroCharacter (E : Charts F) (p : CompletedHeckeZeros F E) :
    PontryaginDual (IdeleClass F) :=
  heckeOrdinateCharacter F p.1 p.2.val.im

def completedZeroMultiplicity (E : Charts F) (p : CompletedHeckeZeros F E) : ℕ :=
  (completedHeckeZeroOrder F E p.1 p.2.val).toNat

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem completedZero_in_criticalStrip (E : Charts F) (p : CompletedHeckeZeros F E) :
    p.2.val.re ∈ Icc (0 : ℝ) 1 := by
  have hpos := p.2.property
  have hbad (hh : p.2.val.re < 0 ∨ 1 < p.2.val.re) : False := by
    unfold completedHeckeZeroOrder at hpos
    rw [MeromorphicOn.divisor_apply (E p.1).meromorphic (mem_univ _),
      (E p.1).order_outside _ hh, WithTop.untop₀_zero] at hpos
    exact (lt_irrefl _ hpos)
  exact ⟨le_of_not_gt fun h ↦ hbad (Or.inl h), le_of_not_gt fun h ↦ hbad (Or.inr h)⟩

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem completedZeroCharacter_on_normOne (E : Charts F) (p : CompletedHeckeZeros F E)
    (x : K F) : completedZeroCharacter F E p x.val = p.1 x :=
  DFunLike.congr_fun (heckeNormOneRestriction_ordinateCharacter F p.1 p.2.val.im) x

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem normOneEulerCharacter_on_normOne (ω : PontryaginDual (K F)) (x : K F) :
    normOneEulerCharacter F ω x.val = ω x := by
  change ω (ideleClassNormOnePart F x.val) = ω x
  congr 1
  apply Subtype.ext
  change x.val / ideleClassExpSection F (ideleClassLogNorm F x.val) = x.val
  have hx : ideleClassLogNorm F x.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F x.val)) = _
    rw [x.property, Real.log_one]
    rfl
  rw [hx, map_one, div_one]

set_option maxHeartbeats 1000000 in
omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem discriminantConductor_bound_on_annihilator (H : Subgroup (K F))
    (hgen : IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F)
      (H.map (normOneIdeleClass F).subtype))) :
    ∃ Q : ℝ, 1 ≤ Q ∧
      ∀ ω : lcaAnnihilator (G := K F) H,
        (heckeDiscriminantConductor F (normOneEulerCharacter F ω.val) : ℝ) ≤ Q := by
  let J := lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype)
  obtain ⟨b, hb, hBound⟩ := heckeConductorExponent_bounded_of_compactlyGenerated F J hgen
  obtain ⟨B, hB⟩ := heckeConductorIdeal_absNorm_bounded_of_exponents F b hb
  refine ⟨1 + (NumberField.discr F).natAbs * (B : ℝ), le_add_of_nonneg_right (by positivity), fun ω ↦ ?_⟩
  have hm : normOneEulerCharacter F ω.val ∈ J := by
    apply (mem_lcaAnnihilator_iff (G := IdeleClass F) _ _).mpr
    intro x
    obtain ⟨u, hu, he⟩ := x.property
    change normOneEulerCharacter F ω.val x.val = 1
    rw [← he]
    change normOneEulerCharacter F ω.val u.val = 1
    exact (normOneEulerCharacter_on_normOne F ω.val u).trans
      ((mem_lcaAnnihilator_iff (G := K F) H _).mp ω.property ⟨u, hu⟩)
  have h := hB _ (hBound ⟨_, hm⟩)
  unfold heckeDiscriminantConductor
  push_cast
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast h) (Nat.cast_nonneg _)).trans
    (le_add_of_nonneg_left zero_le_one)

/-- Absolute value of the Mellin symbol used for one coordinate in the zero count. -/
def completedZeroFrequency (E : Charts F) (p : CompletedHeckeZeros F E)
    (j : HeckeFrequencyDirection F) : ℝ :=
  |(mellinOrbitSlope (G := IdeleClass F) (mellinClassModulus F) 0
    (completedZeroCharacter F E p) (heckeFrequencyFlow F j)).im|

private def zeroTruncatedWeight (E : Charts F) (R : ℕ)
    (ω : PontryaginDual (K F)) (z : ℂ) : ℤ :=
  max (divisor (E ω).continuation (heckeTruncatedStrip R) z) 0

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem zeroTruncatedWeight_finite (E : Charts F) (R : ℕ) (ω : PontryaginDual (K F)) :
    (Function.support (zeroTruncatedWeight F E R ω)).Finite := by
  refine ((divisor (E ω).continuation (heckeTruncatedStrip R)).finiteSupport
    (isCompact_Icc.reProdIm isCompact_Icc)).subset ?_
  intro z hz
  contrapose! hz
  have hz' : divisor (E ω).continuation (heckeTruncatedStrip R) z = 0 :=
    Function.notMem_support.mp hz
  exact Function.notMem_support.mpr (by simp [zeroTruncatedWeight, hz'])

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem zeroTruncatedWeight_eq (E : Charts F) (R : ℕ) (p : CompletedHeckeZeros F E)
    (hR : |p.2.val.im| ≤ R) :
    zeroTruncatedWeight F E R p.1 p.2.val = (completedZeroMultiplicity F E p : ℤ) := by
  have hz : p.2.val ∈ heckeTruncatedStrip R :=
    Complex.mem_reProdIm.mpr ⟨completedZero_in_criticalStrip F E p, abs_le.mp hR⟩
  let L := (E p.1).continuation
  have hL := (E p.1).meromorphic
  have h' : divisor L (heckeTruncatedStrip R) p.2.val = completedHeckeZeroOrder F E p.1 p.2.val := by
    rw [MeromorphicOn.divisor_apply (fun w _ ↦ hL w (mem_univ w)) hz,
      completedHeckeZeroOrder, MeromorphicOn.divisor_apply hL (mem_univ _)]
  change max (divisor L (heckeTruncatedStrip R) p.2.val) 0 = _
  rw [h', max_eq_left p.2.property.le, completedZeroMultiplicity, Int.toNat_of_nonneg p.2.property.le]

set_option maxHeartbeats 1100000 in
include μ hν in
private theorem completedZero_boxes_count (E : Charts F)
    (U : Set (BruhatCompactTest (IdeleClass F))) (hU : IsVonNBounded ℂ U) :
    ∃ (H : Subgroup (K F)) (A B : ℝ) (n M : ℕ), 0 < A ∧ 0 < B ∧
      (∀ f ∈ U, ∀ k : H, ∀ x, f.val.val (k.val.val * x) = f.val.val x) ∧
      ∀ (R : ℕ) (P : Set (CompletedHeckeZeros F E)),
        (∀ p ∈ P, (∀ k : H, completedZeroCharacter F E p k.val.val = 1) ∧
          ∀ j, completedZeroFrequency F E p j ≤ R) →
        P.Finite ∧
          (∑ᶠ p : P, (completedZeroMultiplicity F E p.val : ℝ)) ≤
            A * (1 + (R : ℝ)) ^ (Module.finrank ℚ F * 14 + 3) *
              (((2 * ⌈B * (R : ℝ)⌉₊ + 1) ^ n * M : ℕ) : ℝ) := by
  obtain ⟨H, B, n, M, hB, _, hgen, hInv, hBoxes⟩ := ideleClassMellin_normOneCharacters_card_box_of_bounded F U hU
  obtain ⟨Q, hQ, hCond⟩ := discriminantConductor_bound_on_annihilator F H hgen
  obtain ⟨A, hA, hZeros⟩ := globalCompletedHecke_truncatedMultiplicity_uniform F ν η μ hν
  refine ⟨H, A * Q ^ 7, B, n, M, by positivity, hB, hInv, ?_⟩
  intro R P hP
  let I := (fun p : CompletedHeckeZeros F E ↦ p.1) '' P
  let Kbox := normOneHeckeCharactersInBox F H R
  have hParam (p : P) :
      p.val.1 ∈ Kbox ∧ |p.val.2.val.im| ≤ R ∧
      ((∑ᶠ z, zeroTruncatedWeight F E R p.val.1 z : ℤ) : ℝ) ≤
        A * Q ^ 7 * (1 + (R : ℝ)) ^ (Module.finrank ℚ F * 14 + 3) := by
    let ω := p.val.1
    let χ := completedZeroCharacter F E p.val
    let C := E ω
    have hω : heckeNormOneRestriction F χ = ω := heckeNormOneRestriction_ordinateCharacter F _ _
    have hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
        (sUnramified F C.stage : Set (QuasiCharacter (IdeleClass F))) := hω.symm ▸ C.unramified
    have hu' : globalNormOneCharacter F (heckeNormOneRestriction F χ)⁻¹ ∈
        (sUnramified F C.stage : Set (QuasiCharacter (IdeleClass F))) := hω.symm ▸ C.inverseUnramified
    have he : EqOn C.continuation
        (globalCompletedHeckeEuler F (heckeNormOneRestriction F χ) C.stage C.surj hu)
        {z | 1 < z.re} := by
      have he' (ψ : PontryaginDual (K F)) (hψ : ψ = ω)
          (hU : globalNormOneCharacter F ψ ∈
            (sUnramified F C.stage : Set (QuasiCharacter (IdeleClass F)))) :
          EqOn C.continuation (globalCompletedHeckeEuler F ψ C.stage C.surj hU)
            {z | 1 < z.re} := by subst ψ; exact C.agrees
      exact he' _ hω hu
    let y := p.val.2.val.im
    have ht : HasHeckeHeight F χ (-y) := heckeOrdinateCharacter_hasHeight F _ _
    have hP' := hP p.val p.property
    have hAnn : ω ∈ lcaAnnihilator (G := K F) H := by
      apply (mem_lcaAnnihilator_iff (G := K F) H _).mpr
      intro k
      exact (completedZeroCharacter_on_normOne F E p.val k.val).symm.trans (hP'.1 k)
    obtain ⟨hHeight, hBox⟩ :=
      (heckeFrequencyFlow_box_iff F χ C.stage C.surj hu (-y) R ht).mp hP'.2
    refine ⟨⟨hAnn, χ, C.stage, C.surj, hu, -y, hω, ht, hBox⟩, by simpa using hHeight, ?_⟩
    apply hZeros χ C.stage C.surj hu hu' C.differentSupported R (-y) Q hHeight hBox hQ _ _
      C.meromorphic he
    rw [hω]
    exact hCond ⟨ω, hAnn⟩
  have hI : I ⊆ Kbox := by
    rintro ω ⟨p, hp, rfl⟩
    exact (hParam ⟨p, hp⟩).1
  obtain ⟨hKfin, hKcard⟩ := hBoxes R (Nat.cast_nonneg R)
  have hIfin := hKfin.subset hI
  letI := hIfin.fintype
  let Fiber (ω : I) := Function.support (zeroTruncatedWeight F E R ω.val)
  letI (ω : I) : Fintype (Fiber ω) := (zeroTruncatedWeight_finite F E R ω.val).fintype
  let emb : P ↪ (Σ ω : I, Fiber ω) :=
    ⟨fun p ↦ ⟨⟨p.val.1, ⟨p.val, p.property, rfl⟩⟩, ⟨p.val.2.val, by
      change zeroTruncatedWeight F E R p.val.1 p.val.2.val ≠ 0
      rw [zeroTruncatedWeight_eq F E R p.val (hParam p).2.1, completedZeroMultiplicity,
        Int.toNat_of_nonneg p.val.2.property.le]
      exact p.val.2.property.ne'⟩⟩, by
      intro a b h
      apply Subtype.ext
      apply Sigma.subtype_ext
      · exact congrArg (fun x : Σ ω : I, Fiber ω ↦ x.1.val) h
      · exact congrArg (fun x : Σ ω : I, Fiber ω ↦ x.2.val) h⟩
  letI : Finite P := Finite.of_injective emb emb.injective
  have hPfin := Set.toFinite P
  letI := hPfin.fintype
  refine ⟨hPfin, ?_⟩
  let w (x : Σ ω : I, Fiber ω) : ℝ := zeroTruncatedWeight F E R x.1.val x.2.val
  have hw (x : Σ ω : I, Fiber ω) : 0 ≤ w x := by
    change 0 ≤ (zeroTruncatedWeight F E R x.1.val x.2.val : ℝ)
    unfold zeroTruncatedWeight
    exact_mod_cast (le_max_right (divisor (E x.1.val).continuation (heckeTruncatedStrip R) x.2.val) 0)
  have hemb (p : P) : w (emb p) = (completedZeroMultiplicity F E p.val : ℝ) := by
    change (zeroTruncatedWeight F E R p.val.1 p.val.2.val : ℝ) = _
    rw [zeroTruncatedWeight_eq F E R p.val (hParam p).2.1, Int.cast_natCast]
  have hsum (ω : I) :
      (∑ z : Fiber ω, (zeroTruncatedWeight F E R ω.val z.val : ℝ)) ≤
        A * Q ^ 7 * (1 + (R : ℝ)) ^ (Module.finrank ℚ F * 14 + 3) := by
    obtain ⟨p, hp, heq⟩ := ω.property
    have hd := (hParam ⟨p, hp⟩).2.2
    have hEq : (∑ z : Fiber ω, zeroTruncatedWeight F E R ω.val z.val) =
        ∑ᶠ z, zeroTruncatedWeight F E R ω.val z := by
      rw [← finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem, finsum_mem_support]
    rw [← Int.cast_sum, hEq, ← heq]
    exact hd
  have hCard : (Fintype.card I : ℝ) ≤ (((2 * ⌈B * (R : ℝ)⌉₊ + 1) ^ n * M : ℕ) : ℝ) := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast ((Nat.card_mono hKfin hI).trans hKcard)
  rw [finsum_eq_sum_of_fintype]
  calc
    _ = ∑ p : P, w (emb p) := Finset.sum_congr rfl fun p _ ↦ (hemb p).symm
    _ = ∑ x ∈ Finset.univ.map emb, w x := (Finset.sum_map _ _ _).symm
    _ ≤ ∑ x, w x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ ↦ hw x
    _ = ∑ ω : I, ∑ z : Fiber ω, (zeroTruncatedWeight F E R ω.val z.val : ℝ) :=
      Fintype.sum_sigma w
    _ ≤ ∑ _ω : I, A * Q ^ 7 * (1 + (R : ℝ)) ^ (Module.finrank ℚ F * 14 + 3) :=
      Finset.sum_le_sum fun ω _ ↦ hsum ω
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_comm (Fintype.card I : ℝ)]
      exact mul_le_mul_of_nonneg_left hCard (by positivity)

private theorem dyadicFrequency_exists {J : Type*} [Fintype J] (a : J → ℝ)
    (ha : ∀ j, 0 ≤ a j) : ∃ n : ℕ, ∀ j, a j ≤ (2 : ℝ) ^ (n + 1) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ j : J, a j) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, fun j ↦ ?_⟩
  exact (Finset.single_le_sum (fun i _ ↦ ha i) (Finset.mem_univ j)).trans
    (hn.le.trans (by rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]))

private def dyadicFrequencyIndex {J : Type*} [Fintype J] (a : J → ℝ) (ha : ∀ j, 0 ≤ a j) : ℕ :=
  Nat.find (dyadicFrequency_exists a ha)

private theorem dyadicFrequencyIndex_upper {J : Type*} [Fintype J] (a : J → ℝ) (ha : ∀ j, 0 ≤ a j)
    (j : J) : a j ≤ (2 : ℝ) ^ (dyadicFrequencyIndex a ha + 1) :=
  Nat.find_spec (dyadicFrequency_exists a ha) j

private theorem dyadicFrequencyIndex_lower {J : Type*} [Fintype J] (a : J → ℝ) (ha : ∀ j, 0 ≤ a j) :
    dyadicFrequencyIndex a ha = 0 ∨ ∃ j, (2 : ℝ) ^ dyadicFrequencyIndex a ha ≤ a j := by
  rcases Nat.eq_zero_or_pos (dyadicFrequencyIndex a ha) with h | h
  · exact Or.inl h
  · right
    have hlt : dyadicFrequencyIndex a ha - 1 < dyadicFrequencyIndex a ha := by omega
    have hn := Nat.find_min (dyadicFrequency_exists a ha) hlt
    push Not at hn
    obtain ⟨j, hj⟩ := hn
    rw [show dyadicFrequencyIndex a ha - 1 + 1 = dyadicFrequencyIndex a ha by omega] at hj
    exact ⟨j, hj.le⟩

private theorem dyadicBox_bound (A B : ℝ) (hA : 0 ≤ A)
    (d n M : ℕ) :
    ∃ C : ℝ, ∀ k : ℕ,
      let R := (2 : ℕ) ^ (k + 1)
      A * (1 + (R : ℝ)) ^ d * (((2 * ⌈B * (R : ℝ)⌉₊ + 1) ^ n * M : ℕ) : ℝ) ≤
        C * ((2 : ℝ) ^ (d + n)) ^ k := by
  let D := 2 * ⌈B⌉₊ + 1
  refine ⟨A * (D : ℝ) ^ n * (M : ℝ) * 3 ^ (d + n), ?_⟩
  intro k R
  have hceil : ⌈B * (R : ℝ)⌉₊ ≤ ⌈B⌉₊ * R := by
    apply Nat.ceil_le.mpr
    push_cast
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil B) (Nat.cast_nonneg R)
  have hstep : 2 * ⌈B * (R : ℝ)⌉₊ + 1 ≤ D * (1 + R) := by
    dsimp only [D]
    nlinarith
  have hbound : (1 + (R : ℝ)) ≤ 3 * (2 : ℝ) ^ k := by
    have hk : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    dsimp only [R]
    push_cast
    rw [pow_succ]
    linarith
  push_cast
  have hstepR : (2 * (⌈B * (R : ℝ)⌉₊ : ℝ) + 1) ≤ (D : ℝ) * (1 + (R : ℝ)) := by
    exact_mod_cast hstep
  calc
    _ ≤ A * (1 + (R : ℝ)) ^ d * (((D : ℝ) * (1 + (R : ℝ))) ^ n * (M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hstepR _) (Nat.cast_nonneg M)
    _ = A * (D : ℝ) ^ n * (M : ℝ) * (1 + (R : ℝ)) ^ (d + n) := by
      rw [mul_pow, pow_add]
      ring
    _ ≤ A * (D : ℝ) ^ n * (M : ℝ) * (3 * (2 : ℝ) ^ k) ^ (d + n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbound _) (by positivity)
    _ = _ := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k]
      ring

set_option maxHeartbeats 1100000 in
include μ hν in
/-- A summable majorant for the actual zero contributions, common to an
entire bounded family of compact Bruhat tests. -/
theorem completedHeckeZeros_mellin_majorant (E : Charts F)
    (V : Set (BruhatCompactTest (IdeleClass F))) (hV : IsVonNBounded ℂ V)
    (r : ℝ) (S : Set (CompletedHeckeZeros F E)) :
    ∃ u : S → ℝ, Summable u ∧ ∀ f ∈ V, ∀ p : S,
      (completedZeroMultiplicity F E p.val : ℝ) *
        ‖∫ g, f.val.val g * (Real.exp ((p.val.2.val.re + r) * (ideleClassLogNorm F g).toAdd) : ℂ) *
          (completedZeroCharacter F E p.val g : ℂ) ∂(globalClassMeasure F ν)‖ ≤ u p := by
  obtain ⟨H, A, B, n, M, hA, _, hf, hBoxes⟩ := completedZero_boxes_count F ν η μ hν E V hV
  let d := Module.finrank ℚ F * 14 + 3
  obtain ⟨C, hC⟩ := dyadicBox_bound A B hA.le d n M
  let Z := CompletedHeckeZeros F E
  let U : Set Z := {p | ∀ k : H, completedZeroCharacter F E p k.val.val = 1}
  let band (p : Z) := dyadicFrequencyIndex (completedZeroFrequency F E p) (fun _ ↦ abs_nonneg _)
  let P (i : ℕ) : Set Z := {p | p ∈ U ∧ band p = i}
  have hCount (i : ℕ) :=
    hBoxes (2 ^ (i + 1)) (P i) (fun p hp ↦ ⟨hp.1, fun j ↦ by
      have h := dyadicFrequencyIndex_upper (completedZeroFrequency F E p) (fun _ ↦ abs_nonneg _) j
      change completedZeroFrequency F E p j ≤ (2 : ℝ) ^ (band p + 1) at h
      simpa only [show band p = i from hp.2, Nat.cast_pow, Nat.cast_ofNat] using h⟩)
  letI (i : ℕ) : Fintype (P i) := (hCount i).1.fintype
  let e : (Σ i, P i) ≃ U :=
    { toFun := fun ⟨_, p⟩ ↦ ⟨p.val, p.property.1⟩
      invFun := fun p ↦ ⟨band p.val, ⟨p.val, p.property, rfl⟩⟩
      left_inv := fun ⟨_, p⟩ ↦ Sigma.subtype_ext p.property.2 rfl
      right_inv := fun _ ↦ rfl }
  letI : (globalClassMeasure F ν).IsHaarMeasure := globalClassMeasure_isHaar F ν
  let m := mellinClassModulus F
  have hm : IsProperMap m :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have hms : Surjective m :=
    fun t => ⟨ideleClassExpSection F t, ideleClassLogNorm_expSection F t⟩
  have hH (k : H) : m k.val.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F k.val.val)) = 1
    rw [show ideleClassNorm F k.val.val = 1 from k.val.property, Real.log_one]
    rfl
  have hfreq (i : ℕ) (p : P i) : i = 0 ∨ ∃ j : HeckeFrequencyDirection F,
      (2 : ℝ) ^ i ≤ completedZeroFrequency F E (e ⟨i, p⟩).val j := by
    have hr := dyadicFrequencyIndex_lower (completedZeroFrequency F E p.val) (fun _ ↦ abs_nonneg _)
    change band p.val = 0 ∨ ∃ j, (2 : ℝ) ^ band p.val ≤ completedZeroFrequency F E p.val j at hr
    rw [show (e ⟨i, p⟩).val = p.val from rfl]
    simpa only [show band p.val = i from p.property.2] using hr
  have hcount (i : ℕ) :
      (∑ p : P i, (completedZeroMultiplicity F E (e ⟨i, p⟩).val : ℝ)) ≤ C * ((2 : ℝ) ^ (d + n)) ^ i := by
    change (∑ p : P i, (completedZeroMultiplicity F E p.val : ℝ)) ≤ _
    rw [← finsum_eq_sum_of_fintype]
    exact (hCount i).2.trans (hC i)
  obtain ⟨u, hu, h⟩ := modulatedMellin_majorant_of_invariant_joint_count (globalClassMeasure F ν)
    m hm hms V hV (fun k : H ↦ k.val.val) hH hf
    (completedZeroCharacter F E) (fun p ↦ p.2.val.re) (completedZeroMultiplicity F E)
    (heckeFrequencyFlow F) e (a := 0) (b := 1) (C := C) (d + n)
    (fun p ↦ completedZero_in_criticalStrip F E (e p).val) hfreq hcount r S
  refine ⟨u, hu, fun f hf p ↦ ?_⟩
  convert h f hf p using 3
  apply integral_congr_ae
  exact Eventually.of_forall fun g ↦ by
    change f.val.val g * _ * _ = (Real.exp ((p.val.2.val.re + r) * (ideleClassLogNorm F g).toAdd) : ℂ) *
      f.val.val g * _
    rw [mul_comm (f.val.val g)]

set_option maxHeartbeats 1100000 in
include μ hν in
/-- Corrected Lemma B.4.4.9. The actual completed zero family admits
absolute Mellin summation over every subset, with multiplicity and any real
modulus twist. The choice of a valid Euler continuation chart is arbitrary. -/
theorem completedHeckeZeros_mellin_summable (E : Charts F)
    (f : BruhatCompactTest (IdeleClass F)) (r : ℝ) (S : Set (CompletedHeckeZeros F E)) :
    Summable (fun p : S ↦ (completedZeroMultiplicity F E p.val : ℝ) *
      ‖∫ g, f.val.val g * (Real.exp ((p.val.2.val.re + r) * (ideleClassLogNorm F g).toAdd) : ℂ) *
        (completedZeroCharacter F E p.val g : ℂ) ∂(globalClassMeasure F ν)‖) := by
  obtain ⟨u, hu, h⟩ := completedHeckeZeros_mellin_majorant F ν η μ hν E
    {f} (isVonNBounded_singleton f) r S
  exact hu.of_nonneg_of_le (fun _ => by positivity) (h f (mem_singleton f))

include μ hν in
/-- Absolute convergence of the unweighted sum (B.4.4.19) on every subset. -/
theorem completedHeckeZeros_mellin_absolute (E : Charts F)
    (f : BruhatCompactTest (IdeleClass F)) (r : ℝ) (S : Set (CompletedHeckeZeros F E)) :
    Summable (fun p : S ↦
      ‖∫ g, f.val.val g * (Real.exp ((p.val.2.val.re + r) * (ideleClassLogNorm F g).toAdd) : ℂ) *
        (completedZeroCharacter F E p.val g : ℂ) ∂(globalClassMeasure F ν)‖) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦ ?_)
    (completedHeckeZeros_mellin_summable F ν η μ hν E f r S)
  apply le_mul_of_one_le_left (norm_nonneg _)
  have hw : 1 ≤ completedZeroMultiplicity F E p.val := by
    have hp := p.val.2.property
    have hh := Int.toNat_of_nonneg hp.le
    unfold completedZeroMultiplicity
    omega
  exact_mod_cast hw


/-- The split unitary and real factors evaluate the chart quasi-character
at its actual zero, with the additional real twist from (B.4.4.19). -/
theorem completedZero_mellin_weight (E : Charts F) (p : CompletedHeckeZeros F E)
    (r : ℝ) (g : IdeleClass F) :
    (Real.exp ((p.2.val.re + r) * (ideleClassLogNorm F g).toAdd) : ℂ) *
        (completedZeroCharacter F E p g : ℂ) =
      (normOneEulerCharacter F p.1 g : ℂ) *
        Complex.exp ((p.2.val + (r : ℂ)) * ((ideleClassLogNorm F g).toAdd : ℂ)) := by
  let z := p.2.val
  let x := (ideleClassLogNorm F g).toAdd
  change (Real.exp ((z.re + r) * x) : ℂ) *
      ((normOneEulerCharacter F p.1 g * Circle.exp (z.im * x) : Circle) : ℂ) = _
  rw [Complex.ofReal_exp, Circle.coe_mul, Circle.coe_exp, mul_left_comm, ← Complex.exp_add]
  apply congrArg (fun w ↦ (normOneEulerCharacter F p.1 g : ℂ) * Complex.exp w)
  change (((z.re + r) * x : ℝ) : ℂ) + (((z.im * x : ℝ) : ℂ) * Complex.I) =
    (z + (r : ℂ)) * (x : ℂ)
  conv_rhs => rw [← Complex.re_add_im z]
  push_cast
  ring

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- Changing the Tate stage or meromorphic representative preserves the actual zero orders. -/
theorem completedHeckeZeroOrder_chart_independent (E E' : Charts F)
    (ω : PontryaginDual (K F)) (z : ℂ) :
    completedHeckeZeroOrder F E ω z = completedHeckeZeroOrder F E' ω z := by
  let C := E ω
  let C' := E' ω
  have he' : EqOn C'.continuation (globalCompletedHeckeEuler F ω C.stage C.surj C.unramified)
      {z | 1 < z.re} := by
    rw [globalCompletedHeckeEuler_stage_eq F ω C.stage C.surj C.unramified
      C'.stage C'.surj C'.unramified]
    exact C'.agrees
  have h := globalHeckeContinuation_unique_germ C.meromorphic C'.meromorphic C.agrees he' z
  unfold completedHeckeZeroOrder
  rw [MeromorphicOn.divisor_apply C.meromorphic (mem_univ _),
    MeromorphicOn.divisor_apply C'.meromorphic (mem_univ _), meromorphicOrderAt_congr h]

end
end Masullo
