import IdelicWeilPrimeSamples
import IdelicWeilFiniteLinear

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField ENNReal NNReal Pointwise

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F
private abbrev U (v : Place F) := principalIntegralUnits F v

local instance weilConductorClassLocallyCompact : LocallyCompactSpace (IdeleClass F) :=
  ideleClasses_locallyCompact
local instance weilConductorClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance weilConductorNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance weilConductorNormOneBorel : BorelSpace (K F) := ⟨rfl⟩
local instance weilConductorUnitCompact (v : Place F) : CompactSpace (U F v) :=
  principalIntegralUnits_compactSpace F v

variable (v : Place F)

local notation "L" => (v.adicCompletion F)ˣ
local notation "q" => (v.asIdeal.absNorm : ℝ)

set_option maxHeartbeats 1000000

/-- The subgroup of integral units within the radius defining a finite
Hecke conductor level. Level zero is the full integral unit group. -/
def idelicWeilCongruenceUnits (n : ℕ) : Subgroup (U F v) where
  carrier := {u | ‖u.val.val - 1‖ ≤ q ^ (-(n : ℤ))}
  one_mem' := by
    change ‖(1 : v.adicCompletion F) - 1‖ ≤ q ^ (-(n : ℤ))
    simp only [sub_self, norm_zero]
    positivity
  mul_mem' {u w} hu hw := by
    change ‖u.val.val - 1‖ ≤ _ at hu
    change ‖w.val.val - 1‖ ≤ _ at hw
    change ‖u.val.val * w.val.val - 1‖ ≤ _
    rw [show u.val.val * w.val.val - 1 =
      u.val.val * (w.val.val - 1) + (u.val.val - 1) by ring]
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    rw [norm_mul, show ‖u.val.val‖ = 1 from u.property, one_mul]
    exact max_le hw hu
  inv_mem' {u} hu := by
    change ‖u.val.val - 1‖ ≤ _ at hu
    change ‖u.val⁻¹.val - 1‖ ≤ _
    have he : u.val⁻¹.val - 1 = -(u.val⁻¹.val * (u.val.val - 1)) := by
      rw [mul_sub, show u.val⁻¹.val * u.val.val = 1 from u.val.inv_val, mul_one]
      ring
    rwa [he, norm_neg, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
      show ‖u.val.val‖ = 1 from u.property, inv_one, one_mul]

private abbrev H (n : ℕ) := idelicWeilCongruenceUnits F v n

private theorem congruenceUnits_closed (n : ℕ) : IsClosed (H F v n : Set (U F v)) :=
  isClosed_le ((Units.continuous_val.comp continuous_subtype_val).sub continuous_const).norm
    continuous_const

private theorem congruenceUnits_open (n : ℕ) : IsOpen (H F v n : Set (U F v)) := by
  have hq : (1 : ℝ) < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hr : (0 : ℝ) < q ^ (-(n : ℤ)) := zpow_pos (zero_lt_one.trans hq) _
  have hval : Continuous (fun u : U F v => u.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  exact (IsUltrametricDist.isOpen_closedBall (1 : v.adicCompletion F) hr.ne').preimage hval

local instance weilConductorLevelCompact (n : ℕ) : CompactSpace (H F v n) :=
  isCompact_iff_compactSpace.mp (congruenceUnits_closed F v n).isCompact
local instance weilConductorLevelMeasurable (n : ℕ) : MeasurableSpace (H F v n) := borel _
local instance weilConductorLevelBorel (n : ℕ) : BorelSpace (H F v n) := ⟨rfl⟩

private def congruenceHaar (n : ℕ) : Measure (H F v n) := Measure.haarMeasure ⊤

private theorem congruenceHaar_univ (n : ℕ) : congruenceHaar F v n univ = 1 :=
  Measure.haarMeasure_self (K₀ := ⊤)

private def congruenceInclusion (n : ℕ) : H F v n →ₜ* K F :=
  (idelicWeilLocalUnitInclusion F v).comp ⟨(H F v n).subtype, continuous_subtype_val⟩

private theorem congruence_trivial_iff (ω : PontryaginDual (K F)) (n : ℕ) :
    ω.comp (congruenceInclusion F v n) = 1 ↔
      heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v ≤ n := by
  let χ := heckeOrdinateCharacter F ω 0
  let P := finiteConductorLevels F v (fun u => χ (ideleClassMap F (singleFiniteIdele F v u)))
  have hP : n ∈ P ↔ heckeConductorExponent F χ v ≤ n := by
    have h := heckeConductorExponent_isLeast F χ v
    exact ⟨fun hn => h.2 hn, fun hn => finiteConductorLevels_mono F v _ h.1 hn⟩
  rw [← hP]
  have he (u : U F v) : χ (ideleClassMap F (singleFiniteIdele F v u.val)) =
      ω (idelicWeilLocalUnitInclusion F v u) := by
    dsimp only [χ]
    rw [idelicWeil_ordinate_zero_eq, ← finitePlaceInsertion_apply, normOneEulerCharacter_localUnit]
  constructor
  · intro h u hu hd
    let w : H F v n := ⟨⟨u, hu⟩, hd⟩
    have hw := congrArg (fun θ : PontryaginDual (H F v n) => θ w) h
    change ω (idelicWeilLocalUnitInclusion F v w.val) = 1 at hw
    exact (he w.val).trans hw
  · intro h
    apply PontryaginDual.ext
    intro w
    change ω (idelicWeilLocalUnitInclusion F v w.val) = 1
    exact (he w.val).symm.trans (h w.val.val w.val.property w.property)

private theorem congruenceHaar_inv_character (ω : PontryaginDual (K F)) (n : ℕ) :
    (∫ u : H F v n, (((ω (congruenceInclusion F v n u))⁻¹ : Circle) : ℂ) ∂congruenceHaar F v n) =
      if heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v ≤ n then 1 else 0 := by
  let θ := ω.comp (congruenceInclusion F v n)
  letI : (congruenceHaar F v n).IsHaarMeasure := by unfold congruenceHaar; infer_instance
  have hm : (congruenceHaar F v n).real univ = 1 := by
    rw [measureReal_def, congruenceHaar_univ, ENNReal.toReal_one]
  have h := integral_character_pair (congruenceHaar F v n) θ 1
  have hθ : θ = 1 ↔ heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v ≤ n :=
    congruence_trivial_iff F v ω n
  simp only [hm, Complex.ofReal_one] at h
  have he : (if θ = 1 then (1 : ℂ) else 0) =
      if heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v ≤ n then 1 else 0 :=
    if_congr hθ rfl rfl
  refine (integral_congr_ae (Eventually.of_forall fun u => ?_)).trans (h.trans he)
  change (((θ u)⁻¹ : Circle) : ℂ) = star (θ u : ℂ) * (1 : ℂ)
  rw [mul_one, Circle.coe_inv_eq_conj, ← Complex.star_def]

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

/-- The Fourier expansion of the probability mean over a principal
congruence subgroup retains exactly the characters of conductor at most its level. -/
theorem idelicWeil_congruenceAverage_hasSum
    (f : BruhatCompactTest (IdeleClass F)) (n : ℕ) :
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * (idelicWeilCenteredTest F ν ω f).val 0) *
        (if heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v ≤ n then 1 else 0))
      (∫ u : H F v n, f.val.val (finitePlaceInsertion F v u.val.val) ∂congruenceHaar F v n) := by
  letI : IsProbabilityMeasure (congruenceHaar F v n) := ⟨congruenceHaar_univ F v n⟩
  have h := hasSum_idelicWeil_compactAverage F ν (congruenceHaar F v n)
    (congruenceInclusion F v n) (congruenceInclusion F v n).continuous.measurable f 1
  simp only [congruenceHaar_inv_character F v] at h
  have he :
      (∫ u : H F v n, f.val.val ((congruenceInclusion F v n u).val * 1) ∂congruenceHaar F v n) =
        ∫ u : H F v n, f.val.val (finitePlaceInsertion F v u.val.val) ∂congruenceHaar F v n := by
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      change f.val.val (finitePlaceInsertion F v u.val.val * 1) = _
      exact congrArg f.val.val (mul_one (finitePlaceInsertion F v u.val.val))
  rw [he] at h
  refine h.congr_fun fun ω => ?_
  have h1 : ideleClassExpSection F (Multiplicative.ofAdd (0 : ℝ)) = 1 := map_one _
  have hg : idelicWeilLogProfile F ν ω f 0 = ∫ a : K F, (ω a : ℂ) * f.val.val (a.val * 1) ∂ν := by
    change (∫ a : K F, (ω a : ℂ) * f.val.val
      (a.val * ideleClassExpSection F (Multiplicative.ofAdd (0 : ℝ))) ∂ν) = _
    rw [h1]
  change (_ * idelicWeilLogProfile F ν ω f 0) * _ = _
  rw [hg]

/-- A compact idelic test is invariant under some principal congruence
subgroup at each finite place. -/
theorem idelicWeil_exists_congruence_invariance (f : BruhatCompactTest (IdeleClass F)) :
    ∃ N : ℕ, ∀ (a : H F v N) (x : IdeleClass F),
      f.val.val (finitePlaceInsertion F v a.val.val * x) = f.val.val x := by
  obtain ⟨C, A, _, hA, hInv⟩ :=
    bruhatCompactTest_common_finite_stage F {f} (isVonNBounded_singleton f)
  have ho : IsOpen ((integralUnitFamilySingle F v) ⁻¹' (A : Set (IntegralUnitFamily F))) :=
    hA.preimage (integralUnitFamilySingle_continuous F v)
  have h1 : (1 : U F v) ∈ (integralUnitFamilySingle F v) ⁻¹' (A : Set (IntegralUnitFamily F)) := by
    change integralUnitFamilySingle F v 1 ∈ A
    rw [show integralUnitFamilySingle F v 1 = 1 from Function.update_eq_self _ _]
    exact A.one_mem
  let S := (integralUnitFamilySingle F v) ⁻¹' (A : Set (IntegralUnitFamily F))
  have hemb : Topology.IsEmbedding (fun u : U F v => u.val.val) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.comp IsEmbedding.subtypeVal
  have hnhds : S ∈ 𝓝 (1 : U F v) := ho.mem_nhds h1
  rw [hemb.isInducing.nhds_eq_comap] at hnhds
  obtain ⟨W, hW, hsub⟩ := mem_comap.mp hnhds
  change W ∈ 𝓝 (1 : v.adicCompletion F) at hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (inv_nonneg.mpr (zero_lt_one.trans hq).le) (inv_lt_one_of_one_lt₀ hq)
  obtain ⟨N, hN⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  refine ⟨N, fun a x => ?_⟩
  have ha : a.val ∈ S := by
    apply hsub
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hle : ‖a.val.val.val - (1 : v.adicCompletion F)‖ ≤ (q⁻¹ : ℝ) ^ N := by
      have ha := a.property
      change ‖a.val.val.val - (1 : v.adicCompletion F)‖ ≤ q ^ (-(N : ℤ)) at ha
      rwa [zpow_neg, zpow_natCast, ← inv_pow] at ha
    exact hle.trans_lt hN
  have h := (hInv f (mem_singleton f)).2 x _ ha
  rw [integralUnitFamilySingle_class] at h
  exact (congrArg f.val.val (mul_comm _ _)).trans h

private theorem centeredTest_zero_of_congruence
    (f : BruhatCompactTest (IdeleClass F)) (N : ℕ)
    (hInv : ∀ (a : H F v N) (x : IdeleClass F),
      f.val.val (finitePlaceInsertion F v a.val.val * x) = f.val.val x)
    (ω : PontryaginDual (K F))
    (hN : ¬ heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v ≤ N) :
    (idelicWeilCenteredTest F ν ω f).val 0 = 0 := by
  have hne : ω.comp (congruenceInclusion F v N) ≠ 1 :=
    fun h => hN ((congruence_trivial_iff F v ω N).mp h)
  obtain ⟨a, ha⟩ : ∃ a : H F v N, ω (congruenceInclusion F v N a) ≠ 1 := by
    by_contra! h
    exact hne (PontryaginDual.ext h)
  let k := congruenceInclusion F v N a
  let R := ideleClassExpSection F (Multiplicative.ofAdd (0 : ℝ))
  let g (b : K F) := (ω b : ℂ) * f.val.val (b.val * R)
  change (∫ b : K F, g b ∂ν) = 0
  have hmul (b : K F) : g (k * b) = (ω k : ℂ) * g b := by
    dsimp only [g]
    rw [map_mul, Circle.coe_mul]
    have hh : f.val.val ((k * b).val * R) = f.val.val (b.val * R) := by
      change f.val.val ((finitePlaceInsertion F v a.val.val * b.val) * R) = _
      exact (congrArg f.val.val (mul_assoc _ _ _)).trans (hInv a (b.val * R))
    rw [hh, mul_assoc]
  have h := integral_mul_left_eq_self (μ := ν) g k
  simp_rw [hmul, integral_const_mul] at h
  have hz : (ω k : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun he => ha (Subtype.ext he)
  apply (mul_eq_zero.mp ?_).resolve_left hz
  rw [sub_mul, h, one_mul, sub_self]

private theorem sum_conductor_indicators {c N : ℕ} (hc : c ≤ N) :
    (∑ n ∈ Finset.range N, ((1 : ℂ) - (if c ≤ n then 1 else 0))) = (c : ℂ) := by
  induction N generalizing c with
  | zero =>
      have : c = 0 := Nat.eq_zero_of_le_zero hc
      simp [this]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      by_cases h : c ≤ N
      · rw [ih h, ite_eq_left h, sub_self, add_zero]
      · have he : c = N + 1 := by omega
        subst c
        have hsum : (∑ n ∈ Finset.range N, ((1 : ℂ) -
            (if N + 1 ≤ n then 1 else 0))) =
            ∑ n ∈ Finset.range N, ((1 : ℂ) - (if N ≤ n then 1 else 0)) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hn' := Finset.mem_range.mp hn
          rw [ite_eq_right (by omega : ¬ N + 1 ≤ n), ite_eq_right hn'.not_ge]
        rw [hsum, ih (Nat.le_refl N)]
        simp

/-- The signed sum of the first congruence means gives the local conductor
contact term. A congruence level of invariance for the test bounds every
conductor that can contribute to its norm-one Fourier expansion. -/
theorem idelicWeil_conductorContact_hasSum_means
    (f : BruhatCompactTest (IdeleClass F)) (N : ℕ)
    (hInv : ∀ (a : H F v N) (x : IdeleClass F),
      f.val.val (finitePlaceInsertion F v a.val.val * x) = f.val.val x) :
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * (idelicWeilCenteredTest F ν ω f).val 0) *
        (heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v : ℂ))
      (∑ n ∈ Finset.range N, (f.val.val 1 -
        ∫ u : H F v n, f.val.val (finitePlaceInsertion F v u.val.val) ∂congruenceHaar F v n)) := by
  let a (ω : PontryaginDual (K F)) :=
    (ν.real univ : ℂ)⁻¹ * (idelicWeilCenteredTest F ν ω f).val 0
  let c (ω : PontryaginDual (K F)) := heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v
  have hid : HasSum a (f.val.val 1) := by
    have h := hasSum_idelicWeilLogProfile F ν f 0
    rw [show ideleClassExpSection F (Multiplicative.ofAdd (0 : ℝ)) = 1 from map_one _] at h
    exact h
  have h := hasSum_sum (s := Finset.range N) (fun n _ =>
    hid.sub (idelicWeil_congruenceAverage_hasSum F v ν f n))
  refine h.congr_fun fun ω => ?_
  change a ω * (c ω : ℂ) =
    ∑ n ∈ Finset.range N, (a ω - a ω * (if c ω ≤ n then 1 else 0))
  by_cases hc : c ω ≤ N
  · simp_rw [← mul_one_sub]
    rw [← Finset.mul_sum, sum_conductor_indicators hc]
  · have hz : (idelicWeilCenteredTest F ν ω f).val 0 = 0 :=
      centeredTest_zero_of_congruence F v ν f N hInv ω hc
    have hzero : a ω = 0 := by dsimp only [a]; rw [hz, mul_zero]
    simp [hzero]

private def congruenceEmbedding (n : ℕ) : H F v n →* L :=
  (U F v).subtype.comp (H F v n).subtype

private theorem congruenceEmbedding_open (n : ℕ) :
    IsOpenEmbedding (congruenceEmbedding F v n) := by
  have hU : IsOpen (U F v : Set L) := by
    rw [show (U F v : Set L) = finitePlaceIntegralUnits F v from
      Set.ext fun a => (integralUnits_iff_norm F v a).symm]
    exact localIntegralUnits_open F v
  exact hU.isOpenEmbedding_subtypeVal.comp (congruenceUnits_open F v n).isOpenEmbedding_subtypeVal

private theorem congruenceEmbedding_range (n : ℕ) :
    range (congruenceEmbedding F v n) =
      {u : L | ‖u.val‖ = 1 ∧ ‖u.val - 1‖ ≤ q ^ (-(n : ℤ))} := by
  ext u
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val.property, a.property⟩
  · rintro ⟨hu, hd⟩
    exact ⟨⟨⟨u, hu⟩, hd⟩, rfl⟩

private theorem norm_eq_one_of_congruence (n : ℕ) (hn : n ≠ 0) (x : v.adicCompletion F)
    (hx : ‖x - 1‖ ≤ q ^ (-(n : ℤ))) : ‖x‖ = 1 := by
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hr : q ^ (-(n : ℤ)) < 1 := zpow_lt_one_of_neg₀ hq (by omega)
  have hlt := hx.trans_lt hr
  have ha := IsUltrametricDist.norm_add_le_max (1 : v.adicCompletion F) (x - 1)
  have hb := IsUltrametricDist.norm_add_le_max x (-(x - 1))
  rw [show 1 + (x - 1) = x by ring, norm_one, max_eq_left hlt.le] at ha
  rw [show x + -(x - 1) = 1 by ring, norm_one, norm_neg, le_max_iff] at hb
  exact le_antisymm ha (hb.resolve_right hlt.not_ge)

private theorem congruenceEmbedding_range_zero :
    range (congruenceEmbedding F v 0) = finitePlaceIntegralUnits F v := by
  rw [congruenceEmbedding_range]
  ext u
  rw [integralUnits_iff_norm]
  constructor
  · exact And.left
  · intro hu
    refine ⟨hu, ?_⟩
    simpa only [sub_eq_add_neg, norm_neg, norm_one, hu, max_self, Nat.cast_zero, neg_zero, zpow_zero] using
      (IsUltrametricDist.norm_add_le_max u.val (-(1 : v.adicCompletion F)))

private def congruenceWeight : ℕ → ℝ
  | 0 => 1
  | n + 1 => q ^ (n + 1) - q ^ n

private theorem sum_congruenceWeight (k : ℕ) :
    ∑ n ∈ Finset.range (k + 1), congruenceWeight F v n = q ^ k := by
  induction k with
  | zero => simp [congruenceWeight]
  | succ k ih => rw [Finset.sum_range_succ, ih, congruenceWeight]; ring

private theorem ordinary_unit_weight_finite (g : L → ℂ) (N : ℕ)
    (hN : ∀ u ∈ range (congruenceEmbedding F v N), g u = 0)
    (u : L) (hu : u ∈ finitePlaceIntegralUnits F v) :
    ‖u.val - 1‖⁻¹ • g u =
      ∑ n ∈ Finset.range N, congruenceWeight F v n •
        (range (congruenceEmbedding F v n)).indicator g u := by
  let A (n : ℕ) := range (congruenceEmbedding F v n)
  have hnorm := (integralUnits_iff_norm F v u).mp hu
  have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hm (n : ℕ) : u ∈ A n ↔ ‖u.val - 1‖ ≤ q ^ (-(n : ℤ)) := by
    dsimp only [A]
    rw [congruenceEmbedding_range]
    exact and_iff_right hnorm
  by_cases huN : u ∈ A N
  · simp only [hN u huN, smul_zero]
    refine (Finset.sum_eq_zero fun n hn => ?_).symm
    by_cases hun : u ∈ A n
    · rw [indicator_of_mem hun, hN u huN, smul_zero]
    · rw [indicator_of_notMem hun, smul_zero]
  · have hx : u.val - 1 ≠ 0 := by
      intro he
      apply huN
      rw [hm, he, norm_zero]
      exact (zpow_pos (zero_lt_one.trans hq) _).le
    let x := Units.mk0 (u.val - 1) hx
    obtain ⟨k, hk⟩ := iUnion_eq_univ_iff.mp (finiteZetaShell_iUnion F v) x
    change ‖u.val - 1‖ = q ^ (-k) at hk
    have hk₀ : 0 ≤ k := by
      have hu0 : u ∈ A 0 := by
        dsimp only [A]
        rwa [congruenceEmbedding_range_zero]
      have hb := (hm 0).mp hu0
      rw [hk, zpow_le_zpow_iff_right₀ hq] at hb
      omega
    have hmem (n : ℕ) : u ∈ A n ↔ n ≤ k.toNat := by
      rw [hm, hk, zpow_le_zpow_iff_right₀ hq]
      omega
    have hkN : k.toNat < N := lt_of_not_ge (fun h => huN ((hmem N).mpr h))
    have hs : Finset.range (k.toNat + 1) ⊆ Finset.range N :=
      Finset.range_subset_range.mpr (Nat.succ_le_of_lt hkN)
    have he : (∑ n ∈ Finset.range N, congruenceWeight F v n • (A n).indicator g u) =
        ∑ n ∈ Finset.range (k.toNat + 1), congruenceWeight F v n • g u := by
      rw [← Finset.sum_subset hs (fun n _ hn => by
        have hn' : ¬ n ≤ k.toNat := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
        rw [indicator_of_notMem (fun h => hn' ((hmem n).mp h)), smul_zero])]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn' : n ≤ k.toNat := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [indicator_of_mem ((hmem n).mpr hn')]
    have hpow : (q ^ k.toNat : ℝ) = q ^ k := by
      calc
        _ = q ^ (k.toNat : ℤ) := (zpow_natCast _ _).symm
        _ = _ := congrArg (fun e : ℤ => q ^ e) (Int.toNat_of_nonneg hk₀)
    rw [he, ← Finset.sum_smul, sum_congruenceWeight, hk, ← zpow_neg, neg_neg, hpow]

section Restriction

variable [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  (μ : Measure (v.adicCompletion F)ˣ) [μ.IsHaarMeasure]

private theorem integral_congruence_eq_mean (g : L → ℂ) (n : ℕ) :
    (∫ u in range (congruenceEmbedding F v n), g u ∂μ) =
      μ.real (range (congruenceEmbedding F v n)) •
        ∫ u : H F v n, g (congruenceEmbedding F v n u) ∂congruenceHaar F v n := by
  let i := congruenceEmbedding F v n
  have he : IsOpenEmbedding i := congruenceEmbedding_open F v n
  have hm : MeasurableEmbedding i := he.measurableEmbedding
  letI : (μ.comap i).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) μ he
  letI : (congruenceHaar F v n).IsHaarMeasure := by unfold congruenceHaar; infer_instance
  have hscale := Measure.isMulInvariant_eq_smul_of_compactSpace (μ.comap i) (congruenceHaar F v n)
  have hmass := congrArg (fun τ : Measure (H F v n) => τ univ) hscale
  change (μ.comap i) univ = _ at hmass
  rw [hm.comap_apply, image_univ, Measure.smul_apply, congruenceHaar_univ,
    ENNReal.smul_def, smul_eq_mul, mul_one] at hmass
  change (∫ u in range i, g u ∂μ) = _
  rw [← hm.map_comap, hm.integral_map g, hscale, integral_smul_nnreal_measure]
  change (Measure.haarScalarFactor (μ.comap i) (congruenceHaar F v n) : ℝ) •
    (∫ u : H F v n, g (i u) ∂congruenceHaar F v n) = _
  rw [show μ.real (range (congruenceEmbedding F v n)) =
      (Measure.haarScalarFactor (μ.comap i) (congruenceHaar F v n) : ℝ) from by
    rw [measureReal_def, hmass, ENNReal.coe_toReal]]

end Restriction

section HaarMass

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
  (α : Measure (v.adicCompletion F)) [α.IsAddHaarMeasure]

private theorem additive_congruenceBall_mass (n : ℕ) :
    α.real (Metric.closedBall (1 : v.adicCompletion F) (q ^ (-(n : ℤ)))) =
      q ^ (-(n : ℤ)) * α.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  let π := chosenFiniteUniformizer F v
  let B := Metric.closedBall (0 : v.adicCompletion F) 1
  have hπ : ‖(π ^ n).val‖ = q ^ (-(n : ℤ)) := by
    rw [Units.val_pow_eq_pow_val, norm_pow, norm_finiteUniformizer F v π.val
      (chosenFiniteUniformizer_spec F v), zpow_neg, zpow_natCast, inv_pow]
  have htranslate : Metric.closedBall (1 : v.adicCompletion F) (q ^ (-(n : ℤ))) =
      (fun x : v.adicCompletion F => -1 + x) ⁻¹'
        (Metric.closedBall 0 (q ^ (-(n : ℤ)))) := by
    ext x
    simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    rw [sub_zero, show (-1 : v.adicCompletion F) + x = x - 1 by ring]
  have hscale : (π ^ n) • B = Metric.closedBall 0 (q ^ (-(n : ℤ))) := by
    rw [← hπ]
    change (π ^ n).val • B = _
    exact smul_unitClosedBall _
  rw [htranslate, measureReal_def, measure_preimage_add α, ← hscale,
    finitePlace_addHaar_smul F v α, ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm, hπ]
  rw [show B = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) from
    finiteCompletion_closedBall F v, measureReal_def]

variable [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]
  (μ : Measure (v.adicCompletion F)ˣ) [μ.IsHaarMeasure]

/-- For each positive congruence level, the mass relative to the full
unit group is the additive ball's radius times the Tamagawa density. -/
theorem idelicWeil_congruence_measureReal (n : ℕ) (hn : n ≠ 0)
    (hμ : μ (finitePlaceIntegralUnits F v) =
      α (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    μ.real (range (congruenceEmbedding F v n)) =
      q / (q - 1) * q ^ (-(n : ℤ)) * μ.real (finitePlaceIntegralUnits F v) := by
  let A := range (congruenceEmbedding F v n)
  have hA : IsOpen A := (congruenceEmbedding_open F v n).isOpen_range
  have hi : MeasurableEmbedding (Units.val : L → v.adicCompletion F) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding
  have himg : Units.val '' A = Metric.closedBall (1 : v.adicCompletion F) (q ^ (-(n : ℤ))) := by
    ext x
    rw [show A = _ from congruenceEmbedding_range F v n, Metric.mem_closedBall, dist_eq_norm]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu.2
    · intro hx
      have hnorm := norm_eq_one_of_congruence F v n hn x hx
      have hne : x ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne one_ne_zero)
      exact ⟨Units.mk0 x hne, ⟨hnorm, hx⟩, rfl⟩
  have hd : finitePlaceUnitDensity F v α A = α (Units.val '' A) := by
    rw [finitePlaceUnitDensity, withDensity_apply _ hA.measurableSet, ← hi.comap_apply α A]
    calc
      _ = ∫⁻ _u in A, (1 : ℝ≥0∞) ∂α.comap Units.val := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hA.measurableSet] with u hu
        have hu' : ‖u.val‖ = 1 := ((congrArg (u ∈ ·) (congruenceEmbedding_range F v n)).mp hu).1
        have hn : ‖u.val‖₊ = 1 := NNReal.eq (by simpa only [coe_nnnorm, NNReal.coe_one] using hu')
        rw [hn, ENNReal.coe_one, inv_one]
      _ = _ := by simp
  have hq : (1 : ℝ≥0∞) ≤ v.asIdeal.absNorm := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  change μ.real A = _
  have hden := congrArg (fun τ : Measure L => τ A) (finitePlaceTamagawa_density F v α μ hμ)
  change μ A = _ at hden
  rw [measureReal_def μ A, hden, Measure.smul_apply, smul_eq_mul, hd,
    himg, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_sub_of_le hq (ENNReal.natCast_ne_top _),
    ENNReal.toReal_one, ENNReal.toReal_natCast]
  change q / (q - 1) * α.real _ = _
  rw [additive_congruenceBall_mass F v α, mul_assoc,
    measureReal_def μ (finitePlaceIntegralUnits F v), hμ, measureReal_def]

private theorem congruenceWeight_mul_mass
    (hμ : μ (finitePlaceIntegralUnits F v) =
      α (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (n : ℕ) :
    congruenceWeight F v n * μ.real (range (congruenceEmbedding F v n)) =
      μ.real (finitePlaceIntegralUnits F v) := by
  cases n with
  | zero => rw [congruenceWeight, congruenceEmbedding_range_zero, one_mul]
  | succ k =>
      have hq : 1 < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
      have hd : q - 1 ≠ 0 := sub_ne_zero.mpr hq.ne'
      rw [idelicWeil_congruence_measureReal F v α μ (k + 1) (Nat.succ_ne_zero k) hμ,
        congruenceWeight, zpow_neg, zpow_natCast, pow_succ q k]
      field_simp

/-- The exact conductor comparison at a finite place, including the sign
of the subtracted canonical Weil unit integral. -/
theorem idelicWeil_conductorContact_hasSum_cutoff
    (hμ : μ (finitePlaceIntegralUnits F v) =
      α (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (f : BruhatCompactTest (IdeleClass F)) :
    let f₀ := bruhatFiniteWeilPullback F v f
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * (idelicWeilCenteredTest F ν ω f).val 0) *
        (heckeConductorExponent F (heckeOrdinateCharacter F ω 0) v : ℂ) *
          (Real.log q : ℂ))
      (-((Real.log q / μ.real (finitePlaceIntegralUnits F v)) •
        ∫ u in finitePlaceIntegralUnits F v, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) •
          (f₀.val u - f₀.val 1) ∂μ)) := by
  obtain ⟨N, hN⟩ := idelicWeil_exists_congruence_invariance F v f
  let A (n : ℕ) := range (congruenceEmbedding F v n)
  let T := finitePlaceIntegralUnits F v
  let M := μ.real T
  let f₀ := bruhatFiniteWeilPullback F v f
  let g (u : L) := f₀.val u - f₀.val 1
  let b (n : ℕ) : ℂ := ∫ u : H F v n,
    f.val.val (finitePlaceInsertion F v u.val.val) ∂congruenceHaar F v n
  have h₁ : f₀.val 1 = f.val.val 1 := by
    change f.val.val (finitePlaceInsertion F v 1) = f.val.val 1
    exact congrArg f.val.val (map_one (finitePlaceInsertion F v))
  have hz : ∀ u ∈ A N, g u = 0 := by
    rintro _ ⟨a, rfl⟩
    change f.val.val (finitePlaceInsertion F v a.val.val) - f₀.val 1 = 0
    rw [h₁, sub_eq_zero]
    exact (congrArg f.val.val (mul_one _)).symm.trans (hN a 1)
  have ho (n : ℕ) : MeasurableSet (A n) :=
    (congruenceEmbedding_open F v n).isOpen_range.measurableSet
  have hT : MeasurableSet T := (localIntegralUnits_open F v).measurableSet
  have hsub (n : ℕ) : A n ⊆ T := by
    rintro _ ⟨a, rfl⟩
    exact (integralUnits_iff_norm F v a.val.val).mpr a.val.property
  have hgc : Continuous g := f₀.property.1.continuous.sub continuous_const
  have hgi : IntegrableOn g T μ :=
    hgc.continuousOn.integrableOn_compact (localIntegralUnits_compact F v)
  have hb (n : ℕ) : (∫ u : H F v n, g (congruenceEmbedding F v n u) ∂congruenceHaar F v n) =
      b n - f.val.val 1 := by
    haveI : IsProbabilityMeasure (congruenceHaar F v n) := ⟨congruenceHaar_univ F v n⟩
    have hc : Continuous (fun u : H F v n => f₀.val (congruenceEmbedding F v n u)) :=
      f₀.property.1.continuous.comp (congruenceEmbedding_open F v n).continuous
    change (∫ u : H F v n, f₀.val (congruenceEmbedding F v n u) - f₀.val 1 ∂congruenceHaar F v n) = _
    rw [integral_sub (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const _), integral_const, measureReal_def, congruenceHaar_univ,
      ENNReal.toReal_one, one_smul, h₁]
    rfl
  have he :
      (∫ u in T, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • g u ∂μ) =
        ∑ n ∈ Finset.range N, M • (b n - f.val.val 1) := by
    calc
      _ = ∫ u in T, ∑ n ∈ Finset.range N, congruenceWeight F v n • (A n).indicator g u ∂μ := by
        apply setIntegral_congr_fun hT
        intro u hu
        change (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • g u =
          ∑ n ∈ Finset.range N, congruenceWeight F v n • (A n).indicator g u
        rw [(integralUnits_iff_norm F v u).mp hu, Real.one_rpow, one_div, norm_sub_rev]
        exact ordinary_unit_weight_finite F v g N hz u hu
      _ = _ := by
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun n _ => ?_
          rw [integral_smul, setIntegral_indicator (ho n), inter_eq_right.mpr (hsub n),
            integral_congruence_eq_mean F v μ g n, hb n, smul_smul,
            congruenceWeight_mul_mass F v α μ hμ]
        · intro n _
          exact Integrable.smul (congruenceWeight F v n) (hgi.indicator (ho n))
  have hm : M ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(localIntegralUnits_open F v).measure_ne_zero μ ⟨1, one_mem _⟩,
      (localIntegralUnits_compact F v).measure_lt_top.ne⟩
  have h := (idelicWeil_conductorContact_hasSum_means F v ν f N hN).mul_right (Real.log q : ℂ)
  have hex : -((Real.log q / M) •
      ∫ u in T, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • g u ∂μ) =
      (∑ n ∈ Finset.range N, (f.val.val 1 - b n)) * (Real.log q : ℂ) := by
    rw [he, ← Finset.smul_sum, smul_smul, div_mul_cancel₀ _ hm, ← smul_neg, ← Finset.sum_neg_distrib]
    simp only [neg_sub, Complex.real_smul, mul_comm (Real.log q : ℂ)]
  change HasSum _ (-((Real.log q / M) •
      ∫ u in T, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) • g u ∂μ))
  rw [hex]
  exact h

end HaarMass

private theorem exists_finite_congruence_level_zero (f : BruhatCompactTest (IdeleClass F)) :
    ∃ S : Finset (Place F), ∀ w ∉ S, ∀ (a : H F w 0) (x : IdeleClass F),
      f.val.val (finitePlaceInsertion F w a.val.val * x) = f.val.val x := by
  obtain ⟨C, A, _, hA, hInv⟩ :=
    bruhatCompactTest_common_finite_stage F {f} (isVonNBounded_singleton f)
  have hmem := eventually_cofinite.mp
    (integralUnitFamilySingle_eventually_mem F (hA.mem_nhds A.one_mem))
  refine ⟨hmem.toFinset, fun w hw a x => ?_⟩
  have hu : integralUnitFamilySingle F w a.val ∈ A :=
    not_not.mp (fun h => hw (hmem.mem_toFinset.mpr h)) a.val
  have he := (hInv f (mem_singleton f)).2 x _ hu
  rw [integralUnitFamilySingle_class] at he
  exact (congrArg f.val.val (mul_comm _ _)).trans he

section Global

variable [∀ w : Place F, MeasurableSpace (w.adicCompletion F)]
  [∀ w : Place F, BorelSpace (w.adicCompletion F)]
  [∀ w : Place F, MeasurableSpace (w.adicCompletion F)ˣ]
  [∀ w : Place F, BorelSpace (w.adicCompletion F)ˣ]
  (α : ∀ w : Place F, Measure (w.adicCompletion F)) [∀ w, (α w).IsAddHaarMeasure]
  (η : ∀ w : Place F, Measure (w.adicCompletion F)ˣ) [∀ w, (η w).IsHaarMeasure]

omit [∀ w : Place F, MeasurableSpace (w.adicCompletion F)]
  [∀ w : Place F, BorelSpace (w.adicCompletion F)]
  [∀ w, (η w).IsHaarMeasure] in
/-- Only finitely many places contribute a subtracted unit integral
for a fixed compact idelic test. -/
theorem idelicWeil_unitCutoff_hasFiniteSupport (f : BruhatCompactTest (IdeleClass F)) :
    (fun w : Place F => (Real.log (w.asIdeal.absNorm : ℝ) /
          (η w).real (finitePlaceIntegralUnits F w)) •
        ∫ u in finitePlaceIntegralUnits F w, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) •
          ((bruhatFiniteWeilPullback F w f).val u -
            (bruhatFiniteWeilPullback F w f).val 1) ∂η w).HasFiniteSupport := by
  obtain ⟨S, hS⟩ := exists_finite_congruence_level_zero F f
  refine S.finite_toSet.subset fun w hw => ?_
  by_contra hn
  have h1 : (bruhatFiniteWeilPullback F w f).val 1 = f.val.val 1 :=
    congrArg f.val.val (map_one (finitePlaceInsertion F w))
  have h0 : (∫ u in finitePlaceIntegralUnits F w, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) •
      ((bruhatFiniteWeilPullback F w f).val u - (bruhatFiniteWeilPullback F w f).val 1) ∂η w) = 0 := by
    rw [← integral_zero (α := (w.adicCompletion F)ˣ) (μ := (η w).restrict _) (G := ℂ)]
    apply setIntegral_congr_fun (localIntegralUnits_open F w).measurableSet
    intro u hu
    have hu' : u ∈ range (congruenceEmbedding F w 0) := by
      rwa [congruenceEmbedding_range_zero]
    obtain ⟨a, rfl⟩ := hu'
    have he : (bruhatFiniteWeilPullback F w f).val (congruenceEmbedding F w 0 a) = f.val.val 1 :=
      (congrArg f.val.val (mul_one (finitePlaceInsertion F w a.val.val))).symm.trans (hS w hn a 1)
    simp only [he, h1, sub_self, smul_zero]
  exact hw (by simp only [h0, smul_zero])

/-- The full sum of the local conductor contacts equals the negative
of the unit contribution to the normalized finite-place cutoff. -/
theorem idelicWeil_conductorContact_hasSum
    (hη : ∀ w, η w (finitePlaceIntegralUnits F w) =
      α w (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
    (f : BruhatCompactTest (IdeleClass F)) :
    HasSum (fun ω : PontryaginDual (K F) =>
      ((ν.real univ : ℂ)⁻¹ * (idelicWeilCenteredTest F ν ω f).val 0) *
        (∑' w : Place F, (heckeConductorExponent F (heckeOrdinateCharacter F ω 0) w : ℂ) *
          (Real.log (w.asIdeal.absNorm : ℝ) : ℂ)))
      (-(∑' w : Place F, (Real.log (w.asIdeal.absNorm : ℝ) /
          (η w).real (finitePlaceIntegralUnits F w)) •
        ∫ u in finitePlaceIntegralUnits F w, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) •
          ((bruhatFiniteWeilPullback F w f).val u - (bruhatFiniteWeilPullback F w f).val 1) ∂η w)) := by
  obtain ⟨S, hS⟩ := exists_finite_congruence_level_zero F f
  let a (ω : PontryaginDual (K F)) :=
    (ν.real univ : ℂ)⁻¹ * (idelicWeilCenteredTest F ν ω f).val 0
  let c (ω : PontryaginDual (K F)) (w : Place F) :=
    (heckeConductorExponent F (heckeOrdinateCharacter F ω 0) w : ℂ) *
      (Real.log (w.asIdeal.absNorm : ℝ) : ℂ)
  let p (w : Place F) := (Real.log (w.asIdeal.absNorm : ℝ) /
      (η w).real (finitePlaceIntegralUnits F w)) •
    ∫ u in finitePlaceIntegralUnits F w, (‖u.val‖ ^ (1 / 2 : ℝ) / ‖1 - u.val‖ : ℝ) •
      ((bruhatFiniteWeilPullback F w f).val u - (bruhatFiniteWeilPullback F w f).val 1) ∂η w
  have hlocal (w : Place F) : HasSum (fun ω => a ω * c ω w) (-p w) := by
    have h := idelicWeil_conductorContact_hasSum_cutoff F w ν (α w) (η w) (hη w) f
    refine h.congr_fun fun ω => ?_
    change _ * (_ * _) = _ * _ * _
    ring
  have hzero (w : Place F) (hw : w ∉ S) (ω : PontryaginDual (K F)) : a ω * c ω w = 0 := by
    by_cases hc : heckeConductorExponent F (heckeOrdinateCharacter F ω 0) w ≤ 0
    · simp only [c, Nat.eq_zero_of_le_zero hc, Nat.cast_zero, zero_mul, mul_zero]
    · simp only [a, centeredTest_zero_of_congruence F w ν f 0 (hS w hw) ω hc, mul_zero, zero_mul]
  have hpzero (w : Place F) (hw : w ∉ S) : p w = 0 := by
    have h := (hlocal w).congr_fun (g := fun _ => (0 : ℂ)) (fun ω => (hzero w hw ω).symm)
    exact neg_eq_zero.mp (h.unique hasSum_zero)
  change HasSum (fun ω => a ω * ∑' w, c ω w) (-(∑' w, p w))
  rw [tsum_eq_sum hpzero, ← Finset.sum_neg_distrib]
  refine (hasSum_sum (s := S) (fun w _ => hlocal w)).congr_fun fun ω => ?_
  rw [← tsum_mul_left]
  exact tsum_eq_sum (fun w hw => hzero w hw ω)

end Global

end
end Masullo
