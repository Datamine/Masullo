import GlobalHeckeTateReflection
import ManuscriptHeckeCharacterChart
import PolynomialStrip
import Mathlib.Analysis.Complex.Liouville

open Asymptotics Filter Function Ideal IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

private abbrev atHeight := comap (abs ∘ Complex.im) atTop

private theorem inv_GammaC_add_isBigO_exp (a b : ℝ) (w : ℂ) :
    (fun z : ℂ ↦ (Complex.Gammaℂ (z + w))⁻¹) =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun z ↦ Real.exp (Real.pi * |z.im|) := by
  have h := (inv_Gammaℝ_add_isBigO_exp a b w).mul
    (inv_Gammaℝ_add_isBigO_exp a b (w + 1))
  refine h.congr' (.of_forall fun z ↦ ?_) (.of_forall fun z ↦ ?_)
  · dsimp only
    rw [← add_assoc, ← mul_inv, Complex.Gammaℝ_mul_Gammaℝ_add_one]
  · dsimp only
    rw [← Real.exp_add]
    congr 1
    ring

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}

variable (S : Finset (Place F)) (hS : Surjective (sIdeleClassInclusion F S))
variable (ω : PontryaginDual (K F))
variable (hω : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

/-- The actual reciprocal archimedean factor has at most exponential
growth on every fixed closed strip. -/
theorem completedTateReciprocalArch_isBigO_exp (lo hi : ℝ) :
    let k := (Fintype.card (R F) : ℝ) * (Real.pi / 2) + Fintype.card (C F) * Real.pi
    completedTateReciprocalArch F S hS ω hω =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc lo hi)]
      fun z ↦ Real.exp (k * |z.im|) := by
  intro k
  let p := sLocalNormOneCharacterOfGlobal F ω S hS hω
  let a := sLocalRealArchParameters F S p
  let j := sLocalComplexArchParameters F S p
  have hR (v : R F) :
      (fun z ↦ realArchZetaDenominator (a v).2 (z + (a v).1)) =O[
        atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc lo hi)] fun z ↦ Real.exp ((Real.pi / 2) * |z.im|) := by
    simpa only [realArchZetaDenominator, add_assoc] using
      (inv_Gammaℝ_add_isBigO_exp lo hi ((a v).1 + (((a v).2 % 2 : ℕ) : ℂ)))
  have hC (v : C F) :
      (fun z ↦ complexArchZetaDenominator (j v).2 (z + (j v).1)) =O[
        atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc lo hi)] fun z ↦ Real.exp (Real.pi * |z.im|) := by
    simpa only [complexArchZetaDenominator, add_assoc] using
      (inv_GammaC_add_isBigO_exp lo hi ((j v).1 + ((j v).2.natAbs : ℂ) / 2))
  have h := (Asymptotics.IsBigO.finsetProd (s := Finset.univ) (fun v _ ↦ hR v)).mul
    (Asymptotics.IsBigO.finsetProd (s := Finset.univ) (fun v _ ↦ hC v))
  refine h.congr' (.of_forall fun _ ↦ rfl) (.of_forall fun z ↦ ?_)
  simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, ← Real.exp_add, k]
  congr 1
  ring

private theorem norm_le_abs_height_add {a b : ℝ} {z : ℂ} (hz : z.re ∈ Icc a b) :
    ‖z‖ ≤ max |a| |b| + |z.im| := by
  have hre : |z.re| ≤ max |a| |b| :=
    abs_le.mpr ⟨(neg_le.mpr ((neg_le_abs a).trans (le_max_left _ _))).trans hz.1,
      hz.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hre le_rfl)

local instance finiteHeckeGrowthNormOneMeasurable : MeasurableSpace (K F) := borel _
local instance finiteHeckeGrowthNormOneBorel : BorelSpace (K F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]

/-- The pole-cleared finite Hecke reference is entire and has at most
exponential growth on every fixed closed strip. -/
theorem finiteClearedHeckeReference_exponential_strip
    (r : GlobalBruhat F) (B : ℂ) (a b : ℝ) :
    let g (z : ℂ) := completedTateReciprocalArch F S hS ω hω z *
      (B⁻¹ * globalHeckeClearedZeta F ν ω r z)
    let k := (Fintype.card (R F) : ℝ) * (Real.pi / 2) + Fintype.card (C F) * Real.pi + 2
    AnalyticOnNhd ℂ g univ ∧
      g =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z ↦ Real.exp (k * |z.im|) := by
  intro g k
  let E := atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)
  let R₀ := max |a| |b|
  obtain ⟨V, hV, hv⟩ := globalHeckeClearedZeta_strip_bound F ν ω r a b
  have hStrip : ∀ᶠ z : ℂ in E, z.re ∈ Icc a b :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ h ↦ h)
  have hP : (fun z ↦ B⁻¹ * globalHeckeClearedZeta F ν ω r z) =O[E]
      fun z ↦ Real.exp (2 * |z.im|) := by
    apply Asymptotics.IsBigO.of_bound (‖B⁻¹‖ * V * Real.exp (2 * R₀))
    filter_upwards [hStrip] with z hz
    have hpoly : 1 + ‖z‖ ^ 2 ≤ Real.exp (2 * ‖z‖) := by
      calc
        _ ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
        _ ≤ (Real.exp ‖z‖) ^ 2 := pow_le_pow_left₀ (by positivity)
          (by simpa only [add_comm] using Real.add_one_le_exp ‖z‖) _
        _ = _ := by rw [← Real.exp_nat_mul]; norm_num
    have hexp : Real.exp (2 * ‖z‖) ≤ Real.exp (2 * (R₀ + |z.im|)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (norm_le_abs_height_add hz) (by norm_num))
    simp only [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ ‖B⁻¹‖ * (V * Real.exp (2 * (R₀ + |z.im|))) :=
        mul_le_mul_of_nonneg_left ((hv z hz).trans (mul_le_mul_of_nonneg_left (hpoly.trans hexp) hV))
          (norm_nonneg _)
      _ = _ := by rw [mul_add, Real.exp_add]; ring
  refine ⟨fun z _ ↦ (archimedeanNumberFieldZetaDenominator_analytic _ _ _ _).mul
    (analyticAt_const.mul (globalHeckeClearedZeta_analytic F ν ω r z)), ?_⟩
  refine ((completedTateReciprocalArch_isBigO_exp F S hS ω hω a b).mul hP).congr'
    (.of_forall fun _ ↦ rfl) (.of_forall fun z ↦ ?_)
  dsimp only [k]
  rw [← Real.exp_add]
  congr 1
  ring

private theorem completedTateReciprocalArch_ne_zero {z : ℂ} (hz : 0 < z.re) :
    completedTateReciprocalArch F S hS ω hω z ≠ 0 := by
  apply archimedeanNumberFieldZetaDenominator_ne_zero_of_pos
  · intro v
    simpa only [Complex.add_re, sLocalRealArchParameters_re, add_zero] using hz
  · intro v
    simpa only [Complex.add_re, sLocalComplexArchParameters_re, add_zero] using hz

private theorem completedTateArch_bounded_right_strip {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖(completedTateReciprocalArch F S hS ω hω z)⁻¹‖ ≤ B := by
  let p := sLocalNormOneCharacterOfGlobal F ω S hS hω
  let r := sLocalRealArchParameters F S p
  let c := sLocalComplexArchParameters F S p
  have hr (v : R F) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖Complex.Gammaℝ (z + (r v).1 + (((r v).2 % 2 : ℕ) : ℂ))‖ ≤ M := by
    let k : ℕ := (r v).2 % 2
    obtain ⟨M, hM, h⟩ := exists_norm_GammaReal_le_on_strip (b := b + k) ha
    refine ⟨M, hM, fun z hz ↦ h _ ?_⟩
    simp only [Complex.add_re, show (r v).1.re = 0 from sLocalRealArchParameters_re F S p v,
      add_zero, Complex.natCast_re]
    exact ⟨by linarith [hz.1, Nat.cast_nonneg (α := ℝ) k], by linarith [hz.2]⟩
  have hc (v : C F) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖Complex.Gammaℂ (z + (c v).1 + ((c v).2.natAbs : ℂ) / 2)‖ ≤ M := by
    let k : ℕ := (c v).2.natAbs
    obtain ⟨M, hM, h⟩ := exists_norm_GammaComplex_le_on_strip (b := b + (k : ℝ) / 2) ha
    refine ⟨M, hM, fun z hz ↦ h _ ?_⟩
    simp only [Complex.add_re, show (c v).1.re = 0 from sLocalComplexArchParameters_re F S p v,
      add_zero, Complex.div_ofNat_re, Complex.natCast_re]
    exact ⟨by linarith [hz.1, Nat.cast_nonneg (α := ℝ) k], by linarith [hz.2]⟩
  choose A hA hR using hr
  choose B hB hC using hc
  refine ⟨(∏ v, A v) * ∏ v, B v, mul_nonneg
    (Finset.prod_nonneg fun v _ ↦ hA v) (Finset.prod_nonneg fun v _ ↦ hB v), fun z hz ↦ ?_⟩
  change ‖(archimedeanNumberFieldZetaDenominator F r c z)⁻¹‖ ≤ _
  simp only [archimedeanNumberFieldZetaDenominator, realArchZetaDenominator,
    complexArchZetaDenominator, mul_inv, Finset.prod_inv_distrib, inv_inv, norm_mul, norm_prod]
  exact mul_le_mul
    (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hR v z hz))
    (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hC v z hz))
    (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) (Finset.prod_nonneg fun v _ ↦ hA v)

/-- Sharp degree-dependent growth for the reflected archimedean ratio
on the strip needed for the left boundary of the convexity estimate. -/
theorem completedTateArchRatio_critical_left
    (hω' : globalNormOneCharacter F ω⁻¹ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, z.re ∈ Icc (-(1 / 2)) (1 / 2) →
      ‖completedTateReciprocalArch F S hS ω hω z *
        (completedTateReciprocalArch F S hS ω⁻¹ hω' (1 - z))⁻¹‖ ≤
          B * (1 + |z.im|) ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - z.re)) := by
  let D := completedTateReciprocalArch F S hS ω hω
  let E := completedTateReciprocalArch F S hS ω⁻¹ hω'
  let N (z : ℂ) := (E (1 - z))⁻¹
  let H (z : ℂ) := D z * N z
  let a : ℝ := -(1 / 2)
  let b : ℝ := 1 / 2
  let d := Module.finrank ℚ F
  let k := (Fintype.card (R F) : ℝ) * (Real.pi / 2) + Fintype.card (C F) * Real.pi
  have hab : a < b := by norm_num [a, b]
  have hReflect (z : ℂ) (hz : z.re ∈ Icc a b) : (1 - z).re ∈ Icc b (3 / 2) := by
    simp only [Complex.sub_re, Complex.one_re, mem_Icc]
    obtain ⟨hza, hzb⟩ := hz
    dsimp [a, b] at hza hzb ⊢
    exact ⟨by linarith, by linarith⟩
  have hAn (z : ℂ) (hz : z.re ∈ Icc a b) : AnalyticAt ℂ H z := by
    have hn : E (1 - z) ≠ 0 := completedTateReciprocalArch_ne_zero F S hS ω⁻¹ hω'
      ((by norm_num : 0 < b).trans_le (hReflect z hz).1)
    exact (archimedeanNumberFieldZetaDenominator_analytic _ _ _ _).mul
      (((archimedeanNumberFieldZetaDenominator_analytic _ _ _ _).comp
        (f := fun z : ℂ ↦ 1 - z) (analyticAt_const.sub analyticAt_id)).fun_inv hn)
  obtain ⟨A, _, hA⟩ :=
    completedTateArch_bounded_right_strip F S hS ω⁻¹ hω' (b := 3 / 2) (by norm_num : 0 < b)
  have hN : N =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
    apply Asymptotics.IsBigO.of_bound A
    apply eventually_inf_principal.mpr
    exact .of_forall fun z hz ↦ by simpa only [norm_one, mul_one] using hA _ (hReflect z hz)
  have hExp : H =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun z ↦ Real.exp (k * |z.im|) := by
    simpa only [H, mul_one] using (completedTateReciprocalArch_isBigO_exp F S hS ω hω a b).mul hN
  obtain ⟨L, T, hL, _, hLeft⟩ := completedTateArchRatio_half_integer F S hS ω hω hω' 1
  obtain ⟨U, V, hU, _, hRight⟩ := completedTateArchRatio_half_integer F S hS ω hω hω' 0
  have h₁ : VerticalPolynomialBound H a (d : ℝ) := by
    refine ⟨L * (3 / 2) ^ d, T, by positivity, fun y hy ↦ ?_⟩
    let z : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
    have hre : z.re = a := by simp [z, Complex.mul_re]
    have him : z.im = y := by simp [z, Complex.mul_im]
    have hs : z.re = 1 / 2 - ((1 : ℕ) : ℝ) := by rw [hre]; norm_num [a]
    have ho := hLeft z hs (by rwa [him])
    have hn := norm_le_abs_height_add (show z.re ∈ Icc a b from hre.symm ▸ left_mem_Icc.mpr hab.le)
    have hsize : 1 + ‖z‖ ≤ (3 / 2) * (1 + |y|) := by
      rw [him] at hn
      norm_num [a, b] at hn
      linarith [abs_nonneg y]
    rw [Real.rpow_natCast]
    change ‖H z‖ ≤ _
    calc
      _ ≤ L * (1 + ‖z‖) ^ d := by simpa only [Nat.mul_one] using ho
      _ ≤ L * ((3 / 2) * (1 + |y|)) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize _) hL
      _ = _ := by rw [mul_pow, mul_assoc]
  have h₂ : VerticalPolynomialBound H b 0 := by
    refine ⟨U, V, hU, fun y hy ↦ ?_⟩
    let z : ℂ := (b : ℂ) + (y : ℂ) * Complex.I
    have hre : z.re = b := by simp [z, Complex.mul_re]
    have him : z.im = y := by simp [z, Complex.mul_im]
    have hs : z.re = 1 / 2 - ((0 : ℕ) : ℝ) := by rw [hre]; norm_num [b]
    simpa only [Nat.mul_zero, pow_zero, Real.rpow_zero, mul_one] using
      hRight z hs (by rwa [him])
  obtain ⟨M, hM, hI⟩ := holomorphic_poly_interpolate_exp hab hAn (by dsimp [k]; positivity)
    hExp (Nat.cast_nonneg d) le_rfl h₁ h₂
  refine ⟨M, hM, fun z hz ↦ ?_⟩
  have hpow : (1 - (z.re - a) / (b - a)) * (d : ℝ) + (z.re - a) / (b - a) * 0 =
      (d : ℝ) * (1 / 2 - z.re) := by
    norm_num [a, b]
    ring
  simpa only [hpow] using hI z hz

private theorem completed_times_reciprocalArch_agrees {L : ℂ → ℂ}
    (he : EqOn L (globalCompletedHeckeEuler F ω S hS hω) {z | 1 < z.re}) :
    EqOn (completedTateReciprocalArch F S hS ω hω * L)
      (globalFiniteHeckeEuler F ω) {z | 1 < z.re} := by
  intro z hz
  let D := completedTateReciprocalArch F S hS ω hω
  change D z * L z = globalFiniteHeckeEuler F ω z
  rw [he hz]
  change D z * ((D z)⁻¹ * globalFiniteHeckeEuler F ω z) = _
  rw [← mul_assoc, mul_inv_cancel₀ (completedTateReciprocalArch_ne_zero F S hS ω hω
    (zero_lt_one.trans hz)), one_mul]

local instance finiteHeckeGrowthIdeleMeasurable : MeasurableSpace (Idele F) := borel _
local instance finiteHeckeGrowthIdeleBorel : BorelSpace (Idele F) := ⟨rfl⟩

variable (hω' : globalNormOneCharacter F ω⁻¹ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
variable (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))

include hS μ hν in
private theorem finiteEuler_analytic_right
    (χ : PontryaginDual (K F))
    (hχ : globalNormOneCharacter F χ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ (globalFiniteHeckeEuler F χ) z := by
  obtain ⟨L, _, he, ha, hp⟩ :=
    exists_globalCompletedHecke_analytic_or_simple_poles F χ S hS hχ η ν μ hν
  have hAn : AnalyticAt ℂ L z := by
    rcases eq_or_ne χ 1 with hχ₀ | hχ₀
    · apply (hp hχ₀).2.2
      · intro hz₀
        norm_num [hz₀] at hz
      · intro hz₁
        simp [hz₁] at hz
    · exact ha hχ₀ z (mem_univ z)
  have hD : AnalyticAt ℂ (completedTateReciprocalArch F S hS χ hχ) z :=
    archimedeanNumberFieldZetaDenominator_analytic _ _ _ _
  apply (hD.mul hAn).congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem hz] with w hw
  exact completed_times_reciprocalArch_agrees F S hS χ hχ he hw

private theorem reflect_punctured_growth (z : ℂ) :
    Tendsto (fun w : ℂ ↦ 1 - w) (𝓝[≠] z) (𝓝[≠] (1 - z)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact ((continuous_const.sub continuous_id).continuousAt (x := z)).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact fun h ↦ hw (sub_right_injective h)

set_option maxHeartbeats 500000 in
include hS hω hω' μ hν in
private theorem finiteHecke_left_norm_le_arch
    (hD : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (hfe : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (hfa : ∀ z, z.re < 0 → AnalyticAt ℂ f z) {a : ℝ} (ha : a < 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, z.re = a →
      ‖f z‖ ≤ B * ‖completedTateReciprocalArch F S hS ω hω z *
        (completedTateReciprocalArch F S hS ω⁻¹ hω' (1 - z))⁻¹‖ := by
  let D := completedTateReciprocalArch F S hS ω hω
  let D' := completedTateReciprocalArch F S hS ω⁻¹ hω'
  have hr : 1 < 1 - a := by linarith
  have hω'' : globalNormOneCharacter F (ω⁻¹)⁻¹ ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) := by
    rw [inv_inv]
    exact hω
  obtain ⟨U, W, ε, hU, hW, heU, heW, hε, _, hbound, hT⟩ :=
    exists_globalFiniteHecke_tateReflection F S hS ω⁻¹ hω' hω'' η ν μ hν hD
  have htransport (ψ : PontryaginDual (K F)) (hψ : ψ = ω)
      (h : globalNormOneCharacter F ψ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
      (W : ℂ → ℂ) (hW : MeromorphicOn W univ)
      (heW : EqOn W (globalFiniteHeckeEuler F ψ) {z | 1 < z.re}) (z : ℂ) :
      W =ᶠ[𝓝[≠] z] f := by
    subst ψ
    obtain ⟨L, hL, he, _, _⟩ :=
      exists_globalCompletedHecke_analytic_or_simple_poles F ω S hS hω η ν μ hν
    exact (globalFiniteHeckeContinuation_germ F ω S hS hω hL hW he heW z).trans
      (globalFiniteHeckeContinuation_germ F ω S hS hω hL hf he hfe z).symm
  have hArch {ψ : PontryaginDual (K F)} (hψ : ψ = ω)
      (h : globalNormOneCharacter F ψ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) :
      completedTateReciprocalArch F S hS ψ h = D := by subst ψ; rfl
  obtain ⟨B, hB, hb⟩ := hbound (1 - a) (by linarith)
  let C := ‖globalFiniteHeckeEuler F 1 ((1 - a : ℝ) : ℂ)‖
  refine ⟨C * B, by positivity, fun z hz ↦ ?_⟩
  have hzR : 1 < (1 - z).re := by simpa only [Complex.sub_re, Complex.one_re, hz] using hr
  have hn : D' (1 - z) ≠ 0 :=
    completedTateReciprocalArch_ne_zero F S hS ω⁻¹ hω' (zero_lt_one.trans hzR)
  let g (w : ℂ) := D' (1 - w) * f w
  let q (w : ℂ) := globalFiniteHeckeEuler F ω⁻¹ (1 - w) * D w * ε (1 - w)
  have hgel : g =ᶠ[𝓝[≠] z] q := by
    filter_upwards [(reflect_punctured_growth z).eventually (hT (1 - z)),
      htransport _ (inv_inv ω) hω'' W hW heW z,
      ((isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_const.sub continuous_id))).eventually_mem hzR).filter_mono nhdsWithin_le_nhds]
        with w hw hw' hwR
    change D' (1 - w) * W (1 - (1 - w)) =
      U (1 - w) * completedTateReciprocalArch F S hS (ω⁻¹)⁻¹ hω'' (1 - (1 - w)) *
        ε (1 - w) at hw
    have hEqU : U (1 - w) = globalFiniteHeckeEuler F ω⁻¹ (1 - w) := heU hwR
    simpa only [g, q, sub_sub_cancel, hw', hArch (inv_inv ω) hω'', hEqU] using hw
  have hsub : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z := analyticAt_const.sub analyticAt_id
  have hg : ContinuousAt g z :=
    (((archimedeanNumberFieldZetaDenominator_analytic _ _ _ _).comp hsub).mul
      (hfa z (hz ▸ ha))).continuousAt
  have hq : ContinuousAt q z :=
    ((((finiteEuler_analytic_right F S hS ν η μ hν ω⁻¹ hω' hzR).comp hsub).mul
      (archimedeanNumberFieldZetaDenominator_analytic _ _ _ z)).mul
      ((hε (1 - z) (mem_univ _)).comp hsub)).continuousAt
  have heq := ((hg.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hq).mp hgel).eq_of_nhds
  have hF : f z = globalFiniteHeckeEuler F ω⁻¹ (1 - z) * ε (1 - z) * (D z * (D' (1 - z))⁻¹) := by
    change D' (1 - z) * f z = globalFiniteHeckeEuler F ω⁻¹ (1 - z) * D z * ε (1 - z) at heq
    apply (mul_left_cancel₀ hn)
    rw [heq]
    field_simp
  have hfR : ‖globalFiniteHeckeEuler F ω⁻¹ (1 - z)‖ ≤ C :=
    globalFiniteHeckeEuler_bounded_right F ω⁻¹ hr (by simp [Complex.sub_re, hz])
  have hE : ‖ε (1 - z)‖ ≤ B := hb _ (by simp [Complex.sub_re, hz])
  rw [hF, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hfR hE (norm_nonneg _) (norm_nonneg _))
    (norm_nonneg _)

set_option maxHeartbeats 500000 in
include hS hω hω' μ hν in
/-- A finite Hecke continuation analytic on the left half-plane satisfies
polynomial bounds on every negative half-integer vertical line. -/
theorem finiteHecke_negative_half_integer_degree
    (hD : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (hfe : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (hfa : ∀ z, z.re < 0 → AnalyticAt ℂ f z) (k : ℕ) :
    VerticalPolynomialBound f (-(k : ℝ) - 1 / 2) (Module.finrank ℚ F * (k + 1) : ℕ) := by
  let a : ℝ := -(k : ℝ) - 1 / 2
  have ha : a < 0 := by dsimp only [a]; linarith [Nat.cast_nonneg (α := ℝ) k]
  let M := Module.finrank ℚ F * (k + 1)
  obtain ⟨A, T, hA, _, hgamma⟩ :=
    completedTateArchRatio_half_integer F S hS ω hω hω' (k + 1)
  obtain ⟨B, hB, hb⟩ := finiteHecke_left_norm_le_arch F S hS ω hω ν hω' η μ hν hD hf hfe hfa ha
  refine ⟨B * A * (1 + |a|) ^ M, T, by positivity, fun y hy ↦ ?_⟩
  let z : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have hz : z.re = a := by simp [z, Complex.add_re, Complex.mul_re]
  have hzIm : z.im = y := by simp [z, Complex.add_im, Complex.mul_im]
  have hσ : z.re = 1 / 2 - ((k + 1 : ℕ) : ℝ) := by
    rw [hz]; dsimp only [a]; push_cast; ring
  have hG := hgamma z hσ (hzIm ▸ hy)
  have hsize : 1 + ‖z‖ ≤ (1 + |a|) * (1 + |y|) := by
    have hx := Complex.norm_le_abs_re_add_abs_im z
    rw [hz, hzIm] at hx
    nlinarith [abs_nonneg a, abs_nonneg y]
  change ‖f z‖ ≤ _
  rw [Real.rpow_natCast]
  calc
    _ ≤ B * (A * (1 + ‖z‖) ^ M) := (hb z hz).trans (mul_le_mul_of_nonneg_left hG hB)
    _ ≤ B * (A * ((1 + |a|) * (1 + |y|)) ^ M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hsize _) hA) hB
    _ = _ := by rw [mul_pow]; ring

include hS hω hω' μ hν in
theorem finiteHecke_negative_half_integer_polynomial
    (hD : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (hfe : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (hfa : ∀ z, z.re < 0 → AnalyticAt ℂ f z) (k : ℕ) :
    ∃ M : ℕ, VerticalPolynomialBound f (-(k : ℝ) - 1 / 2) M :=
  ⟨_, finiteHecke_negative_half_integer_degree F S hS ω hω ν hω' η μ hν hD hf hfe hfa k⟩

set_option maxHeartbeats 500000 in
include hS hω hω' μ hν in
theorem finiteHecke_critical_left_polynomial
    (hD : ∀ v : Place F, v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    {f : ℂ → ℂ} (hf : MeromorphicOn f univ)
    (hfe : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re})
    (hfa : ∀ z, z.re < 0 → AnalyticAt ℂ f z) {a : ℝ} (hlo : -(1 / 2) ≤ a)
    (ha : a < 0) : VerticalPolynomialBound f a ((Module.finrank ℚ F : ℝ) * (1 / 2 - a)) := by
  obtain ⟨B, hB, hb⟩ := finiteHecke_left_norm_le_arch F S hS ω hω ν hω' η μ hν hD hf hfe hfa ha
  obtain ⟨C, hC, hc⟩ := completedTateArchRatio_critical_left F S hS ω hω hω'
  refine ⟨B * C, 0, mul_nonneg hB hC, fun y _ ↦ ?_⟩
  let z : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have hRe : z.re = a := by simp [z, Complex.add_re, Complex.mul_re]
  have hIm : z.im = y := by simp [z, Complex.add_im, Complex.mul_im]
  have hh := hc z (by rw [hRe]; exact ⟨hlo, by linarith⟩)
  rw [hRe, hIm] at hh
  change ‖f z‖ ≤ _
  simpa only [mul_assoc] using (hb z hRe).trans (mul_le_mul_of_nonneg_left hh hB)

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem pole_factor_norm_upper (z : ℂ) :
    ‖globalHeckePoleFactor F ω z‖ ≤ (1 + ‖z‖) ^ (if ω = 1 then 2 else 0 : ℕ) := by
  by_cases h : ω = 1
  · simp only [globalHeckePoleFactor, h, ite_true, norm_mul]
    have h' := norm_sub_le (1 : ℂ) z
    rw [norm_one] at h'
    exact (mul_le_mul_of_nonneg_left h' (norm_nonneg _)).trans
      (by nlinarith [norm_nonneg z])
  · simp only [globalHeckePoleFactor, h, ite_false, norm_one]
    simp

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem pole_factor_norm_lower {z : ℂ} (hz : 1 ≤ |z.im|) :
    (1 + |z.im|) ^ (if ω = 1 then 2 else 0 : ℕ) ≤ 4 * ‖globalHeckePoleFactor F ω z‖ := by
  by_cases h : ω = 1
  · simp only [globalHeckePoleFactor, h, ite_true, norm_mul]
    have h₀ := Complex.abs_im_le_norm z
    have h₁ : |z.im| ≤ ‖1 - z‖ := by
      apply le_trans ?_ (Complex.abs_im_le_norm (1 - z))
      simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, le_refl]
    rw [pow_two]
    have hm := mul_le_mul (by linarith : 1 + |z.im| ≤ 2 * ‖z‖)
      (by linarith : 1 + |z.im| ≤ 2 * ‖1 - z‖) (by positivity) (by positivity)
    exact hm.trans_eq (by ring)
  · norm_num [globalHeckePoleFactor, h]

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem cleared_line_polynomial {f g : ℂ → ℂ} {x k : ℝ}
    (hg : ∀ z, 1 ≤ |z.im| → g z = globalHeckePoleFactor F ω z * f z)
    (h : VerticalPolynomialBound f x k) :
    VerticalPolynomialBound g x (k + ((if ω = 1 then 2 else 0 : ℕ) : ℝ)) := by
  obtain ⟨C, T, hC, hb⟩ := h
  let m : ℕ := if ω = 1 then 2 else 0
  refine ⟨(1 + |x|) ^ m * C, max T 1, by positivity, fun y hy ↦ ?_⟩
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hre : z.re = x := by simp [z, Complex.mul_re, Complex.add_re]
  have him : z.im = y := by simp [z, Complex.mul_im, Complex.add_im]
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  rw [hre, him] at hnorm
  have hpoly : (1 + ‖z‖) ^ m ≤ (1 + |x|) ^ m * (1 + |y|) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg x, abs_nonneg y]) _
  change ‖g z‖ ≤ _
  rw [hg z (by simpa only [him] using (le_max_right T (1 : ℝ)).trans hy), norm_mul]
  calc
    _ ≤ ((1 + |x|) ^ m * (1 + |y|) ^ m) * (C * (1 + |y|) ^ k) :=
      mul_le_mul ((pole_factor_norm_upper F ω z).trans hpoly)
        (hb y ((le_max_left T (1 : ℝ)).trans hy)) (norm_nonneg _) (by positivity)
    _ = _ := by
      change _ = _ * (1 + |y|) ^ (k + (m : ℝ))
      rw [Real.rpow_add (by positivity), Real.rpow_natCast]
      ring

omit [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem finiteHecke_interpolate_cleared {f g : ℂ → ℂ} {a b K p q : ℝ}
    (hab : a < b) (hK : 0 ≤ K) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : AnalyticOnNhd ℂ g univ)
    (hExp : g =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun z ↦ Real.exp (K * |z.im|))
    (he : ∀ z, 1 ≤ |z.im| → g z = globalHeckePoleFactor F ω z * f z)
    (hL : VerticalPolynomialBound f a p) (hR : VerticalPolynomialBound f b q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| →
      ‖f z‖ ≤ B * (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) := by
  let m : ℕ := if ω = 1 then 2 else 0
  have h₁ := cleared_line_polynomial F ω he hL
  have h₂ := cleared_line_polynomial F ω he hR
  obtain ⟨B, hB, hI⟩ := holomorphic_poly_interpolate_exp hab (fun z _ ↦ ha z (mem_univ z))
    hK hExp (add_nonneg hp (Nat.cast_nonneg m)) (add_nonneg hq (Nat.cast_nonneg m)) h₁ h₂
  refine ⟨4 * B, by positivity, fun z hz ht ↦ ?_⟩
  let x := 1 + |z.im|
  let t := (z.re - a) / (b - a)
  let k := (1 - t) * p + t * q
  have hx : 0 < x := by dsimp [x]; positivity
  have hmul : ‖f z‖ * x ^ m ≤ 4 * ‖g z‖ := by
    rw [he z ht, norm_mul]
    calc
      _ ≤ ‖f z‖ * (4 * ‖globalHeckePoleFactor F ω z‖) :=
        mul_le_mul_of_nonneg_left (pole_factor_norm_lower F ω ht) (norm_nonneg _)
      _ = _ := by ring
  have hUpper := hI z hz
  change ‖g z‖ ≤ B * x ^ ((1 - t) * (p + (m : ℝ)) + t * (q + (m : ℝ))) at hUpper
  rw [show (1 - t) * (p + (m : ℝ)) + t * (q + (m : ℝ)) = k + (m : ℝ) by dsimp [k]; ring,
    Real.rpow_add hx, Real.rpow_natCast] at hUpper
  change ‖f z‖ ≤ 4 * B * x ^ k
  refine le_of_mul_le_mul_right (?_ : ‖f z‖ * x ^ m ≤ (4 * B * x ^ k) * x ^ m) (pow_pos hx _)
  calc
    ‖f z‖ * x ^ m ≤ 4 * ‖g z‖ := hmul
    _ ≤ 4 * (B * (x ^ k * x ^ m)) := mul_le_mul_of_nonneg_left hUpper (by norm_num)
    _ = (4 * B * x ^ k) * x ^ m := by ring

set_option maxHeartbeats 650000 in
include μ hν in
/-- Lemma B.1.1.2 in the canonical norm-one chart. A single continuation
has polynomial growth at large absolute heights on every fixed strip. -/
theorem exists_globalFiniteHecke_degree_polynomial_strips :
    ∃ f : ℂ → ℂ, MeromorphicOn f univ ∧
      EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      (∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ f z) ∧
      (∀ a b : ℝ, a < b → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
        ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N) ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : ℂ, z.re ∈ Icc 0 1 → 1 ≤ |z.im| →
          ‖f z‖ ≤ C * (1 + |z.im|) ^ ((Module.finrank ℚ F : ℝ) * ((1 + δ - z.re) / 2))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc (-6) 10 → 1 ≤ |z.im| →
        ‖f z‖ ≤ C * (1 + |z.im|) ^ (Module.finrank ℚ F * 7) := by
  obtain ⟨S, hs, hu, hu', hD⟩ := exists_globalHeckeTateStage F ω
  obtain ⟨r, L, hL, hm, _, _, ⟨B, hB, hscale⟩, _⟩ :=
    exists_globalCompletedHeckeContinuation F ω S hs hu η ν μ hν
  let D := completedTateReciprocalArch F S hs ω hu
  let f := D * L
  let G := globalZetaContinued F ν r (compactIdeleClassCharacter F ω) 0
  let g (z : ℂ) := D z * (B⁻¹ * globalHeckeClearedZeta F ν ω r z)
  have hLa (z : ℂ) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) : AnalyticAt ℂ L z := by
    have he : L = fun z ↦ B⁻¹ * G z := by
      funext z
      rw [show G z = B * L z from congrFun hscale z, ← mul_assoc, inv_mul_cancel₀ hB, one_mul]
    rw [he]
    exact analyticAt_const.mul
      (globalZetaContinued_analyticAt F ν r (compactIdeleClassCharacter F ω)
        (compactIdeleClassCharacter_unitary F ω) 0 z (by simpa using hz₀)
        (by simpa using sub_ne_zero.mpr hz₁))
  have hf : MeromorphicOn f univ := fun z hz ↦
    (archimedeanNumberFieldZetaDenominator_analytic _ _ _ _).meromorphicAt.mul (hm z hz)
  have he : EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re} :=
    completed_times_reciprocalArch_agrees F S hs ω hu hL
  have hfa (z : ℂ) (h₀ : z ≠ 0) (h₁ : z ≠ 1) : AnalyticAt ℂ f z :=
    (archimedeanNumberFieldZetaDenominator_analytic _ _ _ _).mul (hLa z h₀ h₁)
  have hfg (z : ℂ) (ht : 1 ≤ |z.im|) : g z = globalHeckePoleFactor F ω z * f z := by
    have hz₀ : z ≠ 0 := fun e ↦ by norm_num [e] at ht
    have hz₁ : z ≠ 1 := fun e ↦ by norm_num [e] at ht
    dsimp only [g]
    rw [globalHeckeClearedZeta_eq F ν ω r z hz₀ hz₁]
    change D z * (B⁻¹ * (globalHeckePoleFactor F ω z * G z)) =
      globalHeckePoleFactor F ω z * (D z * L z)
    rw [show G z = B * L z from congrFun hscale z]
    calc
      _ = (B⁻¹ * B) * (globalHeckePoleFactor F ω z * (D z * L z)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hB, one_mul]
  have hfLeft (z : ℂ) (hz : z.re < 0) : AnalyticAt ℂ f z :=
    hfa z (fun e ↦ by simp [e] at hz) (fun e ↦ by norm_num [e] at hz)
  have hRight (u : ℝ) (hu₀ : 1 < u) : VerticalPolynomialBound f u 0 := by
    refine ⟨‖globalFiniteHeckeEuler F 1 (u : ℂ)‖, 0, norm_nonneg _, fun y _ ↦ ?_⟩
    let z : ℂ := (u : ℂ) + (y : ℂ) * Complex.I
    have hre : z.re = u := by simp [z, Complex.add_re, Complex.mul_re]
    change ‖f z‖ ≤ _
    rw [he (show 1 < z.re by rwa [hre]), Real.rpow_zero, mul_one]
    exact globalFiniteHeckeEuler_bounded_right F ω hu₀ (le_of_eq hre.symm)
  have hInterp {l u p : ℝ} (hlu : l < u) (hu₀ : 1 < u) (hp : 0 ≤ p)
      (hLeft : VerticalPolynomialBound f l p) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, z.re ∈ Icc l u → 1 ≤ |z.im| →
        ‖f z‖ ≤ A * (1 + |z.im|) ^ ((1 - (z.re - l) / (u - l)) * p + (z.re - l) / (u - l) * 0) := by
    obtain ⟨hAn, hExp⟩ := finiteClearedHeckeReference_exponential_strip F S hs ω hu ν r B l u
    have hnon : 0 ≤ (Fintype.card (R F) : ℝ) * (Real.pi / 2) + Fintype.card (C F) * Real.pi + 2 :=
      by positivity
    exact finiteHecke_interpolate_cleared F ω hlu hnon hp le_rfl hAn hExp hfg hLeft (hRight u hu₀)
  have hDegree (k : ℕ) (u : ℝ) (hu₀ : 1 < u) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℂ, z.re ∈ Icc (-(k : ℝ) - 1 / 2) u → 1 ≤ |z.im| →
        ‖f z‖ ≤ A * (1 + |z.im|) ^ (Module.finrank ℚ F * (k + 1)) := by
    let l := -(k : ℝ) - 1 / 2
    let M := Module.finrank ℚ F * (k + 1)
    have hlu : l < u := by dsimp [l]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hLeft := finiteHecke_negative_half_integer_degree
      F S hs ω hu ν hu' η μ hν hD hf he hfLeft k
    obtain ⟨A, hA, hI⟩ := hInterp hlu hu₀ (Nat.cast_nonneg M) hLeft
    refine ⟨A, hA, fun z hz ht ↦ (hI z hz ht).trans (mul_le_mul_of_nonneg_left ?_ hA)⟩
    change _ ≤ (1 + |z.im|) ^ M
    rw [← Real.rpow_natCast _ M]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im])
    have ht' : 0 ≤ (z.re - l) / (u - l) :=
      div_nonneg (sub_nonneg.mpr hz.1) (sub_pos.mpr hlu).le
    nlinarith [mul_nonneg ht' (Nat.cast_nonneg (α := ℝ) M)]
  refine ⟨f, hf, he, hfa, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨k, hk⟩ := exists_nat_gt (-a)
    let l : ℝ := -(k : ℝ) - 1 / 2
    let u : ℝ := max 2 b
    have hl : l < a := by dsimp only [l]; linarith
    have hu₀ : 1 < u := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_left _ _)
    obtain ⟨A, hA, hI⟩ := hDegree k u hu₀
    exact ⟨A, _, hA, fun z hz ht ↦ hI z ⟨hl.le.trans hz.1, hz.2.trans (le_max_right _ _)⟩ ht⟩
  · intro δ hδ hδmax
    let l := -δ
    let u := 1 + δ
    let d : ℝ := Module.finrank ℚ F
    have hl : l < 0 := neg_lt_zero.mpr hδ
    have hu₀ : 1 < u := by dsimp [u]; linarith
    have hlu : l < u := hl.trans (zero_lt_one.trans hu₀)
    have hLeft := finiteHecke_critical_left_polynomial F S hs ω hu ν hu' η μ hν hD hf he hfLeft
      (show -(1 / 2) ≤ l by dsimp [l]; linarith) hl
    obtain ⟨A, hA, hI⟩ := hInterp hlu hu₀
      (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hLeft
    refine ⟨A, hA, fun z hz ht ↦ ?_⟩
    have hz' : z.re ∈ Icc l u := ⟨hl.le.trans hz.1, hz.2.trans hu₀.le⟩
    have hpow : (1 - (z.re - l) / (u - l)) * (d * (1 / 2 - l)) + (z.re - l) / (u - l) * 0 =
        d * ((1 + δ - z.re) / 2) := by
      have hw : u - l ≠ 0 := (sub_pos.mpr hlu).ne'
      rw [mul_zero, add_zero]
      field_simp
      dsimp [l, u]
      ring
    have hi := hI z hz' ht
    rw [hpow] at hi
    exact hi
  · obtain ⟨A, hA, hI⟩ := hDegree 6 10 (by norm_num)
    refine ⟨A, hA, fun z hz ht ↦ ?_⟩
    exact hI z ⟨(by norm_num : -(↑(6 : ℕ) : ℝ) - 1 / 2 ≤ -6).trans hz.1, hz.2⟩ ht

include μ hν in
/-- Polynomial growth and the critical-strip interpolation in the norm-one chart. -/
theorem exists_globalFiniteHecke_polynomial_strips :
    ∃ f : ℂ → ℂ, MeromorphicOn f univ ∧
      EqOn f (globalFiniteHeckeEuler F ω) {z | 1 < z.re} ∧
      (∀ z, z ≠ 0 → z ≠ 1 → AnalyticAt ℂ f z) ∧
      (∀ a b : ℝ, a < b → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
        ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z : ℂ, z.re ∈ Icc 0 1 → 1 ≤ |z.im| →
          ‖f z‖ ≤ C * (1 + |z.im|) ^ ((Module.finrank ℚ F : ℝ) * ((1 + δ - z.re) / 2)) := by
  obtain ⟨f, hf, he, hfa, hpoly, hcrit, _⟩ :=
    exists_globalFiniteHecke_degree_polynomial_strips F ω ν η μ hν
  exact ⟨f, hf, he, hfa, hpoly, hcrit⟩

include μ hν in
/-- Lemma B.1.1.2 for arbitrary unitary idele-class characters. The exponent
is allowed to depend on the fixed strip, as well as on the character. -/
theorem exists_manuscriptFiniteHecke_polynomial_strips (χ : PontryaginDual (IdeleClass F)) :
    ∃ (f : ℂ → ℂ) (t : ℝ), HasHeckeHeight F χ t ∧ MeromorphicOn f univ ∧
      EqOn f (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      (∀ z, z ≠ (t : ℂ) * Complex.I → z ≠ 1 + (t : ℂ) * Complex.I → AnalyticAt ℂ f z) ∧
      ∀ a b : ℝ, a < b → ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
        ∀ z : ℂ, z.re ∈ Icc a b → 1 + |t| ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  obtain ⟨L, hm, he, ha, hg, _⟩ :=
    exists_globalFiniteHecke_polynomial_strips F (heckeNormOneRestriction F χ) ν η μ hν
  let u : ℂ := (t : ℂ) * Complex.I
  let q (z : ℂ) := z - u
  have hq (z : ℂ) : AnalyticAt ℂ q z := analyticAt_id.sub analyticAt_const
  have hre (z : ℂ) : (q z).re = z.re := by simp [q, u, Complex.sub_re, Complex.mul_re]
  have him (z : ℂ) : (q z).im = z.im - t := by simp [q, u, Complex.sub_im, Complex.mul_im]
  refine ⟨L ∘ q, t, ht, fun z _ ↦ (hm (q z) (mem_univ _)).comp_analyticAt (hq z),
    fun z hz ↦ ?_, fun z h₀ h₁ ↦ ?_, fun a b hab ↦ ?_⟩
  · rw [manuscriptFiniteHeckeEuler_shift F χ ht]
    exact he (show 1 < (q z).re by rwa [hre])
  · have hL : AnalyticAt ℂ L (q z) :=
      ha _ (fun e ↦ h₀ (sub_eq_zero.mp e)) (fun e ↦ h₁ (sub_eq_iff_eq_add.mp e))
    exact hL.comp (f := q) (hq z)
  · obtain ⟨C, N, hC, hG⟩ := hg a b hab
    refine ⟨C * (1 + |t|) ^ N, N, by positivity, fun z hz hT ↦ ?_⟩
    have h₁ : 1 ≤ |(q z).im| := by
      rw [him]
      linarith [abs_sub_abs_le_abs_sub z.im t]
    have h₂ : 1 + |(q z).im| ≤ (1 + |t|) * (1 + |z.im|) := by
      rw [him]
      nlinarith [abs_sub z.im t, abs_nonneg z.im, abs_nonneg t]
    change ‖L (q z)‖ ≤ _
    calc
      _ ≤ C * (1 + |(q z).im|) ^ N := hG _ (by rwa [hre]) h₁
      _ ≤ C * ((1 + |t|) * (1 + |z.im|)) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h₂ _) hC
      _ = _ := by rw [mul_pow, mul_assoc]

set_option maxHeartbeats 500000 in
include μ hν in
/-- Proposition B.1.1.3 for arbitrary unitary idele-class characters.
The height threshold may depend on ε. The bound holds with constant one
by reserving part of ε to absorb the constants at sufficiently large height. -/
theorem exists_manuscriptFiniteHecke_convexity (χ : PontryaginDual (IdeleClass F)) :
    ∃ f : ℂ → ℂ, MeromorphicOn f univ ∧
      EqOn f (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc 0 1 → T ≤ |z.im| →
        ‖f z‖ ≤ |z.im| ^ ((Module.finrank ℚ F : ℝ) * ((1 - z.re) / 2) + ε) := by
  obtain ⟨t, ht, _⟩ := existsUnique_heckeHeight F χ
  obtain ⟨L, hm, he, _, _, hconv⟩ :=
    exists_globalFiniteHecke_polynomial_strips F (heckeNormOneRestriction F χ) ν η μ hν
  let q (z : ℂ) := z - (t : ℂ) * Complex.I
  have hre (z : ℂ) : (q z).re = z.re := by simp [q, Complex.sub_re, Complex.mul_re]
  have him (z : ℂ) : (q z).im = z.im - t := by simp [q, Complex.sub_im, Complex.mul_im]
  refine ⟨L ∘ q, fun z _ ↦ (hm (q z) (mem_univ _)).comp_analyticAt
    (g := q) (analyticAt_id.sub analyticAt_const), ?_, ?_⟩
  · intro z hz
    rw [manuscriptFiniteHeckeEuler_shift F χ ht]
    exact he (show 1 < (q z).re by rwa [hre])
  · intro ε hε
    let d : ℝ := Module.finrank ℚ F
    let δ := min (1 / 2) (ε / (d + 1))
    have hd : 0 ≤ d := Nat.cast_nonneg _
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
    have hδmax : δ ≤ 1 / 2 := min_le_left _ _
    have hdδ : d * δ ≤ ε := by
      have hh := (le_div_iff₀ (by positivity : 0 < d + 1)).mp (min_le_right (1 / 2) (ε / (d + 1)))
      nlinarith
    obtain ⟨A, hA, hI⟩ := hconv δ hδ hδmax
    let K : ℝ := 2 + |t|
    have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg t]
    obtain ⟨V, hV⟩ := eventually_atTop.mp
      ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).eventually_ge_atTop (A * K ^ (d + ε)))
    refine ⟨max (1 + |t|) V, fun z hz hT ↦ ?_⟩
    have ht₀ : 1 + |t| ≤ |z.im| := (le_max_left _ _).trans hT
    have ht₁ : 1 ≤ |z.im| := by linarith [abs_nonneg t]
    have hheight : 1 ≤ |(q z).im| := by
      rw [him]
      linarith [abs_sub_abs_le_abs_sub z.im t]
    have hsize : 1 + |(q z).im| ≤ K * |z.im| := by
      rw [him]
      dsimp [K]
      nlinarith [abs_sub z.im t, mul_nonneg (abs_nonneg t) (sub_nonneg.mpr ht₁)]
    let p := d * ((1 + δ - z.re) / 2)
    let r := d * ((1 - z.re) / 2)
    have hp : 0 ≤ p := by dsimp [p]; exact mul_nonneg hd (by linarith [hz.2])
    have hpr : p ≤ r + ε / 2 := by dsimp [p, r]; linarith only [hdδ]
    have hpd : p ≤ d + ε := by
      have hr : r ≤ d := by dsimp [r]; exact mul_le_of_le_one_right hd (by linarith [hz.1])
      linarith
    have hL := hI (q z) (by rwa [hre]) hheight
    rw [hre] at hL
    change ‖L (q z)‖ ≤ |z.im| ^ (r + ε)
    calc
      _ ≤ A * (1 + |(q z).im|) ^ p := hL
      _ ≤ A * (K * |z.im|) ^ p :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hsize hp) hA
      _ = (A * K ^ p) * |z.im| ^ p := by
        rw [Real.mul_rpow (zero_le_one.trans hK) (abs_nonneg _), mul_assoc]
      _ ≤ (A * K ^ (d + ε)) * |z.im| ^ p :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hK hpd) hA) (by positivity)
      _ ≤ |z.im| ^ (ε / 2) * |z.im| ^ p :=
        mul_le_mul_of_nonneg_right (hV _ ((le_max_right _ _).trans hT)) (by positivity)
      _ = |z.im| ^ (ε / 2 + p) := by rw [Real.rpow_add (zero_lt_one.trans_le ht₁)]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht₁ (by linarith)

open Metric in
/-- Cauchy's estimate transports polynomial growth at large heights to
each derivative on an interior strip. -/
theorem iteratedDeriv_polynomial_strip {f : ℂ → ℂ} {a b T : ℝ}
    (ha : ∀ z : ℂ, T ≤ |z.im| → AnalyticAt ℂ f z)
    (hp : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      ∀ z : ℂ, z.re ∈ Icc (a - 1) (b + 1) → T ≤ |z.im| → ‖f z‖ ≤ C * (1 + |z.im|) ^ N)
    (n : ℕ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → 1 + T ≤ |z.im| →
      ‖iteratedDeriv n f z‖ ≤ C * (1 + |z.im|) ^ N := by
  obtain ⟨C, N, hC, hP⟩ := hp
  refine ⟨n.factorial * (C * 2 ^ N), N, by positivity, fun z hz ht ↦ ?_⟩
  have hdisk (w : ℂ) (hw : w ∈ closedBall z 1) :
      w.re ∈ Icc (a - 1) (b + 1) ∧ T ≤ |w.im| := by
    have hdist := mem_closedBall_iff_norm.mp hw
    have hr : |w.re - z.re| ≤ 1 := by
      simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (w - z)).trans hdist
    have hi : |w.im - z.im| ≤ 1 := by
      simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (w - z)).trans hdist
    rw [abs_sub_comm] at hi
    exact ⟨⟨by linarith [hz.1, (abs_le.mp hr).1], by linarith [hz.2, (abs_le.mp hr).2]⟩,
      by linarith [(abs_sub_abs_le_abs_sub z.im w.im).trans hi]⟩
  have hAn : AnalyticOnNhd ℂ f (closedBall z 1) :=
    fun w hw ↦ ha w (hdisk w hw).2
  have hdiff : DiffContOnCl ℂ f (ball z 1) := by
    refine ⟨fun w hw ↦ (hAn w (ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt, ?_⟩
    rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
    exact hAn.continuousOn
  have hSphere (w : ℂ) (hw : w ∈ sphere z 1) :
      ‖f w‖ ≤ C * (2 * (1 + |z.im|)) ^ N := by
    obtain ⟨hr, hi⟩ := hdisk w (sphere_subset_closedBall hw)
    have hd : |w.im - z.im| ≤ 1 := by
      simpa only [Complex.sub_im, mem_sphere_iff_norm.mp hw] using Complex.abs_im_le_norm (w - z)
    have hsize : 1 + |w.im| ≤ 2 * (1 + |z.im|) := by
      linarith [(abs_sub_abs_le_abs_sub w.im z.im).trans hd, abs_nonneg z.im]
    exact (hP _ hr hi).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hsize _) hC)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n zero_lt_one hdiff hSphere
  simpa only [one_pow, div_one, mul_pow, ← mul_assoc] using h

include μ hν in
/-- Remark B.1.1.4 with a Cauchy estimate on a wider strip. All derivatives
of the same finite continuation have polynomial growth on fixed strips. -/
theorem exists_manuscriptFiniteHecke_derivative_polynomial_strips
    (χ : PontryaginDual (IdeleClass F)) :
    ∃ f : ℂ → ℂ, MeromorphicOn f univ ∧
      EqOn f (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      ∀ a b : ℝ, a < b → ∀ n : ℕ, ∃ (C T : ℝ) (N : ℕ), 0 ≤ C ∧
        ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| →
          ‖iteratedDeriv n f z‖ ≤ C * (1 + |z.im|) ^ N := by
  obtain ⟨f, t, _, hm, he, ha, hp⟩ :=
    exists_manuscriptFiniteHecke_polynomial_strips F ν η μ hν χ
  refine ⟨f, hm, he, fun a b hab n ↦ ?_⟩
  have hAn (z : ℂ) (hz : 1 + |t| ≤ |z.im|) : AnalyticAt ℂ f z := by
    apply ha z <;> intro e
    · have hi := congrArg Complex.im e
      simp [Complex.mul_im] at hi
      rw [hi] at hz
      linarith
    · have hi := congrArg Complex.im e
      simp [Complex.add_im, Complex.mul_im] at hi
      rw [hi] at hz
      linarith
  obtain ⟨C, N, hC, h⟩ := iteratedDeriv_polynomial_strip hAn (hp (a - 1) (b + 1) (by linarith)) n
  exact ⟨C, 1 + (1 + |t|), N, hC, h⟩

/-- The corrected differentiated reflection in (B.1.1.15). Each derivative
falling on the reflected factor (L(1-z)) contributes a minus sign. -/
theorem iteratedDeriv_reflected_mul {W L : ℂ → ℂ} {z : ℂ}
    (hW : AnalyticAt ℂ W z) (hL : AnalyticAt ℂ L (1 - z)) (n : ℕ) :
    iteratedDeriv n (fun s ↦ W s * L (1 - s)) z =
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i W z *
          ((-1 : ℂ) ^ (n - i) * iteratedDeriv (n - i) L (1 - z)) := by
  have hR : AnalyticAt ℂ (fun s : ℂ ↦ L (1 - s)) z :=
    hL.comp (f := fun s : ℂ ↦ 1 - s) (analyticAt_const.sub analyticAt_id)
  rw [iteratedDeriv_fun_mul hW.contDiffAt hR.contDiffAt]
  simp_rw [iteratedDeriv_comp_const_sub, smul_eq_mul]

end

end Masullo
