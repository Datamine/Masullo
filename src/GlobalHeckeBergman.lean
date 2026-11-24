import GlobalMellinPadding
import BergmanDivisorInterpolation
import ExponentialDecayStructure

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ENat NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Bergman := SchwartzBergman (univ : Set ℝ)

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure]
variable (ω : PontryaginDual (K F)) (f : GlobalBruhat F)

private abbrev χ := compactIdeleClassCharacter F ω

private abbrev radialProfile (t : ℝ) : ℂ :=
  adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val
    (ideleClassExpSection F (Multiplicative.ofAdd t))

private theorem radialProfile_mem
    (hf : globalZetaPolarVanishes F f (χ F ω)) :
    radialProfile F ν ω f ∈ logExponentialDecaySubmodule univ := by
  have hv := (globalZetaPolarVanishes_compact_iff F f ω).mp hf
  apply (logExponentialDecay_mem_iff_twoSided _).mpr
  refine ⟨⟨adelicHomogeneousTheta_radialSchwartz F ν ω f hv, rfl⟩, ?_⟩
  apply (logDerivativesRapid_twoSided_iff _).mpr
  intro n a _
  obtain ⟨N, hN⟩ := exists_nat_gt a
  obtain ⟨C, hC, hdecay⟩ := adelicHomogeneousTheta_radial_derivative_decay F ν ω {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f) n N
  refine ⟨C, hC.le, fun t => (hdecay f (mem_singleton _) hv t).trans ?_⟩
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hC.le
  exact mul_le_mul_of_nonneg_right (neg_le_neg hN.le) (abs_nonneg t)

/-- The homogeneous theta profile on the canonical norm section as an
entire exponential-decay test. -/
def globalPoleFreeRadialProfile
    (hf : globalZetaPolarVanishes F f (χ F ω)) :
    PositiveRealExponentialDecay (univ : Set ℝ) :=
  ⟨radialProfile F ν ω f, radialProfile_mem F ν ω f hf⟩

/-- The entire Mellin transform of the actual homogeneous theta profile
is the pole-free continuation of the global zeta integral. -/
theorem globalPoleFreeRadialProfile_mellin
    (hf : globalZetaPolarVanishes F f (χ F ω)) :
    (positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
      (globalPoleFreeRadialProfile F ν ω f hf)).val = globalZetaContinued F ν f (χ F ω) 0 := by
  let u := globalPoleFreeRadialProfile F ν ω f hf
  funext z
  change (positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty u).val z = _
  rw [positiveRealFourierMellin_apply _ _ _ _ _ _ (mem_univ _), mellin_eq_log_integral]
  have he := globalRadialZeta_eq_continued F ν f (χ F ω)
    (compactIdeleClassCharacter_unitary F ω) (κ := 0) Complex.zero_re
    (fun t => by simp [χ]) (ideleClassExpSection F) (fun t => ideleClassNorm_expSection F _)
    z (Or.inr hf)
  rw [← he]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  rw [globalRadialZetaIntegrand_canonical, compactIdeleClassCharacter_apply_ray,
    normOnePontryaginCharacter_compactIdeleClassCharacter, one_mul]
  change Complex.exp (z * (t : ℂ)) * radialProfile F ν ω f (Real.log (Real.exp t)) = _
  rw [Real.log_exp]

/-- The actual pole-free global zeta transform lies in the entire
Schwartz–Bergman space. -/
theorem globalZetaContinued_mem_schwartzBergman
    (hf : globalZetaPolarVanishes F f (χ F ω)) :
    globalZetaContinued F ν f (χ F ω) 0 ∈ schwartzBergmanSubmodule univ :=
  globalPoleFreeRadialProfile_mellin F ν ω f hf ▸
    (positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
      (globalPoleFreeRadialProfile F ν ω f hf)).property

private def upperSum (z : ℂ) : ℂ :=
  thetaZetaUpper F ν f (χ F ω) z +
    thetaZetaUpper F ν (GlobalBruhat.fourier F f) (χ F ω)⁻¹ (1 - z)

private theorem upperSum_analytic (z : ℂ) : AnalyticAt ℂ (upperSum F ν ω f) z := by
  have hunit := compactIdeleClassCharacter_unitary F ω
  have hinv : IsUnitary F (χ F ω)⁻¹ := fun q => by
    change ‖((χ F ω q)⁻¹ : ℂˣ).val‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, hunit, inv_one]
  have h₁ := (thetaZetaUpper_integrable_analytic F ν f (χ F ω) hunit).2 z trivial
  have h₂ := (thetaZetaUpper_integrable_analytic F ν (GlobalBruhat.fourier F f)
    (χ F ω)⁻¹ hinv).2 (1-z) trivial
  exact h₁.add (h₂.comp (analyticAt_const.sub analyticAt_id))

private def constantTerm : ℂ :=
  (ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F f).val 0

private def fourierConstantTerm : ℂ :=
  (ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0

/-- The two-pole clearing factor in the canonical compact-character chart. -/
def globalHeckePoleFactor : ℂ → ℂ := if ω = 1 then fun z => z * (1 - z) else fun _ => 1

theorem globalHeckePoleFactor_analytic (c : ℂ) :
    AnalyticAt ℂ (globalHeckePoleFactor F ω) c := by
  by_cases hω : ω = 1
  · rw [globalHeckePoleFactor, ite_eq_left hω]
    have h : AnalyticAt ℂ (fun z : ℂ => 1 - z) c := analyticAt_const.sub analyticAt_id
    exact analyticAt_id.mul h
  · simpa only [globalHeckePoleFactor, ite_eq_right hω] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) c)

/-- The entire extension of the pole-cleared global zeta integral of an
actual adelic test. The formula also specifies the values at the deleted poles. -/
def globalHeckeClearedZeta : ℂ → ℂ :=
  if ω = 1 then
    fun z => z * (1 - z) * upperSum F ν ω f z - fourierConstantTerm F ν f * z -
      constantTerm F ν f * (1 - z)
  else upperSum F ν ω f

omit [ν.IsHaarMeasure] in
@[simp] theorem globalHeckeClearedZeta_trivial_zero :
    globalHeckeClearedZeta F ν 1 f 0 =
      -((ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F f).val 0) := by
  simp [globalHeckeClearedZeta, constantTerm]

omit [ν.IsHaarMeasure] in
@[simp] theorem globalHeckeClearedZeta_trivial_one :
    globalHeckeClearedZeta F ν 1 f 1 =
      -((ν.real univ : ℂ) * (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0) := by
  simp [globalHeckeClearedZeta, fourierConstantTerm]

theorem globalHeckeClearedZeta_analytic (z : ℂ) :
    AnalyticAt ℂ (globalHeckeClearedZeta F ν ω f) z := by
  by_cases hω : ω = 1
  · rw [globalHeckeClearedZeta, ite_eq_left hω]
    have h : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := analyticAt_const.sub analyticAt_id
    exact (((analyticAt_id.mul h).mul (upperSum_analytic F ν ω f z)).sub
      (analyticAt_const.mul analyticAt_id)).sub (analyticAt_const.mul h)
  · rw [globalHeckeClearedZeta, ite_eq_right hω]
    exact upperSum_analytic F ν ω f z

theorem globalHeckeClearedZeta_eq (z : ℂ) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) :
    globalHeckeClearedZeta F ν ω f z =
      globalHeckePoleFactor F ω z * globalZetaContinued F ν f (χ F ω) 0 z := by
  have h : 1 - z ≠ 0 := sub_ne_zero.mpr hz₁.symm
  by_cases hω : ω = 1
  · simp only [globalHeckeClearedZeta, globalHeckePoleFactor, globalZetaContinued, upperSum,
      fourierConstantTerm, constantTerm, χ, compactIdeleClassCharacter_integral, hω, ite_true,
      add_zero]
    field_simp
    ring
  · simp only [globalHeckeClearedZeta, globalHeckePoleFactor, globalZetaContinued, upperSum, χ,
      compactIdeleClassCharacter_integral F ν ω, ite_eq_right hω, zero_mul, zero_div,
      add_zero, sub_zero, one_mul]

private theorem upperSum_strip_bound (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖upperSum F ν ω f z‖ ≤ C := by
  have hunit := compactIdeleClassCharacter_unitary F ω
  have hinv : IsUnitary F (χ F ω)⁻¹ := fun q => by
    change ‖((χ F ω q)⁻¹ : ℂˣ).val‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, hunit, inv_one]
  obtain ⟨p, _, hp⟩ := thetaZetaUpper_seminorm_bound F ν (χ F ω) hunit b
  obtain ⟨q, _, hq⟩ := thetaZetaUpper_seminorm_bound F ν (χ F ω)⁻¹ hinv (1-a)
  refine ⟨p f + q (GlobalBruhat.fourier F f), add_nonneg (apply_nonneg p _) (apply_nonneg q _),
    fun z hz => (norm_add_le _ _).trans ?_⟩
  exact add_le_add (hp _ _ hz.2) (hq _ _ (by simpa using sub_le_sub_left hz.1 1))

theorem globalHeckeClearedZeta_strip_bound (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖globalHeckeClearedZeta F ν ω f z‖ ≤ C * (1 + ‖z‖ ^ 2) := by
  obtain ⟨A, hA, hupper⟩ := upperSum_strip_bound F ν ω f a b
  let B := ‖fourierConstantTerm F ν f‖
  let D := ‖constantTerm F ν f‖
  refine ⟨2 * (A + B + D), by dsimp [B, D]; positivity, fun z hz => ?_⟩
  have hz₀ : 0 ≤ ‖z‖ := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hD : 0 ≤ D := norm_nonneg _
  have hlin : 1 + ‖z‖ ≤ 2 * (1 + ‖z‖ ^ 2) := by nlinarith [sq_nonneg (‖z‖ - 1)]
  have hquad : ‖z‖ * (1 + ‖z‖) ≤ 2 * (1 + ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have hsub : ‖1 - z‖ ≤ 1 + ‖z‖ := by simpa using norm_sub_le (1 : ℂ) z
  by_cases hω : ω = 1
  · rw [globalHeckeClearedZeta, ite_eq_left hω]
    calc
      _ ≤ ‖z * (1-z) * upperSum F ν ω f z‖ +
          ‖fourierConstantTerm F ν f * z‖ + ‖constantTerm F ν f * (1-z)‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ (‖z‖ * (1 + ‖z‖)) * A + B * (1 + ‖z‖) + D * (1 + ‖z‖) := by
        simp only [norm_mul]
        gcongr
        · exact hupper z hz
        · linarith
      _ ≤ (2 * (1 + ‖z‖ ^ 2)) * A + B * (2 * (1 + ‖z‖ ^ 2)) +
          D * (2 * (1 + ‖z‖ ^ 2)) := by gcongr
      _ = _ := by ring
  · rw [globalHeckeClearedZeta, ite_eq_right hω]
    refine (hupper z hz).trans ?_
    calc
      A ≤ 2 * (A + B + D) := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by linarith [sq_nonneg ‖z‖])

/-- A Gaussian multiplier puts the cleared continuation of every global
adelic zeta integral in the entire Schwartz–Bergman space. -/
def globalHeckeBergmanRepresentative : Bergman := by
  refine ⟨fun z => Complex.exp (z^2) * globalHeckeClearedZeta F ν ω f z, ?_⟩
  have hg : (fun z : ℂ => Complex.exp (z ^ 2)) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
    simpa using gaussian_mem_schwartzBergmanSubmodule (univ : Set ℝ) isOpen_univ
  have ha : Differentiable ℂ (globalHeckeClearedZeta F ν ω f) :=
    fun z => (globalHeckeClearedZeta_analytic F ν ω f z).differentiableAt
  have hgdiff : Differentiable ℂ (fun z : ℂ => Complex.exp (z ^ 2)) := by fun_prop
  refine ⟨by simp, (hgdiff.mul ha).differentiableOn, fun a b hab hs N => ?_⟩
  obtain ⟨C, hC, hbnd⟩ := globalHeckeClearedZeta_strip_bound F ν ω f a b
  obtain ⟨A, hA⟩ := hg.2.2 a b hab hs N
  obtain ⟨B, hB⟩ := hg.2.2 a b hab hs (N+2)
  refine ⟨C * (A + B), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have ho : ‖z‖ ^ N * ‖Complex.exp (z^2)‖ ≤ A := by
    simpa only [norm_mul, norm_pow] using hA ⟨z, hz, rfl⟩
  have ht : ‖z‖ ^ (N+2) * ‖Complex.exp (z^2)‖ ≤ B := by
    simpa only [norm_mul, norm_pow] using hB ⟨z, hz, rfl⟩
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ ‖z‖ ^ N * (‖Complex.exp (z^2)‖ * (C * (1 + ‖z‖ ^ 2))) := by
      gcongr
      exact hbnd z hz
    _ = C * (‖z‖ ^ N * ‖Complex.exp (z^2)‖ +
        ‖z‖ ^ (N+2) * ‖Complex.exp (z^2)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add ho ht) hC

/-- The strip-decay representative has exactly the cleared divisor orders. -/
theorem globalHeckeBergmanRepresentative_order (z : ℂ) :
    analyticOrderAt (globalHeckeBergmanRepresentative F ν ω f).val z =
      analyticOrderAt (globalHeckeClearedZeta F ν ω f) z := by
  have h : AnalyticAt ℂ (fun s : ℂ => Complex.exp (s^2)) z := by fun_prop
  change analyticOrderAt ((fun s : ℂ => Complex.exp (s^2)) *
    globalHeckeClearedZeta F ν ω f) z = _
  rw [analyticOrderAt_mul h (globalHeckeClearedZeta_analytic F ν ω f z),
    h.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _), zero_add]

private theorem eventually_ne_at_puncture (c p : ℂ) : ∀ᶠ z in 𝓝[≠] c, z ≠ p := by
  by_cases h : c = p
  · subst p
    exact self_mem_nhdsWithin
  · exact eventually_ne_nhdsWithin h

/-- The entire function has the order of the pole factor times the
meromorphic continuation, including at the potential poles. -/
theorem globalHeckeClearedZeta_meromorphicOrder (c : ℂ) :
    meromorphicOrderAt (globalHeckeClearedZeta F ν ω f) c =
      meromorphicOrderAt (globalHeckePoleFactor F ω) c +
        meromorphicOrderAt (globalZetaContinued F ν f (χ F ω) 0) c := by
  have he : globalHeckeClearedZeta F ν ω f =ᶠ[𝓝[≠] c]
      globalHeckePoleFactor F ω * globalZetaContinued F ν f (χ F ω) 0 := by
    filter_upwards [eventually_ne_at_puncture c 0, eventually_ne_at_puncture c 1]
      with z h₀ h₁ using globalHeckeClearedZeta_eq F ν ω f z h₀ h₁
  exact (meromorphicOrderAt_congr he).trans (meromorphicOrderAt_mul
    (globalHeckePoleFactor_analytic F ω c).meromorphicAt
    (globalZetaContinued_meromorphic F ν f _ (compactIdeleClassCharacter_unitary F ω)
      0 c trivial))

theorem globalHeckeClearedZeta_order_ne_top
    (hf : ∀ z, meromorphicOrderAt (globalZetaContinued F ν f (χ F ω) 0) z ≠ ⊤)
    (z : ℂ) : analyticOrderAt (globalHeckeClearedZeta F ν ω f) z ≠ ⊤ := by
  intro h
  have ho : meromorphicOrderAt (globalHeckeClearedZeta F ν ω f) z = ⊤ := by
    rw [(globalHeckeClearedZeta_analytic F ν ω f z).meromorphicOrderAt_eq, h, ENat.map_top]
  have hp : meromorphicOrderAt (globalHeckePoleFactor F ω) z ≠ ⊤ := by
    intro htop
    have he := meromorphicOrderAt_eq_top_iff.mp htop
    have hfalse := he.and ((eventually_ne_at_puncture z 0).and (eventually_ne_at_puncture z 1))
    obtain ⟨w, hw, h₀, h₁⟩ := hfalse.exists
    have hw' : globalHeckePoleFactor F ω w = 0 := hw
    by_cases hω : ω = 1
    · exact (mul_ne_zero h₀ (sub_ne_zero.mpr h₁.symm))
        (by simpa only [globalHeckePoleFactor, ite_eq_left hω] using hw')
    · exact one_ne_zero (by simpa only [globalHeckePoleFactor, ite_eq_right hω] using hw')
  rw [globalHeckeClearedZeta_meromorphicOrder F ν ω f] at ho
  exact (WithTop.add_ne_top.mpr ⟨hp, hf z⟩) ho

private abbrev Place := HeightOneSpectrum (𝓞 F)
local instance : MeasurableSpace (Idele F) := borel _

/-- The actual Euler reference for a conductor stage has a finite
pole-cleared divisor represented by an entire Schwartz–Bergman function. -/
theorem exists_globalHeckeBergmanReference
    (η : Measure (Idele F)) [η.IsHaarMeasure]
    (S : Finset (Place F)) (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈
      (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
    [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
    (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
    [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν)) :
    ∃ (r : sLocalBruhatImage F S) (q : Bergman),
      let g := globalHeckeClearedZeta F ν ω r.val
      (∀ z, analyticOrderAt q.val z = analyticOrderAt g z) ∧
      (∀ z, analyticOrderAt g z ≠ ⊤) ∧
      (∀ t : sLocalBruhatImage F S, globalHeckeBergmanRepresentative F ν ω t.val ∈
        bergmanDivisorSubmodule g) ∧
      ∀ (a b : ℝ), a ≤ b →
        let I : Set ({z : ℂ // z.re ∈ Icc a b} × ℕ) := {i | (i.2 : ℕ∞) < analyticOrderAt g i.1}
        ∃ J : I → StrongDual ℂ (Bergman ⧸ bergmanDivisorSubmodule g),
          (∀ i p, J i ((bergmanDivisorSubmodule g).mkQ p) =
            bergmanNormalizedJet i.val.1 i.val.2 p) ∧
          Equicontinuous (fun i (p : Bergman ⧸ bergmanDivisorSubmodule g) ↦ J i p) ∧
          IsVonNBounded ℂ (range J) ∧
          ∀ i, ∃ x, ∀ j, J j x = if j = i then 1 else 0 := by
  obtain ⟨r, _, _, _, hr, hcompare⟩ :=
    exists_globalMellin_order_reference F η ω S hs hu μ ν hν
  let q := globalHeckeBergmanRepresentative F ν ω r.val
  let g := globalHeckeClearedZeta F ν ω r.val
  have horder := globalHeckeBergmanRepresentative_order F ν ω r.val
  have hfinite := globalHeckeClearedZeta_order_ne_top F ν ω r.val hr
  refine ⟨r, q, horder, hfinite, ?_, fun a b hab => ?_⟩
  · intro t
    let p := globalHeckeBergmanRepresentative F ν ω t.val
    have hg : Differentiable ℂ g :=
      fun z => (globalHeckeClearedZeta_analytic F ν ω r.val z).differentiableAt
    have hp : Differentiable ℂ p.val := by
      simpa only [preimage_univ, differentiableOn_univ] using p.property.2.1
    exact (bergmanDivisorSubmodule_mem_iff hg p).mpr
      ((entire_divisibility_iff_orders hg hp).mpr (by
        intro z
        have ha := sLocalEulerNormalizedMellin_entire F S (fun v ↦ μ v.val)
          (sLocalNormOneCharacterOfGlobal F ω S hs hu) t z (mem_univ _)
        have hle : meromorphicOrderAt g z ≤
            meromorphicOrderAt (globalHeckeClearedZeta F ν ω t.val) z := by
          change meromorphicOrderAt (globalHeckeClearedZeta F ν ω r.val) z ≤ _
          rw [globalHeckeClearedZeta_meromorphicOrder, globalHeckeClearedZeta_meromorphicOrder,
            hcompare t z, ← add_assoc]
          exact le_add_of_nonneg_right ha.meromorphicOrderAt_nonneg
        rw [(hg.analyticAt z).meromorphicOrderAt_eq,
          (globalHeckeClearedZeta_analytic F ν ω t.val z).meromorphicOrderAt_eq] at hle
        change analyticOrderAt g z ≤
          analyticOrderAt (globalHeckeBergmanRepresentative F ν ω t.val).val z
        rw [globalHeckeBergmanRepresentative_order]
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfinite z)
        rw [← hn] at hle ⊢
        cases hm : analyticOrderAt (globalHeckeClearedZeta F ν ω t.val) z using ENat.recTopCoe with
        | top => exact le_top
        | coe m =>
          rw [hm, ENat.map_natCast, ENat.map_natCast] at hle
          have hnm : (n : ℤ) ≤ (m : ℤ) := WithTop.coe_le_coe.mp hle
          exact_mod_cast hnm))
  · exact bergmanDivisor_quotientJets_biorthogonal _ q horder hfinite a b hab

end

end Masullo
