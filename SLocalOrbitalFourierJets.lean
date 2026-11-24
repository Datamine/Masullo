import SLocalZetaRadialDerivative
import GlobalMellinPadding
import SLocalFourierTail
import SchwartzBergman

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

section RightBounds

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

include hν in
private theorem continuedZeta_analyticAt_right (ω : PontryaginDual (K F S)) (f : E F S)
    (z : ℂ) (hz : 0 < z.re) : AnalyticAt ℂ (Z F S μ ω f) z := by
  have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  apply (sLocalThetaZeta_analytic F S ν ω f z hz).congr
  filter_upwards [ho.mem_nhds hz] with w hw
  exact (sLocalContinuedZeta_eq_theta F S μ ν hν ω f hw).symm

include hν in
/-- Every spectral power of the continued transform is bounded on each
closed strip in the positive half-plane. -/
theorem sLocalContinuedZeta_weighted_norm_bounded_rightStrip
    (ω : PontryaginDual (K F S)) (f : E F S) (a b : ℝ) (ha : 0 < a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖z ^ N * Z F S μ ω f z‖ ≤ C := by
  let g := (sLocalRadialDerivative F S)^[N] f
  obtain ⟨c, M, _, hM, hint, hbound⟩ := sLocalRadialMellin_strip_majorant F S
    (sLocalExpSection F S) (sLocalIdeleNorm_expSection F S) ν ω {g}
    (isVonNBounded_singleton (𝕜 := ℂ) g) a b ha
  refine ⟨∫ t : ℝ, M * Real.exp (-c * |t|), integral_nonneg fun _ ↦ by positivity, ?_⟩
  intro z hza hzb
  have hz := ha.trans_le hza
  have hp := sLocalContinuedZeta_iterate_radialDerivative_of_pos F S μ ν hν ω f N z hz
  change Z F S μ ω g z = (-z) ^ N * Z F S μ ω f z at hp
  have he : ‖z ^ N * Z F S μ ω f z‖ = ‖Z F S μ ω g z‖ := by
    rw [hp]
    simp only [norm_mul, norm_pow, norm_neg]
  have hr := (sLocalContinuedZeta_eq_theta F S μ ν hν ω g hz).trans
    (sLocalThetaZeta_integrable_eq_radial F S ν ω g z hz).2
  change Z F S μ ω g z = sLocalRadialMellin F S (sLocalExpSection F S) ν ω g z at hr
  rw [he, hr, sLocalRadialMellin]
  exact norm_integral_le_of_norm_le hint (.of_forall (hbound g (mem_singleton g) z hza hzb))

include hν in
/-- All complex derivatives retain rapid decay on every interior
vertical line of the positive half-plane. -/
theorem sLocalContinuedZeta_iteratedDeriv_weighted_norm_bounded
    (ω : PontryaginDual (K F S)) (f : E F S) {a : ℝ} (ha : 0 < a) (N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re = a →
      ‖z ^ N * iteratedDeriv k (Z F S μ ω f) z‖ ≤ C := by
  let G := Z F S μ ω f
  have hG : DifferentiableOn ℂ G (Complex.re ⁻¹' Ioo 0 (2*a)) := by
    intro z hz
    exact (continuedZeta_analyticAt_right F S μ ν hν ω f z hz.1).differentiableAt.differentiableWithinAt
  have hbound (c d : ℝ) (hc : 0 < c) (_ : c < d) (_ : d < 2 * a) :
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * G z‖) '' (Complex.re ⁻¹' Ioo c d)) := by
    obtain ⟨C, _, hC⟩ := sLocalContinuedZeta_weighted_norm_bounded_rightStrip F S μ ν hν ω f c d hc N
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC z hz.1.le hz.2.le
  obtain ⟨C, hC⟩ := verticalStrip_weighted_iteratedDeriv_bounded 0 (2*a) (by linarith)
    G hG N hbound k (a/2) (3*a/2) (by linarith) (by linarith) (by linarith)
  refine ⟨max C 0, le_max_right _ _, fun z hz ↦ ?_⟩
  refine (hC (mem_image_of_mem _ (show z.re ∈ Ioo (a/2) (3*a/2) from ?_))).trans (le_max_left _ _)
  rw [hz]
  constructor <;> linarith

private theorem lattice_weight_le (a b d : ℝ) (ha : 0 < a) (hd : d ≠ 0) (m : ℤ) :
    |(m : ℝ)| ≤ ((1 + |b| / a) / |d|) * ‖(a : ℂ) + ((b + (m : ℝ) * d : ℝ) : ℂ) * Complex.I‖ := by
  let z := (a : ℂ) + ((b + (m : ℝ) * d : ℝ) : ℂ) * Complex.I
  have hre : z.re = a := by simp [z]
  have him : z.im = b + (m : ℝ) * d := by simp [z]
  have hnorm : a ≤ ‖z‖ := by
    simpa only [hre, abs_of_pos ha] using Complex.abs_re_le_norm z
  have hB : |b| ≤ (|b| / a) * ‖z‖ := by
    calc
      _ = (|b| / a) * a := (div_mul_cancel₀ _ ha.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (div_nonneg (abs_nonneg _) ha.le)
  have hm : |(m : ℝ)| * |d| ≤ (1 + |b| / a) * ‖z‖ := by
    rw [← abs_mul, show (m : ℝ) * d = z.im - b by rw [him]; ring]
    calc
      _ ≤ |z.im| + |b| := abs_sub _ _
      _ ≤ ‖z‖ + (|b| / a) * ‖z‖ := add_le_add (Complex.abs_im_le_norm z) hB
      _ = _ := by ring
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (abs_pos.mpr hd)).mpr hm

include hν in
/-- Fourier jets in §7.3.1.6(5) decay faster than every inverse power of
the lattice index. The local Fourier integral is represented by its
compression on the stage, including when the stage omits a different prime. -/
theorem sLocalOrbitalFourierJets_rapid (ω : PontryaginDual (K F S)) (f : E F S)
    (b d : ℝ) (hd : d ≠ 0) (N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℤ, |(m : ℝ)| ^ N *
      ‖iteratedDeriv k (fun s : ℂ ↦ Z F S μ ω (sLocalFourierCompression F S f) (1 - s))
        (((b + (m : ℝ) * d : ℝ) : ℂ) * Complex.I)‖ ≤ C := by
  let G := Z F S μ ω (sLocalFourierCompression F S f)
  obtain ⟨C, hC, hbound⟩ := sLocalContinuedZeta_iteratedDeriv_weighted_norm_bounded
    F S μ ν hν ω (sLocalFourierCompression F S f) (a := 1) zero_lt_one N k
  let L := (1 + |-b| / 1) / |-d|
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  refine ⟨L ^ N * C, mul_nonneg (pow_nonneg hL _) hC, fun m ↦ ?_⟩
  let w : ℂ := (((b + (m : ℝ) * d : ℝ) : ℂ) * Complex.I)
  let z : ℂ := 1 - w
  have hz : z.re = 1 := by simp [z, w]
  have hm : |(m : ℝ)| ≤ L * ‖z‖ := by
    have he : z = (1 : ℂ) + (((-b + (m : ℝ) * -d : ℝ) : ℂ) * Complex.I) := by
      dsimp only [z, w]
      push_cast
      ring
    rw [he]
    exact lattice_weight_le 1 (-b) (-d) zero_lt_one (neg_ne_zero.mpr hd) m
  change |(m : ℝ)| ^ N * ‖iteratedDeriv k (fun s : ℂ ↦ G (1 - s)) w‖ ≤ _
  rw [iteratedDeriv_comp_const_sub]
  simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc
    _ ≤ (L * ‖z‖) ^ N * ‖iteratedDeriv k G z‖ := by
      gcongr
    _ = L ^ N * ‖z ^ N * iteratedDeriv k G z‖ := by rw [norm_mul, norm_pow, mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound z hz) (pow_nonneg hL _)

include hν in
/-- The sampled Fourier jets have Schwartz decay in the integer parameter
of each finite-place Euler lattice. -/
theorem sLocalOrbitalFinitePlaceFourierJets_rapid
    (hF : ∀ f ∈ E F S, GlobalBruhat.fourier F f ∈ E F S)
    (ω : PontryaginDual (K F S)) (f : E F S) (v : S) (N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℤ, |(m : ℝ)| ^ N *
      ‖iteratedDeriv k (fun s : ℂ ↦ Z F S μ ω (sLocalStageFourier F S hF f) (1-s))
        (((m : ℂ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) -
          finitePolePhase F S ω v) * Complex.I)‖ ≤ C := by
  let b := -finitePolePhase F S ω v
  let d := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
  have hlog : 0 < Real.log (v.val.asIdeal.absNorm : ℝ) :=
    Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
  have hd : 0 < d := div_pos (mul_pos (by norm_num) Real.pi_pos) hlog
  obtain ⟨C, hC, h⟩ := sLocalOrbitalFourierJets_rapid F S μ ν hν ω f b d hd.ne' N k
  refine ⟨C, hC, fun m ↦ ?_⟩
  rw [sLocalStageFourier_eq_compression F S hF]
  have he : ((m : ℂ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) -
      finitePolePhase F S ω v) =
      (((b + (m : ℝ) * d : ℝ) : ℂ)) := by
    dsimp [b, d]
    push_cast
    ring
  rw [he]
  exact h m

end RightBounds

section ReflectedOrders

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μ v).IsHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
  (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]
  (hνG : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
variable (ω : PontryaginDual (normOneIdeleClass F))
variable (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
variable (hF : ∀ f ∈ sLocalBruhatImage F S, GlobalBruhat.fourier F f ∈ sLocalBruhatImage F S)

include hu in
omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem globalNormOneCharacter_inv_mem_sUnramified :
    globalNormOneCharacter F ω⁻¹ ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) := by
  apply (mem_sUnramified_iff F S _).mpr
  intro v hv u
  let q := ideleClassMap F (singleFiniteIdele F v
    (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u))
  have hc := (mem_sUnramified_iff F S _).mp hu v hv u
  change (((ω (ideleClassNormOnePart F q))⁻¹ : Circle) : ℂ) = 1
  change (ω (ideleClassNormOnePart F q) : ℂ) = 1 at hc
  rw [Circle.coe_inv, hc, inv_one]

private abbrev σ := sLocalNormOneCharacterOfGlobal F ω S hs hu

private abbrev G (f : GlobalBruhat F) :=
  globalZetaContinued F νG f (compactIdeleClassCharacter F ω) 0

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem globalMellin_order_fourier (f : GlobalBruhat F) (c : ℂ) :
    meromorphicOrderAt (G F νG ω f) c =
      meromorphicOrderAt (G F νG ω⁻¹ (GlobalBruhat.fourier F f)) (1 - c) := by
  let r (z : ℂ) := 1 - z
  have he : G F νG ω f = G F νG ω⁻¹ (GlobalBruhat.fourier F f) ∘ r :=
    funext (globalZetaContinued_compact_functionalEquation F νG f ω)
  have hr : AnalyticAt ℂ r c := analyticAt_const.sub analyticAt_id
  have hd : deriv r c ≠ 0 := by
    have hd : HasDerivAt r (-1) c := (hasDerivAt_id c).const_sub 1
    rw [hd.deriv]
    norm_num
  rw [he]
  exact meromorphicOrderAt_comp_of_deriv_ne_zero hr hd

include hνG in
private theorem globalMellin_order_leftTranslate (χ : PontryaginDual (normOneIdeleClass F))
    (g : Idele F) (f : GlobalBruhat F) (c : ℂ) :
    meromorphicOrderAt (G F νG χ (GlobalBruhat.leftTranslate F g f)) c =
      meromorphicOrderAt (G F νG χ f) c := by
  let w (z : ℂ) := (ideleNormTwist F (compactIdeleClassCharacter F χ) z (ideleClassMap F g) : ℂ)
  have ha : AnalyticAt ℂ w c :=
    analyticAt_const.mul ((analyticAt_id.mul analyticAt_const).cexp)
  have hne : w c ≠ 0 := Units.ne_zero _
  have havoid (b : ℂ) : ∀ᶠ z in 𝓝[≠] c, z ≠ b := by
    by_cases hb : c = b
    · subst b
      exact self_mem_nhdsWithin
    · have h : ∀ᶠ z in 𝓝 c, z ≠ b := (isClosed_singleton (x := b)).isOpen_compl.mem_nhds hb
      exact h.filter_mono nhdsWithin_le_nhds
  have he : G F νG χ (GlobalBruhat.leftTranslate F g f) =ᶠ[𝓝[≠] c] w * G F νG χ f := by
    filter_upwards [havoid 0, havoid 1] with z hz₀ hz₁
    exact globalZetaContinued_leftTranslate F η νG hνG g f χ z (fun _ ↦ ⟨hz₀,hz₁⟩)
  exact (meromorphicOrderAt_congr he).trans (meromorphicOrderAt_mul_of_ne_zero ha hne)

include hνG in
/-- Pole clearing gives equal orders at
reflected parameters for the two local components, even at zeros. The
global reference shifts cancel because each component attains its own
lower order bound. -/
theorem sLocalNormalizedMellin_order_compression
    (f : sLocalBruhatImage F S) (c : ℂ) :
    meromorphicOrderAt (sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
        (σ F S ω hs hu) f) c =
      meromorphicOrderAt (sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
        (σ F S ω⁻¹ hs (globalNormOneCharacter_inv_mem_sUnramified F S ω hu))
        (sLocalFourierCompression F S f)) (1 - c) := by
  let hu' := globalNormOneCharacter_inv_mem_sUnramified F S ω hu
  let A := σ F S ω hs hu
  let B := σ F S ω⁻¹ hs hu'
  let T := sLocalFourierCompression F S
  let N (χ : PontryaginDual (K F S)) :=
    sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) χ
  obtain ⟨r, C, hC, hr, hfinite, hOrd⟩ :=
    exists_globalMellin_order_reference F η ω S hs hu μ νG hνG
  obtain ⟨r', C', hC', hr', _, hOrd'⟩ :=
    exists_globalMellin_order_reference F η ω⁻¹ S hs hu' μ νG hνG
  let m := meromorphicOrderAt (G F νG ω r.val) c
  let m' := meromorphicOrderAt (G F νG ω⁻¹ r'.val) (1 - c)
  have hA (g : sLocalBruhatImage F S) :
      meromorphicOrderAt (G F νG ω g.val) c = m + meromorphicOrderAt (N A g) c := hOrd g c
  have hB (g : sLocalBruhatImage F S) :
      meromorphicOrderAt (G F νG ω⁻¹ g.val) (1 - c) =
        m' + meromorphicOrderAt (N B g) (1 - c) := hOrd' g (1-c)
  have hnn (χ : PontryaginDual (K F S)) (g : sLocalBruhatImage F S) (z : ℂ) :
      0 ≤ meromorphicOrderAt (N χ g) z :=
    (sLocalEulerNormalizedMellin_entire F S (fun v ↦ μ v.val) χ g z
      (mem_univ _)).meromorphicOrderAt_nonneg
  have hEq (g : sLocalBruhatImage F S) :
      meromorphicOrderAt (G F νG ω g.val) c =
        meromorphicOrderAt (G F νG ω⁻¹ (T g).val) (1-c) :=
    (globalMellin_order_fourier F νG ω g.val c).trans (by
      rw [sLocalFourier_eq_tailTranslate F S g]
      exact globalMellin_order_leftTranslate F η νG hνG ω⁻¹ _ _ _)
  have hEq' (g : sLocalBruhatImage F S) :
      meromorphicOrderAt (G F νG ω⁻¹ g.val) (1-c) =
        meromorphicOrderAt (G F νG ω (T g).val) c := by
    have he := globalMellin_order_fourier F νG ω⁻¹ g.val (1-c)
    rw [inv_inv, sub_sub_cancel] at he
    rw [sLocalFourier_eq_tailTranslate F S g] at he
    exact he.trans (globalMellin_order_leftTranslate F η νG hνG ω _ _ _)
  have hm' : m' ≤ m := by
    have he := hEq r
    change m = meromorphicOrderAt (G F νG ω⁻¹ (T r).val) (1-c) at he
    rw [he, hB]
    exact le_add_of_nonneg_right (hnn B (T r) (1-c))
  have hm : m ≤ m' := by
    have he := hEq' r'
    change m' = meromorphicOrderAt (G F νG ω (T r').val) c at he
    rw [he, hA]
    exact le_add_of_nonneg_right (hnn A (T r') c)
  have he := hEq f
  rw [hA, hB, ← le_antisymm hm hm'] at he
  exact WithTop.add_left_cancel (hfinite c) he

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem restricted_normOne_inv :
    σ F S ω⁻¹ hs (globalNormOneCharacter_inv_mem_sUnramified F S ω hu) =
      (σ F S ω hs hu)⁻¹ := by
  apply DFunLike.ext
  intro x
  obtain ⟨k, rfl⟩ := globalNormOneToSLocal_surjective F S hs x
  rw [sLocalNormOneCharacterOfGlobal_match]
  change (ω k)⁻¹ = (σ F S ω hs hu (globalNormOneToSLocal F S hs k))⁻¹
  rw [sLocalNormOneCharacterOfGlobal_match]

omit [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem sLocalSelectedFinitePoleCount_re_zero (χ : PontryaginDual (K F S))
    (W : Finset S) (c : ℂ) (ht : 0 < sLocalSelectedFinitePoleCount F S χ W c) :
    c.re = 0 := by
  have ht' : 0 < (W.filter fun v ↦ finiteZetaWeilMultiplier F v.val
      (sLocalFiniteZetaPhases F S χ v) c = 0).card := ht
  obtain ⟨v, hv⟩ := Finset.card_pos.mp ht'
  have h := (Finset.mem_filter.mp hv).2
  let ψ := sLocalFiniteZetaPhases F S χ v
  by_cases hψ : finiteZetaUnramified F v.val ψ
  · change finiteZetaWeilMultiplier F v.val ψ c = 0 at h
    rw [finiteZetaWeilMultiplier, ite_eq_left hψ] at h
    have he := congrArg norm (sub_eq_zero.mp h)
    have hL : 0 < Real.log (v.val.asIdeal.absNorm : ℝ) := Real.log_pos (by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.val)
    simp only [finiteZetaRatio, norm_one, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] at he
    have hz := (Real.exp_eq_one_iff _).mp he.symm
    exact neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hL.ne')
  · change finiteZetaWeilMultiplier F v.val ψ c = 0 at h
    simp [finiteZetaWeilMultiplier, hψ] at h

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable (νS : Measure (K F S)) [νS.IsHaarMeasure]
variable (hνS : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S (fun v ↦ μ v.val) (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S νS))

include hνG hνS in
/-- At a selected center, the removed Laurent band and the reflected
Fourier jet have the same vanishing filtration. -/
theorem sLocalOrbitalCompressedJet_vanish_iff_normalized_order
    (f : sLocalBruhatImage F S) (c : ℂ) (hc : c.re = 0) (n : ℕ) :
    (∀ k < n, iteratedDeriv k (fun z : ℂ ↦
      Z F S (fun v ↦ μ v.val) (σ F S ω hs hu)⁻¹ (sLocalFourierCompression F S f) (1 - z)) c = 0) ↔
    (n : WithTop ℤ) ≤ meromorphicOrderAt
      (sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) (σ F S ω hs hu) f) c := by
  let B := (σ F S ω hs hu)⁻¹
  let g := sLocalFourierCompression F S f
  let Q := Z F S (fun v ↦ μ v.val) B g
  let N := sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) B g
  let D := sLocalEulerDenominator F S B
  let w := 1 - c
  have hw : 0 < w.re := by simp [w, hc]
  have hNU := sLocalNormalizedMellin_order_compression F S μ η νG hνG ω hs hu f c
  rw [restricted_normOne_inv F S ω hs hu] at hNU
  have hQ : AnalyticAt ℂ Q w :=
    continuedZeta_analyticAt_right F S (fun v ↦ μ v.val) νS hνS B g w hw
  have hD := sLocalEulerDenominator_analytic F S B w
  have hD₀ := sLocalEulerDenominator_ne_zero_of_pos F S B hw
  have hDord : meromorphicOrderAt D w = 0 := by
    rw [hD.meromorphicOrderAt_eq, hD.analyticOrderAt_eq_zero.mpr hD₀]
    rfl
  have he := meromorphicOrderAt_congr
    (sLocalEulerNormalizedMellin_eq_germ F S (fun v ↦ μ v.val) B g w)
  change meromorphicOrderAt N w = meromorphicOrderAt (D * Q) w at he
  rw [meromorphicOrderAt_mul hD.meromorphicAt hQ.meromorphicAt, hDord, zero_add] at he
  change (∀ k < n, iteratedDeriv k (fun z : ℂ ↦ Q (1-z)) c = 0) ↔ _
  rw [hNU, show meromorphicOrderAt (sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) B g) w =
      meromorphicOrderAt Q w from he]
  have hleft : (∀ k < n, iteratedDeriv k (fun z : ℂ ↦ Q (1-z)) c = 0) ↔
      ∀ k < n, iteratedDeriv k Q w = 0 := by
    apply forall_congr'
    intro k
    apply imp_congr_right
    intro _
    rw [iteratedDeriv_comp_const_sub]
    change (-1 : ℂ) ^ k * iteratedDeriv k Q w = 0 ↔ _
    exact mul_eq_zero_iff_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  rw [hleft, ← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hQ, hQ.meromorphicOrderAt_eq]
  cases h : analyticOrderAt Q w with
  | top => simp
  | coe j =>
    rw [ENat.map_natCast, ENat.natCast_le_natCast]
    change n ≤ j ↔ (n : WithTop ℤ) ≤ ((j : ℤ) : WithTop ℤ)
    norm_cast

include hνG hνS in
/-- Both the Fourier-jet and Laurent descriptions have exactly the
specified principal-value range as their common kernel. -/
theorem sLocalOrbitalCompressedJets_ker_eq_principalValue_range
    (W : Finset S) (f : sLocalBruhatImage F S) :
    let A := σ F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S νS A
    M.mkQ f ∈ (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ ↔
      ∀ c : ℂ, ∀ k < sLocalSelectedFinitePoleCount F S A W c,
        iteratedDeriv k (fun z : ℂ ↦
          Z F S (fun v ↦ μ v.val) A⁻¹ (sLocalFourierCompression F S f) (1-z)) c = 0 := by
  let A := σ F S ω hs hu
  let M := sLocalHomogeneousThetaKernel F S νS A
  change M.mkQ f ∈ (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ ↔ _
  rw [sLocal_mk_mem_selected_finiteImage_iff_removed_coefficients F S
    (fun v ↦ μ v.val) νS hνS A W f]
  apply forall_congr'
  intro c
  let t := sLocalSelectedFinitePoleCount F S A W c
  let d := sLocalPoleCount F S A c
  by_cases ht : 0 < t
  · have hc := sLocalSelectedFinitePoleCount_re_zero F S A W c ht
    have hjet := sLocalOrbitalCompressedJet_vanish_iff_normalized_order
      F S μ η νG hνG ω hs hu νS hνS f c hc t
    have hb := sLocal_removedLaurent_iff_normalized_order F S (fun v ↦ μ v.val) A W f c
    have hband : (∀ k : ℕ, d - t < k → k ≤ d →
        sLocalLaurentCoeff F S (fun v ↦ μ v.val) A c k f = 0) ↔
        (∀ k : ℕ, d - t < k → sLocalLaurentCoeff F S (fun v ↦ μ v.val) A c k f = 0) := by
      refine ⟨fun h k hk ↦ ?_, fun h k hk _ ↦ h k hk⟩
      by_cases hkd : k ≤ d
      · exact h k hk hkd
      · have hbound := sLocalZeta_poleOrder_le_euler F S (fun v ↦ μ v.val) A f c
        rw [sLocalEulerFactor_order F S A c, sLocalAllowedPoleOrder_eq_count F S A c] at hbound
        exact (sLocalLaurentCoeff_vanish_iff F S (fun v ↦ μ v.val) A c d f).mpr
          hbound k (lt_of_not_ge hkd)
    exact (⟨fun h ↦ h ht, fun h _ ↦ h⟩ : (_ → _) ↔ _).trans
      (hband.trans (hb.trans hjet.symm))
  · exact ⟨fun _ k hk ↦ (ht (Nat.zero_le k |>.trans_lt hk)).elim, fun _ h ↦ (ht h).elim⟩


include hνS in
private theorem reflectedStageMellin_analyticAt
    (χ : PontryaginDual (K F S)) (f : sLocalBruhatImage F S) (c : ℂ) (hc : c.re = 0) :
    AnalyticAt ℂ (fun z : ℂ ↦ Z F S (fun v ↦ μ v.val) χ (sLocalFourierCompression F S f) (1-z)) c := by
  let g := sLocalFourierCompression F S f
  let w := 1 - c
  have hw : 0 < w.re := by simp [w, hc]
  have ha := continuedZeta_analyticAt_right F S (fun v ↦ μ v.val) νS hνS χ g w hw
  have hR : AnalyticAt ℂ (fun z : ℂ ↦ 1-z) c := analyticAt_const.sub analyticAt_id
  exact ha.comp (f := fun z : ℂ ↦ 1 - z) (x := c) hR

include hνS in
private def orbitalFourierJetLinear (χ : PontryaginDual (K F S)) (c : ℂ) (hc : c.re = 0) (k : ℕ) :
    sLocalBruhatImage F S →ₗ[ℂ] ℂ where
  toFun f := iteratedDeriv k
    (fun z : ℂ ↦ Z F S (fun v ↦ μ v.val) χ (sLocalFourierCompression F S f) (1-z)) c
  map_add' f g := by
    let T := sLocalFourierCompression F S
    let B (u : sLocalBruhatImage F S) (z : ℂ) := Z F S (fun v ↦ μ v.val) χ (T u) (1-z)
    have hadd : B (f+g) = B f + B g := by
      funext z
      let P := sLocalContinuedMellinEval F S (fun v ↦ μ v.val) χ (1-z)
      change P (T (f+g)) = P (T f) + P (T g)
      rw [map_add, map_add]
    change iteratedDeriv k (B (f+g)) c = _
    rw [hadd]
    exact iteratedDeriv_add
      (reflectedStageMellin_analyticAt F S μ νS hνS χ f c hc).contDiffAt
      (reflectedStageMellin_analyticAt F S μ νS hνS χ g c hc).contDiffAt
  map_smul' a f := by
    let T := sLocalFourierCompression F S
    let B (u : sLocalBruhatImage F S) (z : ℂ) := Z F S (fun v ↦ μ v.val) χ (T u) (1-z)
    have hsmul : B (a • f) = fun z ↦ a * B f z := by
      funext z
      let P := sLocalContinuedMellinEval F S (fun v ↦ μ v.val) χ (1-z)
      change P (T (a • f)) = a * P (T f)
      rw [map_smul, map_smul, smul_eq_mul]
    change iteratedDeriv k (B (a • f)) c = _
    rw [hsmul, iteratedDeriv_const_mul_field]
    rfl

include hνG hνS in
/-- Every selected Fourier jet is a continuous linear functional on
the actual principal-value quotient. The finite Laurent block at the
same center controls its continuity. -/
theorem exists_sLocalOrbitalCompressedJet_on_quotient
    (W : Finset S) (c : ℂ) (k : ℕ)
    (hk : k < sLocalSelectedFinitePoleCount F S (σ F S ω hs hu) W c) :
    let A := σ F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S νS A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    ∃ J : StrongDual ℂ ((SLocalHomogeneousThetaQuotient F S νS A) ⧸ R),
      ∀ f : sLocalBruhatImage F S, J (R.mkQ (M.mkQ f)) =
        iteratedDeriv k (fun z : ℂ ↦
          Z F S (fun v ↦ μ v.val) A⁻¹ (sLocalFourierCompression F S f) (1-z)) c := by
  let A := σ F S ω hs hu
  let M := sLocalHomogeneousThetaKernel F S νS A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let t := sLocalSelectedFinitePoleCount F S A W c
  let d := sLocalPoleCount F S A c
  let I := ↥(Finset.Ioc (d-t) d)
  let P : sLocalBruhatImage F S →L[ℂ] (I → ℂ) :=
    ContinuousLinearMap.pi fun i ↦ sLocalLaurentCoeff F S (fun v ↦ μ v.val) A c i.val
  have hp : 0 < t := (Nat.zero_le k).trans_lt hk
  have hc := sLocalSelectedFinitePoleCount_re_zero F S A W c hp
  let L := orbitalFourierJetLinear F S μ νS hνS A⁻¹ c hc k
  have hker : P.ker ≤ L.ker := by
    intro f hf
    have hv : ∀ n > d-t, sLocalLaurentCoeff F S (fun v ↦ μ v.val) A c n f = 0 := by
      intro n hn
      by_cases hnd : n ≤ d
      · have hi : n ∈ Finset.Ioc (d-t) d := Finset.mem_Ioc.mpr ⟨hn, hnd⟩
        exact congrFun (LinearMap.mem_ker.mp hf) (⟨n, hi⟩ : I)
      · have hb := sLocalZeta_poleOrder_le_euler F S (fun v ↦ μ v.val) A f c
        rw [sLocalEulerFactor_order F S A c, sLocalAllowedPoleOrder_eq_count F S A c] at hb
        exact (sLocalLaurentCoeff_vanish_iff F S (fun v ↦ μ v.val) A c d f).mpr
          hb n (lt_of_not_ge hnd)
    apply LinearMap.mem_ker.mpr
    exact (sLocalOrbitalCompressedJet_vanish_iff_normalized_order
      F S μ η νG hνG ω hs hu νS hνS f c hc t).mpr
        ((sLocal_removedLaurent_iff_normalized_order F S (fun v ↦ μ v.val) A W f c).mp hv) k hk
  let Pₗ := P.toLinearMap
  obtain ⟨Q, hQ⟩ := LinearMap.exists_extend
    ((P.ker.liftQ L hker).comp Pₗ.quotKerEquivRange.symm.toLinearMap)
  let C : sLocalBruhatImage F S →L[ℂ] ℂ :=
    (⟨Q, Q.continuous_of_finiteDimensional⟩ : (I → ℂ) →L[ℂ] ℂ).comp P
  have hC (f : sLocalBruhatImage F S) : C f = L f := by
    have he := DFunLike.congr_fun hQ (Pₗ.quotKerEquivRange (P.ker.mkQ f))
    have hproj : (Pₗ.quotKerEquivRange (P.ker.mkQ f) : I → ℂ) = P f :=
      Pₗ.quotKerEquivRange_apply_mk f
    change Q ((Pₗ.quotKerEquivRange (P.ker.mkQ f) : Pₗ.range) : I → ℂ) =
      (P.ker.liftQ L hker) (Pₗ.quotKerEquivRange.symm
      (Pₗ.quotKerEquivRange (P.ker.mkQ f))) at he
    rw [hproj, LinearEquiv.symm_apply_apply] at he
    exact he
  have hCR (f : sLocalBruhatImage F S) (hf : M.mkQ f ∈ R) : C f = 0 := by
    rw [hC]
    exact (sLocalOrbitalCompressedJets_ker_eq_principalValue_range
      F S μ η νG hνG ω hs hu νS hνS W f).mp hf c k hk
  have hM : M ≤ C.ker := by
    intro f hf
    apply LinearMap.mem_ker.mpr
    apply hCR f
    rw [show M.mkQ f = 0 from (Submodule.Quotient.mk_eq_zero M).mpr hf]
    exact R.zero_mem
  let D := M.liftQL C hM
  have hR : R ≤ D.ker := by
    intro q hq
    obtain ⟨f, rfl⟩ := M.mkQ_surjective q
    exact hCR f hq
  exact ⟨R.liftQL D hR, hC⟩


include hνG in
theorem sLocalNormalizedMellin_order_fourier
    (f : sLocalBruhatImage F S) (c : ℂ) :
    meromorphicOrderAt (sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
        (σ F S ω hs hu) f) c =
      meromorphicOrderAt (sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val)
        (σ F S ω⁻¹ hs (globalNormOneCharacter_inv_mem_sUnramified F S ω hu))
        (sLocalStageFourier F S hF f)) (1 - c) := by
  simp only [sLocalStageFourier_eq_compression]
  exact sLocalNormalizedMellin_order_compression F S μ η νG hνG ω hs hu f c

include hνG hνS in
theorem sLocalOrbitalFourierJet_vanish_iff_normalized_order
    (f : sLocalBruhatImage F S) (c : ℂ) (hc : c.re = 0) (n : ℕ) :
    (∀ k < n, iteratedDeriv k (fun z : ℂ ↦
      Z F S (fun v ↦ μ v.val) (σ F S ω hs hu)⁻¹ (sLocalStageFourier F S hF f) (1 - z)) c = 0) ↔
    (n : WithTop ℤ) ≤ meromorphicOrderAt
      (sLocalEulerNormalizedMellin F S (fun v ↦ μ v.val) (σ F S ω hs hu) f) c := by
  simp only [sLocalStageFourier_eq_compression]
  exact sLocalOrbitalCompressedJet_vanish_iff_normalized_order F S μ η νG hνG ω hs hu νS hνS f c hc n

include hνG hνS in
theorem sLocalOrbitalFourierJets_ker_eq_principalValue_range
    (W : Finset S) (f : sLocalBruhatImage F S) :
    let A := σ F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S νS A
    M.mkQ f ∈ (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ ↔
      ∀ c : ℂ, ∀ k < sLocalSelectedFinitePoleCount F S A W c,
        iteratedDeriv k (fun z : ℂ ↦
          Z F S (fun v ↦ μ v.val) A⁻¹ (sLocalStageFourier F S hF f) (1-z)) c = 0 := by
  simp only [sLocalStageFourier_eq_compression]
  exact sLocalOrbitalCompressedJets_ker_eq_principalValue_range F S μ η νG hνG ω hs hu νS hνS W f

include hνG hνS in
theorem exists_sLocalOrbitalFourierJet_on_quotient
    (W : Finset S) (c : ℂ) (k : ℕ)
    (hk : k < sLocalSelectedFinitePoleCount F S (σ F S ω hs hu) W c) :
    let A := σ F S ω hs hu
    let M := sLocalHomogeneousThetaKernel F S νS A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    ∃ J : StrongDual ℂ ((SLocalHomogeneousThetaQuotient F S νS A) ⧸ R),
      ∀ f : sLocalBruhatImage F S, J (R.mkQ (M.mkQ f)) =
        iteratedDeriv k (fun z : ℂ ↦
          Z F S (fun v ↦ μ v.val) A⁻¹ (sLocalStageFourier F S hF f) (1-z)) c := by
  simp only [sLocalStageFourier_eq_compression]
  exact exists_sLocalOrbitalCompressedJet_on_quotient F S μ η νG hνG ω hs hu νS hνS W c k hk


end ReflectedOrders

end

end Masullo
