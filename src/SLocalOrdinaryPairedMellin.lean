import SLocalTateProduct
import SLocalArchRangeComparison
import SLocalUnramifiedThetaRange

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S
private abbrev V (v : S) := v.val.adicCompletion F
private abbrev B := SchwartzBergman (Ioi (0 : ℝ)) × SchwartzBergman (Iio (1 : ℝ))

variable [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  (μ : ∀ v : S, Measure (V F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

private abbrev productHaar := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
  (hν : IsWeilQuotientMeasure (sUnitImage F S) (productHaar F S μ) Measure.count
    (sLocalClassHaar F S ν))

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

private def clearPole (H : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn (fun z ↦ (z-c)^n * H z) univ

private theorem clearPole_germ {H : ℂ → ℂ} (hH : Meromorphic H) (c : ℂ) (n : ℕ) :
    clearPole H c n =ᶠ[𝓝[≠] c] fun z ↦ (z-c)^n * H z := by
  have hm : MeromorphicOn (fun z ↦ (z-c)^n * H z) univ :=
    fun z _ ↦ (((analyticAt_id.sub analyticAt_const).pow n).meromorphicAt).mul (hH z)
  exact hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ c)

private theorem clearPole_order {H : ℂ → ℂ} (hH : Meromorphic H) (c : ℂ) (n : ℕ) :
    meromorphicOrderAt (clearPole H c n) c =
      (n : WithTop ℤ) + meromorphicOrderAt H c := by
  rw [meromorphicOrderAt_congr (clearPole_germ hH c n)]
  change meromorphicOrderAt ((fun z : ℂ ↦ (z-c)^n) * H) c = _
  have h : MeromorphicAt (fun z : ℂ ↦ (z-c)^n) c :=
    ((analyticAt_id.sub analyticAt_const).pow n).meromorphicAt
  rw [meromorphicOrderAt_mul h (hH c)]
  congr 1
  exact meromorphicOrderAt_pow_id_sub_const (x := c) (n := n)

private theorem clearPole_analytic {H : ℂ → ℂ} (hH : Meromorphic H) (c : ℂ) (n : ℕ)
    (hb : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H c) :
    AnalyticAt ℂ (clearPole H c n) c := by
  apply (meromorphicNFOn_toMeromorphicNFOn _ univ (mem_univ c)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  change 0 ≤ meromorphicOrderAt (clearPole H c n) c
  rw [clearPole_order hH]
  calc
    _ = (n : WithTop ℤ) + ((-(n : ℤ) : ℤ) : WithTop ℤ) := by simp
    _ ≤ _ := add_le_add_right hb _

private def principalPartCoeff (ω : PontryaginDual (K F S)) (H : ℂ → ℂ) (c : ℂ) (k : ℕ) : ℂ :=
  let n := sLocalAllowedPoleOrder F S ω c
  if k ≤ n then iteratedDeriv (n-k) (clearPole H c n) c / ((n-k).factorial : ℂ) else 0

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem principalPartCoeff_test (ω : PontryaginDual (K F S)) (c : ℂ) (k : ℕ) (f : E F S) :
    principalPartCoeff F S ω (Z F S μ ω f) c k = sLocalLaurentCoeff F S μ ω c k f := by
  let h := exists_sLocalMellinLaurentDisk F S ω c
  exact (sLocalLaurentCircleCoeff_eq_taylor F S μ ω c h.choose h.choose_spec.1 h.choose_spec.2 k f).symm

omit [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem principalPartCoeff_vanish {H : ℂ → ℂ} (hH : Meromorphic H)
    (ω : PontryaginDual (K F S)) (c : ℂ) (m k : ℕ)
    (hm : m ≤ sLocalAllowedPoleOrder F S ω c)
    (hb : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H c) (hk : m < k) :
    principalPartCoeff F S ω H c k = 0 := by
  let n := sLocalAllowedPoleOrder F S ω c
  change m ≤ n at hm
  have hn : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H c :=
    (WithTop.coe_le_coe.mpr (by exact_mod_cast (neg_le_neg (Int.ofNat_le.mpr hm)))).trans hb
  have hA := clearPole_analytic hH c n hn
  have horder : ((n-m : ℕ) : WithTop ℤ) ≤ meromorphicOrderAt (clearPole H c n) c := by
    rw [clearPole_order hH]
    change (((n-m : ℕ) : ℤ) : WithTop ℤ) ≤ _
    rw [Nat.cast_sub hm, sub_eq_add_neg, WithTop.coe_add]
    exact add_le_add_right hb _
  have hAorder : ((n-m : ℕ) : ENat) ≤ analyticOrderAt (clearPole H c n) c := by
    rw [hA.meromorphicOrderAt_eq] at horder
    cases e : analyticOrderAt (clearPole H c n) c with
    | top => exact le_top
    | coe a =>
      rw [e, ENat.map_natCast] at horder
      exact_mod_cast horder
  by_cases hkn : k ≤ n
  · have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mp hAorder
      (n-k) (by omega)
    change (if k ≤ n then _ else _) = 0
    rw [ite_eq_left hkn, hzero, zero_div]
  · exact ite_eq_right hkn

omit [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem order_sub_nonneg_of_principalPartCoeff {H G : ℂ → ℂ}
    (hH : Meromorphic H) (hG : Meromorphic G) (ω : PontryaginDual (K F S)) (c : ℂ)
    (hHb : ((-(sLocalAllowedPoleOrder F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H c)
    (hGb : ((-(sLocalAllowedPoleOrder F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G c)
    (he : ∀ k : ℕ, 0 < k → principalPartCoeff F S ω H c k = principalPartCoeff F S ω G c k) :
    0 ≤ meromorphicOrderAt (H-G) c := by
  let n := sLocalAllowedPoleOrder F S ω c
  let A := clearPole H c n
  let Q := clearPole G c n
  have ha := clearPole_analytic hH c n hHb
  have hq := clearPole_analytic hG c n hGb
  have hj (i : ℕ) (hi : i < n) : iteratedDeriv i (A-Q) c = 0 := by
    have h := he (n-i) (by omega)
    have hni : n - (n-i) = i := by omega
    have hle : n-i ≤ n := by omega
    change (if n-i ≤ n then iteratedDeriv (n-(n-i)) A c / ((n-(n-i)).factorial : ℂ) else 0) =
      (if n-i ≤ n then iteratedDeriv (n-(n-i)) Q c / ((n-(n-i)).factorial : ℂ) else 0) at h
    rw [ite_eq_left hle, ite_eq_left hle, hni] at h
    rw [iteratedDeriv_sub ha.contDiffAt hq.contDiffAt,
      (div_left_inj' (by exact_mod_cast i.factorial_ne_zero : (i.factorial : ℂ) ≠ 0)).mp h, sub_self]
  have hn : (n : ENat) ≤ analyticOrderAt (A-Q) c :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (ha.sub hq)).2 hj
  have hO : (n : WithTop ℤ) ≤ meromorphicOrderAt (A-Q) c := by
    rw [(ha.sub hq).meromorphicOrderAt_eq]
    cases e : analyticOrderAt (A-Q) c with
    | top => exact le_top
    | coe j =>
      rw [ENat.map_natCast]
      rw [e] at hn
      exact_mod_cast hn
  have hEq : A-Q =ᶠ[𝓝[≠] c] (fun z : ℂ ↦ (z-c)^n) * (H-G) := by
    filter_upwards [clearPole_germ hH c n, clearPole_germ hG c n] with z hz hw
    change A z - Q z = (z-c)^n * (H z-G z)
    rw [show A z = _ from hz, show Q z = _ from hw, mul_sub]
  have hpow : MeromorphicAt (fun z : ℂ ↦ (z-c)^n) c :=
    ((analyticAt_id.sub analyticAt_const).pow n).meromorphicAt
  have hpord : meromorphicOrderAt (fun z : ℂ ↦ (z-c)^n) c = (n : WithTop ℤ) :=
    meromorphicOrderAt_pow_id_sub_const (x := c) (n := n)
  rw [meromorphicOrderAt_congr hEq, meromorphicOrderAt_mul hpow ((hH c).sub (hG c)), hpord] at hO
  cases h : meromorphicOrderAt (H-G) c with
  | top => exact le_top
  | coe j =>
    rw [h] at hO
    change ((n : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) + (j : WithTop ℤ) at hO
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at hO
    exact WithTop.coe_nonneg.mpr (by omega)

include hν in
/-- Every meromorphic function with the allowed archimedean poles has the
same principal parts as an actual S-local test with finite factors vanishing
at zero. -/
theorem exists_sLocalTest_realizes_archPrincipalParts
    (ω : PontryaginDual (K F S)) (H : ℂ → ℂ) (hH : Meromorphic H)
    (hb : ∀ c : ℂ, ((-(sLocalArchPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt H c) :
    ∃ f : sLocalFiniteNonzeroTestSubspace F S Finset.univ,
      ∀ c : ℂ, 0 ≤ meromorphicOrderAt (H - Z F S μ ω f.val) c := by
  obtain ⟨g, hg, hinterp⟩ := exists_sLocalArchFixedFiniteSimultaneousInterpolation F S μ ω
  obtain ⟨φ, hφ⟩ := hinterp fun i ↦ principalPartCoeff F S ω H i.val.1 i.val.2
  let f := sLocalBruhatPure F S φ (locallyConstantTestPiProduct g)
  have hf : f ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ :=
    Submodule.subset_span ⟨φ, g, fun v _ ↦ hg v, rfl⟩
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let q : sLocalArchPolarImage F S ν ω := ⟨M.mkQ f, f, hf, rfl⟩
  have hm := sLocalProductZetaContinued_meromorphic F S μ ω
    (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) f
  refine ⟨⟨f, hf⟩, fun c ↦ ?_⟩
  have hle : sLocalArchPoleCount F S ω c ≤ sLocalAllowedPoleOrder F S ω c := by
    rw [sLocalAllowedPoleOrder_eq_count, sLocalPoleCount]
    exact Nat.le_add_right _ _
  have hnorm : ((-(sLocalAllowedPoleOrder F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (Z F S μ ω f) c := by
    rw [← sLocalEulerFactor_order]
    exact sLocalZeta_poleOrder_le_euler F S μ ω f c
  apply order_sub_nonneg_of_principalPartCoeff F S hH hm ω c
    ((WithTop.coe_le_coe.mpr (neg_le_neg (Int.ofNat_le.mpr hle))).trans (hb c)) hnorm
  intro k hk
  rw [principalPartCoeff_test]
  by_cases h : k ≤ sLocalArchPoleCount F S ω c
  · exact (hφ ⟨(c,k), hk, h⟩).symm
  · rw [principalPartCoeff_vanish F S hH ω c _ k hle (hb c) (lt_of_not_ge h)]
    exact (sLocalArchLaurentCoeff_eq_zero_of_lt F S μ ν hν ω (lt_of_not_ge h) q).symm

private def pairedContinuation (ρ : ℂ → ℂ) (p : B) (z : ℂ) : ℂ :=
  if 0 < z.re then p.1.val z else ρ z * p.2.val z

private theorem pairedContinuation_right (ρ : ℂ → ℂ) (p : B) {z : ℂ} (hz : 0 < z.re) :
    pairedContinuation ρ p z = p.1.val z := ite_eq_left hz

private theorem pairedContinuation_left (ρ : ℂ → ℂ) (p : B)
    (hp : p ∈ sLocalBergmanGluing ρ) {z : ℂ} (hz : z.re < 1) :
    pairedContinuation ρ p z = ρ z * p.2.val z := by
  by_cases h : 0 < z.re
  · exact (pairedContinuation_right ρ p h).trans (hp z h hz)
  · exact ite_eq_right h

private theorem pairedContinuation_meromorphic (ρ : ℂ → ℂ) (hρ : Meromorphic ρ) (p : B)
    (hp : p ∈ sLocalBergmanGluing ρ) : Meromorphic (pairedContinuation ρ p) := by
  intro c
  by_cases h : 0 < c.re
  · have he := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h
    apply (p.1.property.2.1.analyticAt he).meromorphicAt.congr
    filter_upwards [nhdsWithin_le_nhds he] with z hz
    exact (pairedContinuation_right ρ p hz).symm
  · have hc : c.re < 1 := by linarith
    have he := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hc
    apply ((hρ c).mul (p.2.property.2.1.analyticAt he).meromorphicAt).congr
    filter_upwards [nhdsWithin_le_nhds he] with z hz
    exact (pairedContinuation_left ρ p hp hz).symm

private abbrev D (ω : PontryaginDual (K F S)) :=
  sLocalFiniteZetaDenominator F S (sLocalFiniteZetaPhases F S ω)

omit [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem finiteDenominator_strip_bound (ω : PontryaginDual (K F S)) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r → ‖D F S ω z‖ ≤ C := by
  let L (v : S) := Real.log (v.val.asIdeal.absNorm : ℝ)
  let U (v : S) := 1 + Real.exp (-l * L v)
  have hu (v : S) : 0 ≤ U v := by dsimp [U]; positivity
  refine ⟨∏ v, U v, Finset.prod_nonneg fun v _ ↦ hu v, fun z hz ↦ ?_⟩
  unfold D sLocalFiniteZetaDenominator
  rw [norm_prod]
  apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
  intro v _
  split_ifs with hv
  · have he : ‖finiteZetaRatio F v.val (sLocalFiniteZetaPhases F S ω v) z‖ =
        Real.exp (-z.re * L v) := by
      simp only [finiteZetaRatio, L, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
        Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hL : 0 ≤ L v := Real.log_nonneg (by
      exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.val).le)
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖finiteZetaRatio F v.val (sLocalFiniteZetaPhases F S ω v) z‖ :=
        norm_sub_le _ _
      _ ≤ U v := by
        rw [norm_one, he]
        exact add_le_add_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (neg_le_neg hz.1) hL)) 1
  · simpa only [norm_one] using (le_add_of_nonneg_right (Real.exp_nonneg (-l * L v)))

private def multiplyBergman {I : Set ℝ} (D₀ : ℂ → ℂ) (ha : ∀ z, AnalyticAt ℂ D₀ z)
    (hb : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖D₀ z‖ ≤ C)
    (p : SchwartzBergman I) : SchwartzBergman I := by
  refine ⟨fun z ↦ D₀ z * p.val z, ?_, ?_, ?_⟩
  · intro z hz
    change D₀ z * p.val z = 0
    rw [p.property.1 hz]
    exact mul_zero _
  · have hdiff : Differentiable ℂ D₀ := fun z ↦ (ha z).differentiableAt
    exact hdiff.differentiableOn.mul p.property.2.1
  · intro l r hlr hsub n
    obtain ⟨C, hC, hD⟩ := hb l r
    obtain ⟨M, hM⟩ := p.property.2.2 l r hlr hsub n
    refine ⟨C * max M 0, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hp : ‖z^n * p.val z‖ ≤ max M 0 :=
      (hM (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    change ‖z^n * (D₀ z * p.val z)‖ ≤ C * max M 0
    rw [show z^n * (D₀ z * p.val z) = D₀ z * (z^n * p.val z) by ring, norm_mul]
    exact mul_le_mul (hD z hz) hp (norm_nonneg _) hC

omit [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem multFiniteArchPoleBound (ω : PontryaginDual (K F S)) (ρ : ℂ → ℂ)
    (hm : Meromorphic ρ)
    (ho : ∀ c, ((-(sLocalPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt ρ c)
    (p : B) (hp : p ∈ sLocalBergmanGluing ρ) (c : ℂ) :
    ((-(sLocalArchPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (D F S ω * pairedContinuation ρ p) c := by
  have hD : AnalyticAt ℂ (D F S ω) c :=
    sLocalFiniteZetaDenominator_analytic F S (sLocalFiniteZetaPhases F S ω) c trivial
  by_cases hc : c.re < 1
  · have hnear := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hc
    have hEq : D F S ω * pairedContinuation ρ p =ᶠ[𝓝[≠] c] D F S ω * (ρ * p.2.val) := by
      filter_upwards [nhdsWithin_le_nhds hnear] with z hz
      exact congrArg (D F S ω z * ·) (pairedContinuation_left ρ p hp hz)
    have ha := p.2.property.2.1.analyticAt hnear
    have hDord : meromorphicOrderAt (D F S ω) c =
        ((sLocalFinitePolesAt F S ω c).card : WithTop ℤ) :=
      sLocalSelectedEulerMultiplier_order F S ω Finset.univ c
    rw [meromorphicOrderAt_congr hEq, meromorphicOrderAt_mul hD.meromorphicAt
      ((hm c).mul ha.meromorphicAt), meromorphicOrderAt_mul (hm c) ha.meromorphicAt, hDord]
    have hx : ((-(sLocalArchPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) =
        ((sLocalFinitePolesAt F S ω c).card : WithTop ℤ) +
          ((-(sLocalPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) := by
      change _ = (((sLocalFinitePolesAt F S ω c).card : ℤ) : WithTop ℤ) + _
      rw [sLocalPoleCount, ← WithTop.coe_add]
      congr 1
      push_cast
      ring
    rw [hx, ← add_assoc]
    exact le_trans (add_le_add_right (ho c) _)
      (le_add_of_nonneg_right ha.meromorphicOrderAt_nonneg)
  · have hz : 0 < c.re := by linarith
    have hnear := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    have he : D F S ω * pairedContinuation ρ p =ᶠ[𝓝[≠] c] D F S ω * p.1.val := by
      filter_upwards [nhdsWithin_le_nhds hnear] with z hz
      exact congrArg (D F S ω z * ·) (pairedContinuation_right ρ p hz)
    rw [meromorphicOrderAt_congr he]
    exact le_trans (WithTop.coe_le_coe.mpr (show -(sLocalArchPoleCount F S ω c : ℤ) ≤ 0 from neg_nonpos.mpr (Int.natCast_nonneg _)))
      (hD.mul (p.1.property.2.1.analyticAt hnear)).meromorphicOrderAt_nonneg

private theorem matching_pair_eq_of_right (ρ : ℂ → ℂ)
    (hρ : ∀ z : ℂ, 0 < z.re → z.re < 1 → ρ z ≠ 0)
    (p q : B) (hp : p ∈ sLocalBergmanGluing ρ) (hq : q ∈ sLocalBergmanGluing ρ)
    (he : ∀ z : ℂ, 0 < z.re → p.1.val z = q.1.val z) : p = q := by
  have h₀ : (1/2 : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    norm_num [Complex.div_ofNat_re]
  have hOpen := isOpen_lt Complex.continuous_re (continuous_const (y := (1 : ℝ)))
  have hG : EqOn p.2.val q.2.val {z | z.re < 1} := by
    refine (p.2.property.2.1.analyticOnNhd hOpen).eqOn_of_preconnected_of_eventuallyEq
      (q.2.property.2.1.analyticOnNhd hOpen) (convex_halfSpace_re_lt 1).isPreconnected
      (z₀ := (1/2 : ℂ)) h₀.2 ?_
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).inter hOpen).mem_nhds h₀] with z hz
    exact mul_left_cancel₀ (hρ z hz.1 hz.2) ((hp z hz.1 hz.2).symm.trans
      ((he z hz.1).trans (hq z hz.1 hz.2)))
  refine Prod.ext (Subtype.ext (funext fun z ↦ ?_)) (Subtype.ext (funext fun z ↦ ?_))
  · by_cases hz : 0 < z.re
    · exact he z hz
    · exact (p.1.property.1 hz).trans (q.1.property.1 hz).symm
  · by_cases hz : z.re < 1
    · exact hG hz
    · exact (p.2.property.1 hz).trans (q.2.property.1 hz).symm

set_option maxHeartbeats 2000000 in
include hν in
/-- Clearing the finite poles reduces ordinary realization to archimedean
principal-part interpolation and the pole-free range theorem. -/
theorem sLocalPaired_range_of_archPrincipalParts
    (ω : PontryaginDual (K F S)) (ρ : ℂ → ℂ) (hρ : Meromorphic ρ)
    (hρ₀ : ∀ z : ℂ, 0 < z.re → z.re < 1 → ρ z ≠ 0)
    (ho : ∀ c, ((-(sLocalPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt ρ c)
    (hT : range (sLocalPairedBergmanMellin F S ν ω) ⊆ sLocalBergmanGluing ρ)
    (hleft : ∀ (f : E F S) c, c.re < 1 → Z F S μ ω f =ᶠ[𝓝[≠] c]
      ρ * (sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk f)).2.val)
    (hflat : ∀ p : B, p ∈ sLocalBergmanGluing ρ →
      (∀ c : ℂ, c.re < 1 → 0 ≤ meromorphicOrderAt (ρ * p.2.val) c) →
      ∃ f : sLocalPolarFreeTestSubspace F S,
        sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk f.val) = p) :
    range (sLocalPairedBergmanMellin F S ν ω) = sLocalBergmanGluing ρ := by
  refine le_antisymm hT ?_
  intro p hp
  let d := D F S ω
  have hd (z : ℂ) : AnalyticAt ℂ d z :=
    sLocalFiniteZetaDenominator_analytic F S (sLocalFiniteZetaPhases F S ω) z trivial
  let C := pairedContinuation ρ p
  let H := d * C
  have hH : Meromorphic H := fun c ↦
    (hd c).meromorphicAt.mul (pairedContinuation_meromorphic ρ hρ p hp c)
  obtain ⟨f, hf⟩ := exists_sLocalTest_realizes_archPrincipalParts F S μ ν hν ω H hH
    (multFiniteArchPoleBound F S ω ρ hρ ho p hp)
  let U := sLocalPairedBergmanMellin F S ν ω
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let u := U (M.mkQ f.val)
  let q : B := (multiplyBergman d hd (finiteDenominator_strip_bound F S ω) p.1,
    multiplyBergman d hd (finiteDenominator_strip_bound F S ω) p.2)
  have hq : q ∈ sLocalBergmanGluing ρ := by
    intro z hz hr
    change d z * p.1.val z = ρ z * (d z * p.2.val z)
    rw [hp z hz hr]
    ring
  let r := q - u
  have hr : r ∈ sLocalBergmanGluing ρ := (sLocalBergmanGluing ρ).sub_mem hq (hT ⟨_, rfl⟩)
  have hrPole (c : ℂ) (hc : c.re < 1) : 0 ≤ meromorphicOrderAt (ρ * r.2.val) c := by
    have he : H - Z F S μ ω f.val =ᶠ[𝓝[≠] c] ρ * r.2.val := by
      have hnear := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hc
      filter_upwards [nhdsWithin_le_nhds hnear, hleft f.val c hc] with z hz hz'
      change d z * C z - Z F S μ ω f.val z = ρ z * (d z * p.2.val z - u.2.val z)
      have hu : Z F S μ ω f.val z = ρ z * u.2.val z := hz'
      rw [show C z = _ from pairedContinuation_left ρ p hp hz, hu]
      ring
    rw [← meromorphicOrderAt_congr he]
    exact hf c
  obtain ⟨g, hg⟩ := hflat r hr hrPole
  have hgN : g.val ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ := by
    have hle : sLocalPolarFreeTestSubspace F S ≤ sLocalFiniteNonzeroTestSubspace F S Finset.univ := by
      rw [sLocalPolarFreeTestSubspace_eq_inf]
      exact inf_le_right
    exact hle g.property
  have hmem : f.val + g.val ∈ (sLocalWeilPrincipalValues F S Finset.univ).range := by
    rw [sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
    exact (sLocalFiniteNonzeroTestSubspace F S Finset.univ).add_mem f.property hgN
  obtain ⟨v, hv⟩ := hmem
  have hq' : U (M.mkQ (sLocalWeilPrincipalValues F S Finset.univ v)) = q := by
    calc
      _ = U (M.mkQ (f.val + g.val)) := congrArg (fun a : E F S ↦ U (M.mkQ a)) hv
      _ = u + U (M.mkQ g.val) := by rw [map_add, map_add]
      _ = u + r := congrArg (u + ·) hg
      _ = q := by dsimp only [r]; rw [add_comm u, sub_add_cancel]
  refine ⟨M.mkQ v, matching_pair_eq_of_right ρ hρ₀ _ p (hT ⟨_, rfl⟩) hp ?_⟩
  letI : (productHaar F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  have hpos (f' : E F S) (z : ℂ) (hz : 0 < z.re) : (U (M.mkQ f')).1.val z = Z F S μ ω f' z :=
    ((sLocalPairedBergmanMellin_idelic F S ν ω (productHaar F S μ) hν f').1 z hz).trans
      ((sLocalIdelicZeta_meromorphic_continuation F S μ ω f').2 hz).symm
  intro z hz
  have he := congrArg (fun a : B ↦ a.1.val z) hq'
  have he' : Z F S μ ω (sLocalWeilPrincipalValues F S Finset.univ v) z = d z * p.1.val z :=
    (hpos _ z hz).symm.trans he
  have hh := sLocalWeilPrincipalValues_continued_pos F S μ ν hν ω Finset.univ v z hz
  have hd₀ : d z ≠ 0 := sLocalFiniteZetaDenominator_ne_zero_of_pos F S (sLocalFiniteZetaPhases F S ω) z hz
  exact (hpos v z hz).trans (mul_left_cancel₀ hd₀ (hh.symm.trans he'))

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]

local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

set_option maxHeartbeats 2000000 in
include hν in
/-- At the canonical section, every pair satisfying the actual S-local
Tate relation is represented by a Schwartz–Bruhat test. -/
theorem exists_sLocalOrdinaryPaired_range (ω : PontryaginDual (K F S)) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      let ρ := sLocalExplicitTateFactor F S ω ε
      (∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ ρ z) ∧
      (∀ l r : ℝ, 0 < l → r < 1 →
        ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
          ‖ρ z‖ ≤ C * (1 + |z.im|)^k) ∧
      range (sLocalPairedBergmanMellin F S ν ω) =
        sLocalBergmanGluing ρ := by
  obtain ⟨ε, ha, hne, hstrip, hnorm, hGerm, _⟩ :=
    exists_sLocalMellin_fourier_functionalEquation F S μ ω
  obtain ⟨εv, hεv, hnorm', _, hflat⟩ := exists_sLocalTate_polarFreePaired_range F S μ ν hν ω
  obtain ⟨g, B₀, hB₀, hg⟩ := exists_sLocalEulerNormalizedMellin_constant F S μ ω
  let N (ξ : PontryaginDual (K F S)) (f : E F S) := sLocalEulerNormalizedMellin F S μ ξ f
  have hε : ε = sLocalTateEpsilonProduct F S ω εv := by
    funext z
    let R := N ω⁻¹ (sLocalSelectedFourier F S g) (1-z)
    have hR : R ≠ 0 := by
      intro h
      have he : N ω g z = ε z * R := hnorm g z
      rw [h, mul_zero] at he
      exact hB₀ ((congrFun hg z).symm.trans he)
    exact mul_right_cancel₀ hR ((hnorm g z).symm.trans (hnorm' g z))
  let ρ := sLocalExplicitTateFactor F S ω ε
  have hρ : Meromorphic ρ := sLocalExplicitTateFactor_meromorphic F S ω ε (fun z ↦ ha z trivial)
  have hρ₀ (z : ℂ) (hz : 0 < z.re) (hr : z.re < 1) : ρ z ≠ 0 := by
    have hr' : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hr
    exact mul_ne_zero (mul_ne_zero (hne z)
      (inv_ne_zero (sLocalEulerDenominator_ne_zero_of_pos F S ω hz)))
      (sLocalEulerDenominator_ne_zero_of_pos F S ω⁻¹ hr')
  have hρbound (c : ℂ) : ((-(sLocalPoleCount F S ω c : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt ρ c := by
    by_cases h : meromorphicOrderAt ρ c < 0
    · have hL := (sLocalExplicitTateFactor_poles F S ω ε (fun z ↦ ha z trivial) hne c).mp h
      rw [show meromorphicOrderAt ρ c = _ from
        sLocalExplicitTateFactor_order_eq_neg_count F S ω ε (fun z ↦ ha z trivial) hne hL]
      rfl
    · exact (WithTop.coe_le_coe.mpr (neg_nonpos.mpr (Int.natCast_nonneg _))).trans (not_lt.mp h)
  letI : (productHaar F S μ).IsHaarMeasure :=
    sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  have hgrowth := sLocalTateRatio_overlap_growth F S μ ω εv hεv
  rw [← hε] at hgrowth
  refine ⟨ε, ha, hne, hgrowth.1, hgrowth.2, sLocalPaired_range_of_archPrincipalParts F S μ ν hν ω ρ hρ
    hρ₀ hρbound ?_ ?_ ?_⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨f, rfl⟩ := (sLocalHomogeneousThetaKernel F S ν ω).mkQ_surjective q
    obtain ⟨h₁, h₂⟩ := sLocalPairedBergmanMellin_idelic F S ν ω (productHaar F S μ) hν f
    intro z hz hr
    exact (h₁ z hz).trans ((hstrip f z hz hr).trans (congrArg (ρ z * ·) (h₂ z hr).symm))
  · intro f c hc
    have hNear := (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hc
    have h₂ := (sLocalPairedBergmanMellin_idelic F S ν ω (productHaar F S μ) hν f).2
    apply (hGerm f c).trans
    filter_upwards [nhdsWithin_le_nhds hNear] with z hz
    have hp : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hz
    exact congrArg (ρ z * ·)
      (((sLocalIdelicZeta_meromorphic_continuation F S μ ω⁻¹
        (sLocalSelectedFourier F S f)).2 hp).trans (h₂ z hz).symm)
  · intro p hp ho
    have he : ρ = sLocalExplicitTateFactor F S ω (sLocalTateEpsilonProduct F S ω εv) :=
      congrArg (sLocalExplicitTateFactor F S ω) hε
    have h := And.intro hp ho
    rw [he] at h
    exact (Set.ext_iff.mp hflat p).mpr h

include hν in
/-- The ordinary S-local paired transform is a closed embedding. The
inverse is continuous by open mapping on the homogeneous Fréchet quotient. -/
theorem exists_sLocalOrdinaryPaired_closedEmbedding (ω : PontryaginDual (K F S)) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      let ρ := sLocalExplicitTateFactor F S ω ε
      (∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ ρ z) ∧
      (∀ l r : ℝ, 0 < l → r < 1 →
        ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
          ‖ρ z‖ ≤ C * (1 + |z.im|)^k) ∧
      IsClosedEmbedding (sLocalPairedBergmanMellin F S ν ω) ∧
      range (sLocalPairedBergmanMellin F S ν ω) =
        sLocalBergmanGluing ρ := by
  obtain ⟨ε, ha, hne, hAnalytic, hGrowth, hRange⟩ := exists_sLocalOrdinaryPaired_range F S μ ν hν ω
  let U := sLocalPairedBergmanMellin F S ν ω
  let X := SLocalHomogeneousThetaQuotient F S ν ω
  let Y := U.toLinearMap.range
  let Q := U.rangeRestrict
  have hY : IsClosed (Y : Set B) := by
    change IsClosed (range (sLocalPairedBergmanMellin F S ν ω))
    rw [hRange]
    exact sLocalBergmanGluing_isClosed _
  have hsurj : Surjective Q := fun y ↦ by
    obtain ⟨x,hx⟩ := y.property
    exact ⟨x, Subtype.ext hx⟩
  have hinj : Injective Q := fun _ _ h ↦
    sLocalPairedBergmanMellin_injective F S ν ω (congrArg Subtype.val h)
  obtain ⟨hXa, hXp, hXm, hXc⟩ := sLocalHomogeneousTheta_isFrechet F S ν ω
  letI : IsTopologicalAddGroup X := hXa
  letI : MetrizableSpace X := hXm
  letI : PolynormableSpace ℂ X := hXp
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : @CompleteSpace X (IsTopologicalAddGroup.rightUniformSpace X) := hXc
  obtain ⟨hYa, hYp, hYm, hYc⟩ :=
    isFrechetTVS_closedSubmodule sLocalPairedBergman_frechet Y hY
  letI : IsTopologicalAddGroup Y := hYa
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : MetrizableSpace Y := hYm
  letI : CompleteSpace Y := hYc
  letI : PolynormableSpace ℂ Y := hYp
  letI : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  letI : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
  have hO := isOpenMap_of_surjective_complete_baire Q hsurj
  have he := (IsOpenEmbedding.of_continuous_injective_isOpenMap Q.continuous hinj hO).isEmbedding
  exact ⟨ε, ha, hne, hAnalytic, hGrowth, ⟨IsEmbedding.subtypeVal.comp he, hY⟩, hRange⟩

private def shiftEquiv (d : ℂ) (hd : d.re = 0) : B ≃L[ℂ] B :=
  (schwartzBergmanVerticalShiftEquiv _ isOpen_Ioi ordConnected_Ioi nonempty_Ioi d hd).prodCongr
    (schwartzBergmanVerticalShiftEquiv _ isOpen_Iio ordConnected_Iio nonempty_Iio d hd)

private theorem shiftEquiv_matching_iff (ρ : ℂ → ℂ) (d : ℂ) (hd : d.re = 0) (p : B) :
    shiftEquiv d hd p ∈ sLocalBergmanGluing (fun z ↦ ρ (z+d)) ↔
      p ∈ sLocalBergmanGluing ρ := by
  have hre (z : ℂ) : (z+d).re = z.re := by simp [hd]
  have hre' (z : ℂ) : (z-d).re = z.re := by simp [hd]
  constructor
  · intro h z hz hr
    have he := h (z-d) (by rwa [hre']) (by rwa [hre'])
    change p.1.val (z-d+d) = ρ (z-d+d) * p.2.val (z-d+d) at he
    simpa only [sub_add_cancel] using he
  · intro h z hz hr
    exact h (z+d) (by rwa [hre]) (by rwa [hre])

include hν in
/-- The ordinary closed embedding and exact matching range in any
purely imaginary translate of the canonical coordinate. -/
theorem exists_sLocalOrdinaryPaired_shift_closedEmbedding (ω : PontryaginDual (K F S))
    (d : ℂ) (hd : d.re = 0) :
    ∃ ε : ℂ → ℂ, AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ (sLocalExplicitTateFactor F S ω ε) z) ∧
      (∀ l r : ℝ, 0 < l → r < 1 →
        ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
          ‖sLocalExplicitTateFactor F S ω ε z‖ ≤ C * (1 + |z.im|)^k) ∧
      IsClosedEmbedding (sLocalPairedBergmanMellin_shift F S ν ω d hd) ∧
      range (sLocalPairedBergmanMellin_shift F S ν ω d hd) =
        sLocalBergmanGluing (fun z ↦ sLocalExplicitTateFactor F S ω ε (z+d)) := by
  obtain ⟨ε, ha, hne, hAnalytic, hGrowth, hclosed, hRange⟩ :=
    exists_sLocalOrdinaryPaired_closedEmbedding F S μ ν hν ω
  let U := sLocalPairedBergmanMellin F S ν ω
  let e := shiftEquiv d hd
  let ρ := sLocalExplicitTateFactor F S ω ε
  refine ⟨ε, ha, hne, hAnalytic, hGrowth, e.toHomeomorph.isClosedEmbedding.comp hclosed, ?_⟩
  change range (e ∘ U) = _
  have hU : range U = (sLocalBergmanGluing ρ : Set B) := hRange
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    have hx : U x ∈ range U := ⟨x,rfl⟩
    rw [hU] at hx
    exact (shiftEquiv_matching_iff ρ d hd (U x)).2 hx
  · intro hp
    change p ∈ sLocalBergmanGluing (fun z ↦ ρ (z+d)) at hp
    let q := e.symm p
    have he : e q = p := e.apply_symm_apply p
    have hq : q ∈ range U := by
      rw [hU]
      apply (shiftEquiv_matching_iff ρ d hd q).1
      simpa only [show shiftEquiv d hd q = p from he] using hp
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, (congrArg e hx).trans he⟩

include hν in
/-- The corrected ordinary Second Structure Theorem in every continuous
homomorphic norm section, with the original character on both components. -/
theorem exists_sLocalOrdinaryPaired_for_section (ω : PontryaginDual (K F S))
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t) :
    ∃ (d : ℂ) (hd : d.re = 0) (ε : ℂ → ℂ),
      AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ (z : ℂ) (t : ℝ) (k : K F S),
        sLocalZetaWeight F S ω (z-d) (τ (Multiplicative.ofAdd t) * k.val) =
          Complex.exp (z * (t : ℂ)) * (ω k : ℂ)) ∧
      let U := sLocalPairedBergmanMellin_shift F S ν ω (-d) (by simp [hd])
      IsClosedEmbedding U ∧
      range U = sLocalBergmanGluing (fun z ↦ sLocalExplicitTateFactor F S ω ε (z-d)) ∧
      (∀ (f : E F S) (z : ℂ), 0 < z.re →
        (U (Submodule.Quotient.mk f)).1.val z =
          sLocalIdelicZetaIntegral F S (productHaar F S μ) ω f (z-d)) ∧
      (∀ (f : E F S) (z : ℂ), z.re < 1 →
        (U (Submodule.Quotient.mk f)).2.val z =
          sLocalIdelicZetaIntegral F S (productHaar F S μ) ω⁻¹ (sLocalSelectedFourier F S f) (1-(z-d))) ∧
      (∀ c q, U (sLocalHomogeneousThetaTranslate F S ν ω c q) =
        sLocalPairedTateTranslate F S ω (-d) c (U q)) := by
  obtain ⟨d, hd, hphase⟩ := exists_sLocalSection_phase F S ω τ hτ hmod
  have hd' : (-d).re = 0 := by simp [hd]
  obtain ⟨ε, ha, hn, _, _, hClosed, hRange⟩ :=
    exists_sLocalOrdinaryPaired_shift_closedEmbedding F S μ ν hν ω (-d) hd'
  refine ⟨d, hd, ε, ha, hn, hphase, hClosed, ?_, ?_, ?_, ?_⟩
  · simpa only [← sub_eq_add_neg] using hRange
  · intro f z hz
    letI : (productHaar F S μ).IsHaarMeasure :=
      sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
    have he := (sLocalPairedBergmanMellin_idelic F S ν ω (productHaar F S μ) hν f).1
      (z-d) (by simpa [Complex.sub_re, hd] using hz)
    simpa only [sLocalPairedBergmanMellin_shift_apply, ← sub_eq_add_neg] using he
  · intro f z hz
    letI : (productHaar F S μ).IsHaarMeasure :=
      sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
    have he := (sLocalPairedBergmanMellin_idelic F S ν ω (productHaar F S μ) hν f).2
      (z-d) (by simpa [Complex.sub_re, hd] using hz)
    simpa only [sLocalPairedBergmanMellin_shift_apply, ← sub_eq_add_neg] using he
  · exact sLocalPairedTateTranslate_intertwines F S μ ν ω hν (-d) hd'

end

end Masullo
