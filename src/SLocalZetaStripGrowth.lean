import GammaStripBounds
import SLocalMellinDivisor
import SLocalZetaVerticalSchwartz

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
private abbrev RealPlaces := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlaces := {v : InfinitePlace F // v.IsComplex}

private theorem norm_finiteZetaDenominator_le_two
    (v : HeightOneSpectrum (𝓞 F)) (χ : (v.adicCompletion F)ˣ →ₜ* Circle)
    (z : ℂ) (hz : 0 < z.re) :
    ‖finiteZetaDenominator F v χ z‖ ≤ 2 := by
  have hr : ‖finiteZetaRatio F v χ z‖ ≤ 1 := by
    rw [finiteZetaRatio, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [Complex.neg_re]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz.le)
      (Real.log_nonneg (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le))
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖finiteZetaRatio F v χ z‖ := norm_sub_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

/-- On the positive half-plane, each selected finite denominator has
norm at most two. -/
theorem norm_sLocalFiniteZetaDenominator_le
    (χ : ∀ v : S, (v.val.adicCompletion F)ˣ →ₜ* Circle) (z : ℂ) (hz : 0 < z.re) :
    ‖sLocalFiniteZetaDenominator F S χ z‖ ≤ 2 ^ S.card := by
  unfold sLocalFiniteZetaDenominator
  rw [norm_prod]
  calc
    _ ≤ ∏ _v : S, (2 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
      intro v _
      split_ifs
      · exact norm_finiteZetaDenominator_le_two F v.val (χ v) z hz
      · norm_num
    _ = _ := by simp

/-- The reciprocal S-local Euler product has exponential rate π/4 for
each real place and π/2 for each complex place on positive strips. -/
theorem sLocalEulerDenominator_norm_le_on_strip
    (χ : PontryaginDual (SLocalThetaNormOne F S)) (a b : ℝ) (ha : 0 < a) :
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖sLocalEulerDenominator F S χ z‖ ≤ C *
        (1 + |z.im|) ^ (Fintype.card (RealPlaces F) + Fintype.card (ComplexPlaces F)) *
        Real.exp (Real.pi * ((Fintype.card (RealPlaces F) : ℝ) / 4 +
          (Fintype.card (ComplexPlaces F) : ℝ) / 2) * |z.im|) := by
  let A := sLocalRealArchParameters F S χ
  let J := sLocalComplexArchParameters F S χ
  let wR (v : RealPlaces F) := (A v).1 + (((A v).2 % 2 : ℕ) : ℂ)
  let wC (v : ComplexPlaces F) := (J v).1 + (((J v).2.natAbs : ℕ) : ℂ) / 2
  choose CR hCR hR using fun v : RealPlaces F ↦
    exists_norm_inv_GammaReal_add_le_on_strip a b ha (wR v) (by
      simp only [wR, A, Complex.add_re, sLocalRealArchParameters_re, zero_add, Complex.natCast_re]
      positivity)
  choose CC hCC hC using fun v : ComplexPlaces F ↦
    exists_norm_inv_GammaComplex_add_le_on_strip a b ha (wC v) (by
      simp only [wC, J, Complex.add_re, sLocalComplexArchParameters_re, zero_add,
        Complex.div_ofNat_re, Complex.natCast_re]
      positivity)
  let R := Fintype.card (RealPlaces F)
  let T := Fintype.card (ComplexPlaces F)
  refine ⟨(∏ v, CR v) * (∏ v, CC v) * (2 : ℝ) ^ S.card,
    mul_pos (mul_pos (Finset.prod_pos fun v _ ↦ hCR v) (Finset.prod_pos fun v _ ↦ hCC v))
      (by positivity), fun z hz ↦ ?_⟩
  let u : ℝ := 1 + |z.im|
  let r := Real.exp (Real.pi * |z.im| / 4)
  let t := Real.exp (Real.pi * |z.im| / 2)
  have hr : ‖∏ v : RealPlaces F, realArchZetaDenominator (A v).2 (z + (A v).1)‖ ≤
      (∏ v, CR v) * (u * r) ^ R := by
    have he : (u * r) ^ R = ∏ _v : RealPlaces F, u * r := by simp [R]
    rw [norm_prod, he, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun v _ ↦ by
      simpa only [realArchZetaDenominator, wR, add_assoc] using hR v z hz
  have ht : ‖∏ v : ComplexPlaces F, complexArchZetaDenominator (J v).2 (z + (J v).1)‖ ≤
      (∏ v, CC v) * (u * t) ^ T := by
    have he : (u * t) ^ T = ∏ _v : ComplexPlaces F, u * t := by simp [T]
    rw [norm_prod, he, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun v _ ↦ by
      simpa only [complexArchZetaDenominator, wC, add_assoc] using hC v z hz
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hrr : 0 ≤ (∏ v, CR v) * (u * r) ^ R :=
    mul_nonneg (Finset.prod_nonneg fun v _ ↦ (hCR v).le)
      (pow_nonneg (mul_nonneg hu (Real.exp_pos _).le) _)
  have htt : 0 ≤ (∏ v, CC v) * (u * t) ^ T :=
    mul_nonneg (Finset.prod_nonneg fun v _ ↦ (hCC v).le)
      (pow_nonneg (mul_nonneg hu (Real.exp_pos _).le) _)
  unfold sLocalEulerDenominator archimedeanNumberFieldZetaDenominator
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ((∏ v, CR v) * (u * r) ^ R) * ((∏ v, CC v) * (u * t) ^ T) * 2 ^ S.card := by
      exact mul_le_mul
        (mul_le_mul hr ht (norm_nonneg _) hrr)
        (norm_sLocalFiniteZetaDenominator_le F S _ z (ha.trans_le hz.1)) (norm_nonneg _) (mul_nonneg hrr htt)
    _ = _ := by
      rw [mul_pow, mul_pow]
      have he : r ^ R * t ^ T =
          Real.exp (Real.pi * ((R : ℝ) / 4 + (T : ℝ) / 2) * |z.im|) := by
        dsimp only [r, t]
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      have hsum : u ^ R * u ^ T = u ^ (R + T) := (pow_add _ _ _).symm
      change _ = _ * u ^ (R + T) * _
      rw [← he, ← hsum]
      ring

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
attribute [local instance] sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

/-- Clearing the Euler poles preserves arbitrary polynomial decay after
allowing the exponential rate of the reciprocal archimedean factors. -/
theorem sLocalIdelicZeta_normalized_strip_growth
    (μ : Measure (SAdeles F S)ˣ) [μ.IsHaarMeasure]
    (χ : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S)
    (a b : ℝ) (ha : 0 < a) (N : ℕ) :
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| →
      |z.im| ^ N * ‖sLocalEulerDenominator F S χ z * sLocalIdelicZetaIntegral F S μ χ f z‖ ≤
        C * Real.exp (Real.pi * ((Fintype.card (RealPlaces F) : ℝ) / 4 +
          (Fintype.card (ComplexPlaces F) : ℝ) / 2) * |z.im|) := by
  obtain ⟨D, hD, hDz⟩ := sLocalEulerDenominator_norm_le_on_strip F S χ a b ha
  obtain ⟨g, hg, hgval⟩ := sLocalIdelicZeta_vertical_schwartz F S μ χ f a b ha
  let n := Fintype.card (RealPlaces F) + Fintype.card (ComplexPlaces F)
  obtain ⟨B, hB, hBk⟩ :=
    (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hg (N + n, 0)
  refine ⟨D * 2 ^ n * B, by positivity, fun z hz ht ↦ ?_⟩
  let σ : Icc a b := ⟨z.re, hz⟩
  let x := |z.im|
  let E := Real.exp (Real.pi * ((Fintype.card (RealPlaces F) : ℝ) / 4 +
    (Fintype.card (ComplexPlaces F) : ℝ) / 2) * x)
  have he : (⟨σ.val, z.im⟩ : ℂ) = z := Complex.ext rfl rfl
  have hZ : x ^ (N + n) * ‖sLocalIdelicZetaIntegral F S μ χ f z‖ ≤ B := by
    have hs := (SchwartzMap.le_seminorm' ℂ (N + n) 0 (g σ) z.im).trans
      ((hBk (g σ) (mem_range_self σ)).le)
    simpa only [iteratedDeriv_zero, hgval σ z.im, he] using hs
  have hx : 0 ≤ x := abs_nonneg _
  have hp : (1 + x) ^ n ≤ 2 ^ n * x ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by dsimp [x] at ht ⊢; linarith) _
  have hD' : ‖sLocalEulerDenominator F S χ z‖ ≤ D * (2 ^ n * x ^ n) * E :=
    (hDz z hz).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hD.le) (Real.exp_pos _).le)
  rw [norm_mul]
  calc
    _ ≤ x ^ N * ((D * (2 ^ n * x ^ n) * E) * ‖sLocalIdelicZetaIntegral F S μ χ f z‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD' (norm_nonneg _)) (pow_nonneg hx _)
    _ = (D * 2 ^ n * E) * (x ^ (N + n) * ‖sLocalIdelicZetaIntegral F S μ χ f z‖) := by
      rw [pow_add]
      ring
    _ ≤ (D * 2 ^ n * E) * B := mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = _ := by dsimp [E, x]; ring

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]

/-- The Euler-normalized continuation is entire and satisfies the strip
estimate of Lemma 3.3.1.7(2), with absolute height in the exponential. -/
theorem sLocalNormalizedZeta_entire_and_strip_growth
    (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
    [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
    (χ : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S) :
    let Z := sLocalProductZetaContinued F S μ χ (sLocalRealArchParameters F S χ)
      (sLocalComplexArchParameters F S χ) f
    let W := toMeromorphicNFOn (fun z ↦ sLocalEulerDenominator F S χ z * Z z) univ
    AnalyticOnNhd ℂ W univ ∧ ∀ (a b : ℝ), 0 < a → ∀ N : ℕ,
      ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| →
        |z.im| ^ N * ‖W z‖ ≤ C *
          Real.exp (Real.pi * ((Fintype.card (RealPlaces F) : ℝ) / 4 +
            (Fintype.card (ComplexPlaces F) : ℝ) / 2) * |z.im|) := by
  intro Z W
  refine ⟨sLocalEulerDenominator_mul_zeta_entire F S μ χ f, fun a b ha N ↦ ?_⟩
  letI : MeasurableSpace (InfiniteAdeleRing F)ˣ := borel _
  letI : BorelSpace (InfiniteAdeleRing F)ˣ := ⟨rfl⟩
  let η := sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)
  letI : η.IsHaarMeasure := sLocalZetaProductMeasure_isHaar F S μ (archimedeanMultiplicativeHaar F)
  obtain ⟨C, hC, hbound⟩ := sLocalIdelicZeta_normalized_strip_growth F S η χ f a b ha N
  have hZ : Meromorphic Z ∧ EqOn Z (sLocalIdelicZetaIntegral F S η χ f) {z | 0 < z.re} :=
    sLocalIdelicZeta_meromorphic_continuation F S μ χ f
  let D := sLocalEulerDenominator F S χ
  let P (z : ℂ) := D z * Z z
  have hP : MeromorphicOn P univ :=
    fun z _ ↦ (sLocalEulerDenominator_analytic F S χ z).meromorphicAt.mul (hZ.1 z)
  refine ⟨C, hC, fun z hz ht ↦ ?_⟩
  have hpos : 0 < z.re := ha.trans_le hz.1
  have hZan : AnalyticAt ℂ Z z := by
    apply (sLocalIdelicZeta_analytic F S η χ f z hpos).congr
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with w hw
    exact (hZ.2 hw).symm
  have hPan : AnalyticAt ℂ P z := (sLocalEulerDenominator_analytic F S χ z).mul hZan
  have he : W z = D z * sLocalIdelicZetaIntegral F S η χ f z := by
    change toMeromorphicNFOn P univ z = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hP (mem_univ z),
      toMeromorphicNFAt_eq_self.2 hPan.meromorphicNFAt]
    exact congrArg (D z * ·) (hZ.2 hpos)
  rw [he]
  exact hbound z hz ht

/-- The absolute-height version of the power in (3.3.1.27), with its
varying real part across the strip. -/
theorem sLocalNormalizedZeta_printed_strip_power
    (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
    [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
    (χ : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S)
    (a b : ℝ) (ha : 0 < a) (N : ℕ) :
    let Z := sLocalProductZetaContinued F S μ χ (sLocalRealArchParameters F S χ)
      (sLocalComplexArchParameters F S χ) f
    let W := toMeromorphicNFOn (fun z ↦ sLocalEulerDenominator F S χ z * Z z) univ
    let k : ℝ := (Fintype.card (RealPlaces F) : ℝ) / 2 + (Fintype.card (ComplexPlaces F) : ℝ)
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b → 1 ≤ |z.im| →
      ‖W z‖ ≤ C * |z.im| ^ (-((N : ℝ) + (z.re - 1 / 2) * k)) *
        Real.exp (Real.pi * k * |z.im| / 2) := by
  intro Z W k
  obtain ⟨m, hm⟩ := exists_nat_gt ((b - 1 / 2) * k)
  have h := (sLocalNormalizedZeta_entire_and_strip_growth F S μ χ f).2 a b ha (N + m)
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun z hz ht ↦ ?_⟩
  let x := |z.im|
  have hx : 0 < x := zero_lt_one.trans_le ht
  let e := Real.exp (Real.pi * k * x / 2)
  have heq :
      Real.exp (Real.pi * ((Fintype.card (RealPlaces F) : ℝ) / 4 +
        (Fintype.card (ComplexPlaces F) : ℝ) / 2) * x) = e := by
    congr 1
    dsimp only [k]
    ring
  have hxW : x ^ (N + m) * ‖W z‖ ≤ C * e := by rw [← heq]; exact hb z hz ht
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hpower : (z.re - 1 / 2) * k ≤ m :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_right hz.2 _) hk).trans hm.le
  have h₀ : ‖W z‖ ≤ C * e / x ^ (N + m) :=
    (le_div_iff₀ (pow_pos hx _)).2 (by simpa only [mul_comm] using hxW)
  calc
    _ ≤ C * x ^ (-((N : ℝ) + (m : ℝ))) * e := by
      rw [div_eq_mul_inv, ← Real.rpow_natCast, Nat.cast_add, ← Real.rpow_neg hx.le] at h₀
      simpa only [mul_assoc, mul_comm e] using h₀
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) hC.le) (Real.exp_pos _).le

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ] in
/-- Every unitary character of the full S-idele class group is the canonical
norm-one character times an imaginary radial twist. -/
theorem sLocalZetaWeight_unitary_shift
    (χ : QuasiCharacter (SIdeleQuotient F S)) (hχ : ∀ q, ‖χ q‖ = 1) :
    ∃ (ω : PontryaginDual (SLocalThetaNormOne F S)) (τ : ℝ),
      ∀ (z : ℂ) (q : SIdeleQuotient F S),
        χ q * Complex.exp (z * ((sLocalZetaSplit F S).symm q).1) =
          sLocalZetaWeight F S ω (z + (τ : ℂ) * Complex.I) q := by
  obtain ⟨ω, a, ha, -⟩ := sLocalZetaWeight_represents F S χ
  have hr : a.re = 0 := by
    have h := hχ (sLocalZetaSplit F S (1, 1))
    rw [ha, sLocalZetaWeight_split, Complex.ofReal_one, mul_one, map_one, Circle.coe_one,
      mul_one, Complex.norm_exp, ← Real.exp_zero, Real.exp_eq_exp] at h
    exact h
  have hAI : a = (a.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using hr
    · simp
  refine ⟨ω, a.im, fun z q ↦ ?_⟩
  rw [ha, ← hAI]
  obtain ⟨⟨t, k⟩, rfl⟩ := (sLocalZetaSplit F S).surjective q
  rw [Homeomorph.symm_apply_apply]
  simp only [sLocalZetaWeight_split, add_mul, Complex.exp_add]
  ring

/-- Imaginary reparametrization of a unitary component preserves the strip
estimate with the same exponential rate and power in the new height. -/
theorem sLocalNormalizedZeta_shifted_strip_power
    (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
    [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
    (χ : PontryaginDual (SLocalThetaNormOne F S)) (f : sLocalBruhatImage F S)
    (τ a b : ℝ) (ha : 0 < a) (N : ℕ) :
    let Z := sLocalProductZetaContinued F S μ χ (sLocalRealArchParameters F S χ)
      (sLocalComplexArchParameters F S χ) f
    let W := toMeromorphicNFOn (fun z ↦ sLocalEulerDenominator F S χ z * Z z) univ
    let k : ℝ := (Fintype.card (RealPlaces F) : ℝ) / 2 + (Fintype.card (ComplexPlaces F) : ℝ)
    AnalyticOnNhd ℂ (fun z ↦ W (z + (τ : ℂ) * Complex.I)) univ ∧
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Icc a b → max 2 (2 * |τ|) ≤ |z.im| →
      ‖W (z + (τ : ℂ) * Complex.I)‖ ≤ C * |z.im| ^ (-((N : ℝ) + (z.re - 1 / 2) * k)) *
        Real.exp (Real.pi * k * |z.im| / 2) := by
  intro Z W k
  let l := Real.pi * k / 2
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hl : 0 ≤ l := by dsimp only [l]; positivity [Real.pi_pos]
  obtain ⟨m, hm⟩ := exists_nat_gt ((b - 1 / 2) * k)
  let p := N + m
  obtain ⟨han, hstrip⟩ := sLocalNormalizedZeta_entire_and_strip_growth F S μ χ f
  obtain ⟨C, hC, hbound⟩ := hstrip a b ha p
  have han' : AnalyticOnNhd ℂ (fun z ↦ W (z + (τ : ℂ) * Complex.I)) univ := by
    intro z _
    have hs : AnalyticAt ℂ (fun t : ℂ ↦ t + (τ : ℂ) * Complex.I) z :=
      analyticAt_id.add analyticAt_const
    exact AnalyticAt.comp (g := W) (f := fun t : ℂ ↦ t + (τ : ℂ) * Complex.I) (x := z)
      (han (z + (τ : ℂ) * Complex.I) trivial) hs
  refine ⟨han', C * (2 : ℝ) ^ p * Real.exp (l * |τ|), by positivity, ?_⟩
  intro z hz ht
  let w := z + (τ : ℂ) * Complex.I
  let t := |z.im|
  let u := |w.im|
  have hwr : w.re = z.re := by simp [w]
  have hwi : w.im = z.im + τ := by simp [w]
  have htu : t ≤ 2 * u := by
    have h₁ : t ≤ u + |τ| := by
      have he : w.im + -τ = z.im := by rw [hwi]; ring
      simpa only [t, u, he, abs_neg] using abs_add_le w.im (-τ)
    have h₂ : 2 * |τ| ≤ t := le_trans (le_max_right _ _) ht
    linarith
  have h₁ : 1 ≤ u := by
    have := le_trans (le_max_left 2 (2 * |τ|)) ht
    linarith
  have ht₁ : 1 ≤ t := (by norm_num : (1 : ℝ) ≤ 2).trans (le_trans (le_max_left _ _) ht)
  have ht₀ : 0 < t := zero_lt_one.trans_le ht₁
  have hupper : u ≤ t + |τ| := by
    change |w.im| ≤ _
    rw [hwi]
    exact abs_add_le _ _
  have hb := hbound w (hwr ▸ hz) h₁
  have hE : Real.pi * ((Fintype.card (RealPlaces F) : ℝ) / 4 +
      (Fintype.card (ComplexPlaces F) : ℝ) / 2) * u = l * u := by
    dsimp only [l, k]
    ring
  rw [hE] at hb
  have hmain : t ^ p * ‖W w‖ ≤ C * (2 : ℝ) ^ p * Real.exp (l * |τ|) * Real.exp (l * t) := by
    have hp : t ^ p ≤ (2 * u) ^ p := pow_le_pow_left₀ (abs_nonneg _) htu _
    have hB : Real.exp (l * u) ≤ Real.exp (l * (t + |τ|)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hupper hl)
    calc
      _ ≤ (2 * u) ^ p * ‖W w‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = (2 : ℝ) ^ p * (u ^ p * ‖W w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ (2 : ℝ) ^ p * (C * Real.exp (l * (t + |τ|))) :=
        mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hB hC.le)) (by positivity)
      _ = _ := by rw [mul_add, Real.exp_add]; ring
  have hpow : (z.re - 1 / 2) * k ≤ m :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_right hz.2 _) hk).trans hm.le
  have hd : ‖W w‖ ≤ (C * 2 ^ p * Real.exp (l * |τ|) * Real.exp (l * t)) / t ^ p := by
    apply (le_div_iff₀ (pow_pos ht₀ p)).mpr
    rw [mul_comm]
    exact hmain
  change ‖W w‖ ≤ C * 2 ^ p * Real.exp (l * |τ|) *
    t ^ (-((N : ℝ) + (z.re - 1 / 2) * k)) * Real.exp (Real.pi * k * t / 2)
  have hl' : Real.pi * k * t / 2 = l * t := by dsimp only [l]; ring
  rw [hl']
  calc
    _ ≤ C * 2 ^ p * Real.exp (l * |τ|) * t ^ (-((N : ℝ) + (m : ℝ))) * Real.exp (l * t) := by
      have hrpow : (t ^ p)⁻¹ = t ^ (-((N : ℝ) + (m : ℝ))) := by
        rw [← Real.rpow_natCast t p, ← Real.rpow_neg ht₀.le]
        simp [p]
      rw [div_eq_mul_inv, hrpow] at hd
      simpa only [mul_assoc, mul_comm (Real.exp (l * t))] using hd
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le ht₁ (by linarith)) (by positivity)) (Real.exp_pos _).le

end

end Masullo
