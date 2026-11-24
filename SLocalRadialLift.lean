import ArchimedeanRadialMoments
import SLocalArchSchwartzDilation
import SLocalFlatMultiplication

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ContDiff NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev G := (SAdeles F S)ˣ
private abbrev Arch := mixedEmbedding.mixedSpace F
private abbrev Test := sLocalBruhatImage F S
private abbrev L (v : S) := v.val.adicCompletion F

private theorem exists_finiteShellCutoff (v : S) :
    ∃ g : locallyConstantTests (L F S v), g.val 0 = 0 ∧ g.val 1 = 1 ∧
      (∀ x, ∃ a : ℝ, 0 ≤ a ∧ g.val x = (a : ℂ)) ∧
      (∀ x, g.val x ≠ 0 → ‖x‖ = 1) := by
  let B := Metric.ball (1 : L F S v) 1
  have hK : IsCompact (Metric.closedBall (1 : L F S v) 1) := by
    rw [IsUltrametricDist.closedBall_eq_of_mem
      (show (0 : L F S v) ∈ Metric.closedBall (1 : L F S v) 1 by simp), finiteCompletion_closedBall]
    exact finitePlaceIntegral_compact F v.val
  have hB : IsCompact B := hK.of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
    Metric.ball_subset_closedBall
  let g := compactOpenIndicator (L F S v) ⟨B, hB, Metric.isOpen_ball⟩
  have hg (x : L F S v) : g.val x = B.indicator (fun _ ↦ (1 : ℂ)) x := rfl
  have hB0 : (0 : L F S v) ∉ B := by simp [B]
  refine ⟨g, by rw [hg, indicator_of_notMem hB0], by rw [hg, indicator_of_mem (Metric.mem_ball_self one_pos)], ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ B
    · exact ⟨1, zero_le_one, by rw [hg, indicator_of_mem hx, Complex.ofReal_one]⟩
    · exact ⟨0, le_rfl, by rw [hg, indicator_of_notMem hx, Complex.ofReal_zero]⟩
  · intro x hx
    have he : x ∈ B := by
      by_contra h
      apply hx
      rw [hg, indicator_of_notMem h]
    have hdist : dist (1 : L F S v) 0 = 1 := by simp
    have hsmall : dist x 1 < 1 := he
    rw [← dist_zero_right, IsUltrametricDist.dist_eq_max_of_dist_ne_dist x 1 0
      (hsmall.ne.trans_eq hdist.symm), hdist, max_eq_right hsmall.le]

private theorem ideleNorm_arch_mul_finite (u : G F S) :
    sLocalIdeleNorm F S u = archModulus F (InfiniteAdeleRing.ringEquiv_mixedSpace F u.val.1) *
      ∏ v : S, ‖u.val.2 v‖ := by
  obtain ⟨p, rfl⟩ := (sLocalZetaIdeleCoordinates F S).symm.surjective u
  rw [sLocalZetaIdeleCoordinates_norm]
  change _ = archModulus F (InfiniteAdeleRing.ringEquiv_mixedSpace F p.1.val) *
    ∏ v : S, ‖(p.2 v).val‖
  rw [archModulus_of_infiniteAdele, InfiniteAdeleRing.norm_def]

/-- The analytic lifting step for Lemma 5.3.4.3. A fixed nonnegative
norm-ray-invariant cutoff on the multiplicative S-adeles realizes every
all-exponent radial profile by a polar-free additive test. -/
theorem exists_sLocalPolarFree_radialLiftCLM_on_ideles_fixedSupport :
    ∃ b : G F S → ℂ, b 1 = 1 ∧ (∀ u, ∃ a : ℝ, 0 ≤ a ∧ b u = (a : ℂ)) ∧
      (∀ t : ℝ, ∀ u : G F S, b (sLocalExpSection F S (Multiplicative.ofAdd t) * u) = b u) ∧
      ∃ L : PositiveRealExponentialDecay univ →L[ℂ] sLocalPolarFreeTestSubspace F S,
        (∀ f (u : G F S), sLocalBruhatRestriction F S (L f).val.val u.val =
          b u * f.val (Real.log (sLocalIdeleNorm F S u))) ∧
        (∀ a b : ℝ, ∃ C : Set (SAdeles F S), IsCompact C ∧
          ∀ f, support f.val ⊆ Icc a b →
            tsupport (sLocalBruhatRestriction F S (L f).val.val) ⊆ C) ∧
        ∀ f, logProfileExponentialMoment f.val = 0 →
          GlobalBruhat.polarEvaluation F (L f).val.val = 0 := by
  obtain ⟨ψ, hψ, hK, hψ1, hψpos⟩ := exists_archimedeanRadialCutoff F
  choose g h0 h1 hpos hnorm using fun v : S ↦ exists_finiteShellCutoff F S v
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q (x : Arch F) := (archModulusRadius F x)⁻¹ • x
  let b (u : G F S) : ℂ := ψ (q (e u.val.1)) * ∏ v : S, (g v).val (u.val.2 v)
  have hq (r : ℝ) (hr : 0 < r) (x : Arch F) : q (r • x) = q x := by
    unfold q
    rw [archModulusRadius_smul F r hr, mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · have hR : archModulusRadius F 1 = 1 := by simp [archModulusRadius, archModulus]
    change ψ (q (e 1)) * ∏ v : S, (g v).val 1 = 1
    rw [map_one]
    simp only [q, hR, inv_one, one_smul, hψ1, h1, Finset.prod_const_one, mul_one]
  · intro u
    obtain ⟨a, ha, ha'⟩ := hψpos (q (e u.val.1))
    choose c hc he using fun v : S ↦ hpos v (u.val.2 v)
    refine ⟨a * ∏ v : S, c v, mul_nonneg ha (Finset.prod_nonneg fun v _ ↦ hc v), ?_⟩
    dsimp [b]
    simp_rw [ha', he, Complex.ofReal_mul, Complex.ofReal_prod]
  · intro t u
    have hi : (sLocalExpSection F S (Multiplicative.ofAdd (-t))).inv =
        (sLocalExpSection F S (Multiplicative.ofAdd t)).val := by
      change ((sLocalExpSection F S (Multiplicative.ofAdd t)⁻¹)⁻¹).val = _
      rw [map_inv, inv_inv]
    have h := sLocalExpSection_inv_mul_components F S (-t) u.val
    rw [hi, neg_neg] at h
    change ψ (q (e (((sLocalExpSection F S (Multiplicative.ofAdd t)).val * u.val).1))) *
      (∏ v : S, (g v).val (((sLocalExpSection F S (Multiplicative.ofAdd t)).val * u.val).2 v)) = b u
    rw [h.1, h.2, hq _ (Real.exp_pos _) _]
  · obtain ⟨Q, hQ, he⟩ := exists_archimedeanFlat_logRadius_liftCLM F ψ hψ hK
    let ψ₀ := locallyConstantTestPiProduct g
    let L₁ : 𝓢(Arch F, ℂ) →L[ℂ] Test F S :=
      ⟨(sLocalBruhatPure F S).flip ψ₀, (GlobalBruhat.pure_continuous F _).subtype_mk _⟩
    let L₂ := L₁.comp Q
    have hL (f : PositiveRealExponentialDecay univ) :
        L₂ f ∈ sLocalPolarFreeTestSubspace F S :=
      (sLocalPolarFreePure F S ⟨Q f, hQ f⟩ g h0).property
    let L := L₂.codRestrict (sLocalPolarFreeTestSubspace F S) hL
    refine ⟨L, fun f u ↦ ?_, fun a b' ↦ ?_, fun f hf ↦ ?_⟩
    · change sLocalBruhatRestriction F S (sLocalBruhatPure F S (Q f) ψ₀).val u.val = _
      rw [sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply, he]
      let A := ∏ v : S, (g v).val (u.val.2 v)
      by_cases hA : A = 0
      · change (_ * _) * A = (_ * A) * _
        rw [hA, mul_zero, mul_zero, zero_mul]
      · have hqv (v : S) : ‖u.val.2 v‖ = 1 :=
          hnorm v _ (fun h ↦ hA (Finset.prod_eq_zero (Finset.mem_univ v) h))
        have hu : sLocalIdeleNorm F S u = archModulus F (e u.val.1) := by
          rw [ideleNorm_arch_mul_finite]
          simp_rw [hqv, Finset.prod_const_one, mul_one]
          rfl
        rw [hu]
        change (_ * _) * A = (_ * A) * _
        ring
    · obtain ⟨C, hC, _, hCcover⟩ := archimedeanLogRadius_fixedSupport F ψ hψ hK a b'
      letI : T2Space (InfiniteAdeleRing F) :=
        (infiniteAdeleMixedHomeomorph F).isEmbedding.t2Space
      let Carch := (infiniteAdeleMixedHomeomorph F).symm '' C
      have hCarch : IsCompact Carch := hC.image (infiniteAdeleMixedHomeomorph F).symm.continuous
      let D := Carch ×ˢ tsupport ψ₀.val
      have hD : IsCompact D := hCarch.prod ψ₀.property.2
      refine ⟨D, hD, fun f hf ↦ closure_minimal ?_ hD.isClosed⟩
      intro x hx
      change sLocalBruhatRestriction F S (sLocalBruhatPure F S (Q f) ψ₀).val x ≠ 0 at hx
      rw [sLocalBruhatPure_restrict, mul_ne_zero_iff] at hx
      exact ⟨⟨e x.1, hCcover f.val (Q f) (he f) hf (subset_closure hx.1),
        (infiniteAdeleMixedHomeomorph F).symm_apply_apply x.1⟩, subset_closure hx.2⟩
    · have hψ₀ : ψ 0 = 0 := notMem_support.mp fun h ↦ by
        have hh : 0 < archModulus F (0 : Arch F) := hK (subset_closure h)
        rw [archModulus_zero] at hh
        exact (lt_irrefl 0) hh
      have hQ₀ : Q f 0 = 0 := by rw [he, smul_zero, hψ₀, zero_mul]
      let z := positiveRealExponentialDecay_zeroInclusion (univ : Set ℝ) (mem_univ 0) f
      have hz : (z : ℝ → ℂ) = f.val :=
        funext (positiveRealExponentialDecay_zeroInclusion_apply univ (mem_univ 0) f)
      have hm : Measurable f.val := hz ▸ z.continuous.measurable
      obtain ⟨c, hc⟩ := exists_archimedeanLogRadius_integral_eq_moment F ψ hψ hK hψpos
      have hIntegral : (∫ x : Arch F, Q f x) = 0 := by
        simp_rw [he]
        rw [hc f.val hm, hf, mul_zero]
      apply Prod.ext
      · change (Q f) (e 0) * (insertFinite F S ψ₀).toLocallyConstant 0 = 0
        rw [map_zero, hQ₀, zero_mul]
      · exact globalBruhatFourier_pure_zero_of_archIntegral_zero F (insertFinite F S ψ₀) (Q f) hIntegral

theorem exists_sLocalPolarFree_radialLiftCLM_on_ideles :
    ∃ b : G F S → ℂ, b 1 = 1 ∧ (∀ u, ∃ a : ℝ, 0 ≤ a ∧ b u = (a : ℂ)) ∧
      (∀ t : ℝ, ∀ u : G F S, b (sLocalExpSection F S (Multiplicative.ofAdd t) * u) = b u) ∧
      ∃ L : PositiveRealExponentialDecay univ →L[ℂ] sLocalPolarFreeTestSubspace F S,
        ∀ f (u : G F S), sLocalBruhatRestriction F S (L f).val.val u.val =
          b u * f.val (Real.log (sLocalIdeleNorm F S u)) := by
  obtain ⟨b, h₁, hp, ht, L, hL, _, _⟩ := exists_sLocalPolarFree_radialLiftCLM_on_ideles_fixedSupport F S
  exact ⟨b, h₁, hp, ht, L, hL⟩

theorem exists_sLocalPolarFree_radialLift_on_ideles :
    ∃ b : G F S → ℂ, b 1 = 1 ∧ (∀ u, ∃ a : ℝ, 0 ≤ a ∧ b u = (a : ℂ)) ∧
      (∀ t : ℝ, ∀ u : G F S, b (sLocalExpSection F S (Multiplicative.ofAdd t) * u) = b u) ∧
      ∀ f : PositiveRealExponentialDecay univ, ∃ g : sLocalPolarFreeTestSubspace F S,
        ∀ u : G F S, sLocalBruhatRestriction F S g.val.val u.val =
          b u * f.val (Real.log (sLocalIdeleNorm F S u)) := by
  obtain ⟨b, h₁, hp, ht, L, hL⟩ := exists_sLocalPolarFree_radialLiftCLM_on_ideles F S
  exact ⟨b, h₁, hp, ht, fun f ↦ ⟨L f, hL f⟩⟩

private abbrev K := SLocalThetaNormOne F S
private abbrev Orbit := Additive (sIntegerRing F S)ˣ

private def radialReferenceBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

private def radialReferenceProfile : PositiveRealExponentialDecay univ := by
  let f (x : ℝ) : ℂ := radialReferenceBump x
  have hK : HasCompactSupport f := by
    change HasCompactSupport (Complex.ofReal ∘ (radialReferenceBump : ℝ → ℝ))
    exact radialReferenceBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp radialReferenceBump.contDiff
  exact ⟨f, mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hK hf⟩

private theorem radialReferenceProfile_zero : radialReferenceProfile.val 0 = 1 := by
  change (radialReferenceBump 0 : ℂ) = 1
  rw [radialReferenceBump.one_of_mem_closedBall (Metric.mem_closedBall_self radialReferenceBump.rIn_pos.le),
    Complex.ofReal_one]

private theorem sLocalOrbit_norm (v : Orbit F S) :
    sLocalIdeleNorm F S (sUnitOrbitEquiv F S v).val = 1 := by
  exact (sPrincipalLocalNormOne F S v.toMul).property

private theorem sLocal_normOne_lift_norm (k : K F S) (u : G F S)
    (hu : (QuotientGroup.mk u : SIdeleQuotient F S) = k.val) : sLocalIdeleNorm F S u = 1 := by
  rw [← sLocalClassModulus_mk, hu]
  have hk : sQuotientNorm F S k.val = 1 := k.property
  simp [sLocalClassModulus, hk]

private theorem theta_normOne_reference_nonneg
    (b : G F S → ℂ) (hb : ∀ u, ∃ a : ℝ, 0 ≤ a ∧ b u = (a : ℂ))
    (f : Test F S) (hf : ∀ u : G F S, sLocalIdeleNorm F S u = 1 →
      sLocalBruhatRestriction F S f.val u.val = b u)
    (u : G F S) (hu : sLocalIdeleNorm F S u = 1) :
    0 ≤ (sLocalTheta F S (sLocalBruhatRestriction F S f.val) (QuotientGroup.mk u)).re := by
  rw [sLocalTheta_mk]
  unfold sLocalThetaOnIdeles
  rw [Complex.re_tsum (sLocalTheta_restriction_summable F S f.val u).of_norm]
  apply tsum_nonneg
  intro v
  let e := (sUnitOrbitEquiv F S v).val
  have hn : sLocalIdeleNorm F S (e * u) = 1 := by rw [map_mul, sLocalOrbit_norm, hu, mul_one]
  rw [← sUnitOrbitEquiv_val F S v]
  change 0 ≤ (sLocalBruhatRestriction F S f.val (e*u).val).re
  rw [hf _ hn]
  obtain ⟨c, hc, he⟩ := hb (e*u)
  simpa [he] using hc

private theorem theta_normOne_reference_at_one
    (b : G F S → ℂ) (hb₁ : b 1 = 1) (hb : ∀ u, ∃ a : ℝ, 0 ≤ a ∧ b u = (a : ℂ))
    (f : Test F S) (hf : ∀ u : G F S, sLocalIdeleNorm F S u = 1 →
      sLocalBruhatRestriction F S f.val u.val = b u) :
    0 < (sLocalTheta F S (sLocalBruhatRestriction F S f.val) (1 : SIdeleQuotient F S)).re := by
  rw [← QuotientGroup.mk_one, sLocalTheta_mk]
  unfold sLocalThetaOnIdeles
  have hs := (sLocalTheta_restriction_summable F S f.val 1).of_norm
  rw [Complex.re_tsum hs]
  apply (Complex.reCLM.summable hs).tsum_pos _ (Additive.ofMul 1)
  · change 0 < (sLocalBruhatRestriction F S f.val
      (sIntegerDiagonal F S (1 : sIntegerRing F S) * (1 : G F S).val)).re
    have he : sIntegerDiagonal F S (1 : sIntegerRing F S) = 1 :=
      (sAdelesDiagonal F S).map_one
    rw [he, one_mul, hf 1 (map_one _), hb₁]
    norm_num
  · intro v
    let e := (sUnitOrbitEquiv F S v).val
    rw [← sUnitOrbitEquiv_val F S v]
    change 0 ≤ (sLocalBruhatRestriction F S f.val (e*1).val).re
    rw [mul_one, hf _ (sLocalOrbit_norm F S v)]
    obtain ⟨c, hc, he⟩ := hb e
    change 0 ≤ (b e).re
    rwa [he, Complex.ofReal_re]

variable [MeasurableSpace (K F S)] [BorelSpace (K F S)]

set_option maxHeartbeats 800000 in
/-- Lemma 5.3.4.3. Every all-exponent logarithmic Schwartz profile is the
trivial homogeneous theta function of an actual flat S-local test. -/
theorem exists_sLocalHomogeneousTheta_trivial_polarFreeCLM_fixedSupport
    (ν : Measure (K F S)) [ν.IsHaarMeasure] :
    ∃ L : PositiveRealExponentialDecay univ →L[ℂ] sLocalPolarFreeTestSubspace F S,
      (∀ φ (q : SIdeleQuotient F S),
        sLocalHomogeneousTheta F S ν 1 (L φ).val.val q = φ.val (Real.log (sLocalClassModulus F S q))) ∧
      (∀ a b : ℝ, ∃ C : Set (SAdeles F S), IsCompact C ∧
        ∀ f, support f.val ⊆ Icc a b →
          tsupport (sLocalBruhatRestriction F S (L f).val.val) ⊆ C) ∧
      ∀ f, logProfileExponentialMoment f.val = 0 →
        GlobalBruhat.polarEvaluation F (L f).val.val = 0 := by
  obtain ⟨b, hb₁, hbp, hbr, L, hLift, hSupport, hMoments⟩ :=
    exists_sLocalPolarFree_radialLiftCLM_on_ideles_fixedSupport F S
  let ref := L radialReferenceProfile
  have href := hLift radialReferenceProfile
  have hRef (u : G F S) (hu : sLocalIdeleNorm F S u = 1) :
      sLocalBruhatRestriction F S ref.val.val u.val = b u := by
    rw [href, hu, Real.log_one, radialReferenceProfile_zero, mul_one]
  let T (k : K F S) := sLocalTheta F S (sLocalBruhatRestriction F S ref.val.val) k.val
  let A : ℂ := ∫ k, T k ∂ν
  have ht : Continuous T :=
    (sLocalTheta_continuous F S ref.val.val).comp continuous_subtype_val
  letI : CompactSpace (K F S) := sLocalThetaNormOne_compact F S
  have hInt : Integrable T ν := ht.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn (k : K F S) : 0 ≤ (T k).re := by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective k.val
    change 0 ≤ (sLocalTheta F S (sLocalBruhatRestriction F S ref.val.val) k.val).re
    rw [← hu]
    exact theta_normOne_reference_nonneg F S b hbp ref.val hRef u (sLocal_normOne_lift_norm F S k u hu)
  have hp₁ : 0 < (T 1).re := theta_normOne_reference_at_one F S b hb₁ hbp ref.val hRef
  have hA : A ≠ 0 := by
    have hp : 0 < ∫ k, (T k).re ∂ν := by
      apply (integral_pos_iff_support_of_nonneg hnn hInt.re).mpr
      apply (isClosed_eq (Complex.continuous_re.comp ht) continuous_const).isOpen_compl.measure_pos ν
      exact ⟨1, hp₁.ne'⟩
    change 0 < ∫ k, RCLike.re (T k) ∂ν at hp
    rw [integral_re hInt] at hp
    intro hz
    change 0 < A.re at hp
    rw [hz, Complex.zero_re] at hp
    exact (lt_irrefl _) hp
  letI : ContinuousSMul ℂ (PositiveRealExponentialDecay univ) :=
    (PolynormableSpace.withSeminorms ℂ (PositiveRealExponentialDecay univ)).continuousSMul
  let P : PositiveRealExponentialDecay univ →L[ℂ] PositiveRealExponentialDecay univ :=
    A⁻¹ • ContinuousLinearMap.id ℂ (PositiveRealExponentialDecay univ)
  have hM (f : PositiveRealExponentialDecay univ) (hf : logProfileExponentialMoment f.val = 0) :
      GlobalBruhat.polarEvaluation F (L (P f)).val.val = 0 := by
    apply hMoments
    change (∫ t : ℝ, (Real.exp t : ℂ) * (A⁻¹ * f.val t)) = 0
    simp_rw [mul_left_comm (Real.exp _ : ℂ) A⁻¹]
    rw [integral_const_mul, ← logProfileExponentialMoment, hf, mul_zero]
  refine ⟨L.comp P, ?_, ?_, hM⟩
  swap
  · intro a b'
    obtain ⟨C, hC, hLC⟩ := hSupport a b'
    refine ⟨C, hC, fun f hf ↦ hLC (P f) ?_⟩
    exact (support_smul_subset_right (fun _ : ℝ ↦ A⁻¹) f.val).trans hf
  intro φ q
  let f := A⁻¹ • φ
  let g := L f
  have hg := hLift f
  change sLocalHomogeneousTheta F S ν 1 g.val.val q = _
  obtain ⟨⟨t, k⟩, rfl⟩ := (sLocalZetaSplit F S).surjective q
  let uₜ := sLocalExpSection F S (Multiplicative.ofAdd t)
  have hLog : Real.log (sLocalClassModulus F S ((sLocalZetaSplit F S) (t, k))) = t := by
    let σ : SIdeleQuotient F S := QuotientGroup.mk uₜ
    change Real.log (sLocalClassModulus F S (σ * k.val)) = t
    rw [show σ * k.val = k.val * σ from mul_comm σ k.val,
      sLocalClassModulus_normOne_mul, sLocalClassModulus_mk,
      sLocalIdeleNorm_expSection F S t, Real.log_exp]
  rw [hLog]
  have he (a : K F S) :
      sLocalTheta F S (sLocalBruhatRestriction F S g.val.val)
        (a.val * ((sLocalZetaSplit F S) (t, k))) = f.val t * T (a*k) := by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (a*k).val
    have hn := sLocal_normOne_lift_norm F S (a*k) u hu
    have heq : a.val * ((sLocalZetaSplit F S) (t, k)) =
        (QuotientGroup.mk (uₜ * u) : SIdeleQuotient F S) := by
      change a.val * ((QuotientGroup.mk uₜ : SIdeleQuotient F S) * k.val) = _
      rw [QuotientGroup.mk_mul, hu]
      exact mul_left_comm (a.val : SIdeleQuotient F S) (QuotientGroup.mk uₜ) k.val
    have hE (v : Orbit F S) : sLocalBruhatRestriction F S g.val.val
        (sIntegerDiagonal F S v.toMul.val * (uₜ*u).val) =
        f.val t * sLocalBruhatRestriction F S ref.val.val (sIntegerDiagonal F S v.toMul.val * u.val) := by
      let e := (sUnitOrbitEquiv F S v).val
      rw [← sUnitOrbitEquiv_val F S v]
      change sLocalBruhatRestriction F S g.val.val (e*(uₜ*u)).val =
        f.val t * sLocalBruhatRestriction F S ref.val.val (e*u).val
      have h₁ : sLocalIdeleNorm F S (e*u) = 1 := by rw [map_mul, sLocalOrbit_norm, hn, one_mul]
      rw [mul_left_comm e uₜ u, hg, hRef _ h₁, hbr t, map_mul, h₁, mul_one,
        sLocalIdeleNorm_expSection F S t, Real.log_exp, mul_comm]
    rw [heq, sLocalTheta_mk]
    change sLocalThetaOnIdeles F S _ _ = f.val t * sLocalTheta F S _ (a*k).val
    rw [← hu, sLocalTheta_mk, sLocalThetaOnIdeles, sLocalThetaOnIdeles, ← tsum_mul_left]
    exact tsum_congr hE
  calc
    _ = ∫ a, f.val t * T (a*k) ∂ν := by
      unfold sLocalHomogeneousTheta
      apply integral_congr_ae
      exact Eventually.of_forall fun a ↦ by
        change (1 : ℂ) * sLocalTheta F S (sLocalBruhatRestriction F S g.val.val)
          (a.val * ((sLocalZetaSplit F S) (t, k))) = _
        rw [one_mul, he]
    _ = φ.val t := by
      rw [integral_const_mul, show (fun a ↦ T (a*k)) = (fun a ↦ T (k*a)) from
        funext fun a ↦ congrArg T (mul_comm a k), integral_mul_left_eq_self T k]
      change (A⁻¹ * φ.val t) * A = φ.val t
      rw [mul_right_comm, inv_mul_cancel₀ hA, one_mul]

theorem exists_sLocalHomogeneousTheta_trivial_polarFreeCLM
    (ν : Measure (K F S)) [ν.IsHaarMeasure] :
    ∃ L : PositiveRealExponentialDecay univ →L[ℂ] sLocalPolarFreeTestSubspace F S,
      ∀ φ (q : SIdeleQuotient F S),
        sLocalHomogeneousTheta F S ν 1 (L φ).val.val q = φ.val (Real.log (sLocalClassModulus F S q)) := by
  obtain ⟨L, hL, _, _⟩ := exists_sLocalHomogeneousTheta_trivial_polarFreeCLM_fixedSupport F S ν
  exact ⟨L, hL⟩

theorem exists_sLocalHomogeneousTheta_trivial_polarFree
    (ν : Measure (K F S)) [ν.IsHaarMeasure] (φ : PositiveRealExponentialDecay univ) :
    ∃ f : sLocalPolarFreeTestSubspace F S, ∀ q : SIdeleQuotient F S,
      sLocalHomogeneousTheta F S ν 1 f.val.val q = φ.val (Real.log (sLocalClassModulus F S q)) := by
  obtain ⟨L, hL⟩ := exists_sLocalHomogeneousTheta_trivial_polarFreeCLM F S ν
  exact ⟨L φ, hL φ⟩

end

end Masullo
