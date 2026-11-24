import RadialSchwartzLift
import ArchimedeanLogarithms
import FrechetFactorization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open Filter Function NumberField Set Topology
open scoped Classical ContDiff SchwartzMap NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev X := mixedEmbedding.mixedSpace F
private abbrev R := {v : InfinitePlace F // v.IsReal}
private abbrev C := {v : InfinitePlace F // v.IsComplex}
private abbrev d := Module.finrank ℚ F

theorem archModulus_nonneg (x : X F) : 0 ≤ archModulus F x := by
  unfold archModulus
  positivity

theorem archModulus_continuous : Continuous (archModulus F) := by
  unfold archModulus
  fun_prop

theorem archModulus_smul_of_pos (r : ℝ) (hr : 0 < r) (x : X F) :
    archModulus F (r • x) = r ^ d F * archModulus F x := by
  have hR (v : R F) : ‖(r • x).1 v‖ = r * ‖x.1 v‖ := by
    change ‖r • x.1 v‖ = _
    rw [norm_smul, Real.norm_of_nonneg hr.le]
  have hC (v : C F) : ‖(r • x).2 v‖ = r * ‖x.2 v‖ := by
    change ‖r • x.2 v‖ = _
    rw [norm_smul, Real.norm_of_nonneg hr.le]
  unfold archModulus
  simp_rw [hR, hC, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, show d F = _ from (InfinitePlace.card_add_two_mul_card_eq_rank F).symm, pow_add]
  ring

private theorem archModulus_pos_iff (x : X F) :
    0 < archModulus F x ↔ (∀ v : R F, x.1 v ≠ 0) ∧ ∀ v : C F, x.2 v ≠ 0 := by
  unfold archModulus
  constructor
  · intro hp
    constructor
    · intro v hv
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, norm_zero]), zero_mul] at hp
      exact (lt_irrefl 0) hp
    · intro v hv
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv]), mul_zero] at hp
      exact (lt_irrefl 0) hp
  · rintro ⟨hR, hC⟩
    exact mul_pos (Finset.prod_pos fun v _ ↦ norm_pos_iff.mpr (hR v))
      (Finset.prod_pos fun v _ ↦ pow_pos (norm_pos_iff.mpr (hC v)) 2)

private theorem archModulus_smooth :
    ContDiffOn ℝ ∞ (archModulus F) {x | 0 < archModulus F x} := by
  intro x hx
  obtain ⟨hR, hC⟩ := (archModulus_pos_iff F x).mp hx
  have hreal (v : R F) : ContDiffAt ℝ ∞ (fun x : X F ↦ ‖x.1 v‖) x := by
    have h : ContDiffAt ℝ ∞ (fun x : X F ↦ x.1 v) x := ((ContinuousLinearMap.proj (R := ℝ) v).comp
      (ContinuousLinearMap.fst ℝ (R F → ℝ) (C F → ℂ))).contDiff.contDiffAt (x := x)
    exact h.norm ℝ (hR v)
  have hcomplex (v : C F) : ContDiffAt ℝ ∞ (fun x : X F ↦ ‖x.2 v‖ ^ 2) x := by
    have h : ContDiffAt ℝ ∞ (fun x : X F ↦ x.2 v) x := ((ContinuousLinearMap.proj (R := ℝ) v).comp
      (ContinuousLinearMap.snd ℝ (R F → ℝ) (C F → ℂ))).contDiff.contDiffAt (x := x)
    exact (h.norm ℝ (hC v)).pow 2
  apply ContDiffAt.contDiffWithinAt
  exact (contDiffAt_prod fun v _ ↦ hreal v).mul (contDiffAt_prod fun v _ ↦ hcomplex v)

/-- The positive homogeneous radius associated to the archimedean modulus. -/
def archModulusRadius (x : X F) : ℝ :=
  archModulus F x ^ ((d F : ℝ)⁻¹)

private theorem degree_pos : (0 : ℝ) < d F := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)

theorem archModulusRadius_continuous : Continuous (archModulusRadius F) :=
  (Real.continuous_rpow_const (inv_nonneg.mpr (degree_pos F).le)).comp (archModulus_continuous F)

theorem archModulusRadius_nonneg (x : X F) : 0 ≤ archModulusRadius F x :=
  Real.rpow_nonneg (archModulus_nonneg F x) _

theorem archModulusRadius_pos_iff (x : X F) : 0 < archModulusRadius F x ↔ 0 < archModulus F x := by
  constructor
  · intro hh
    by_contra! h
    have hz := le_antisymm h (archModulus_nonneg F x)
    change 0 < archModulus F x ^ ((d F : ℝ)⁻¹) at hh
    rw [hz, Real.zero_rpow (inv_ne_zero (degree_pos F).ne')] at hh
    exact (lt_irrefl 0) hh
  · exact fun h ↦ Real.rpow_pos_of_pos h _

theorem archModulusRadius_smul (r : ℝ) (hr : 0 < r) (x : X F) :
    archModulusRadius F (r • x) = r * archModulusRadius F x := by
  unfold archModulusRadius
  rw [archModulus_smul_of_pos F r hr,
    Real.mul_rpow (pow_nonneg hr.le _) (archModulus_nonneg F x),
    Real.pow_rpow_inv_natCast hr.le (Nat.ne_of_gt Module.finrank_pos)]

private theorem archModulusRadius_smooth :
    ContDiffOn ℝ ∞ (archModulusRadius F) {x | 0 < archModulusRadius F x} := by
  have hh : {x | 0 < archModulusRadius F x} = {x | 0 < archModulus F x} :=
    Set.ext (archModulusRadius_pos_iff F)
  rw [hh]
  exact (archModulus_smooth F).rpow_const_of_ne (fun _ h ↦ (show 0 < archModulus F _ from h).ne')

theorem archModulusRadius_log (x : X F) :
    (d F : ℝ) * Real.log (archModulusRadius F x) = Real.log (archModulus F x) := by
  rcases eq_or_lt_of_le (archModulus_nonneg F x) with hz | hp
  · unfold archModulusRadius
    rw [← hz, Real.zero_rpow (inv_ne_zero (degree_pos F).ne'), Real.log_zero, mul_zero]
  · unfold archModulusRadius
    rw [Real.log_rpow hp, ← mul_assoc, mul_inv_cancel₀ (degree_pos F).ne', one_mul]

/-- An all-exponent profile can be lifted on the actual mixed Schwartz
space using any compact transverse cutoff supported away from the walls. -/
theorem exists_archimedeanFlat_logRadius_lift (ψ : 𝓢(X F, ℂ)) (hψ : HasCompactSupport ψ)
    (hK : tsupport ψ ⊆ {x | 0 < archModulus F x}) (f : PositiveRealExponentialDecay univ) :
    ∃ g : 𝓢(X F, ℂ), g ∈ archimedeanFlatTestSubspace F ∧
      ∀ x, g x = ψ ((archModulusRadius F x)⁻¹ • x) * f.val (Real.log (archModulus F x)) := by
  obtain ⟨g, hg, hφ⟩ := exists_flatSchwartz_of_logRadius (archModulusRadius F)
    (archModulusRadius_continuous F) (archModulusRadius_nonneg F) (archModulusRadius_smul F)
    (archModulusRadius_smooth F) ψ hψ
    (fun x hx ↦ (archModulusRadius_pos_iff F x).mpr (hK hx)) (d F : ℝ) (degree_pos F) f
  refine ⟨g, (mem_schwartzFlatSubspace _ _).mpr fun x hx ↦ ?_, fun x ↦ ?_⟩
  · apply (mem_schwartzFlatSubspace _ _).mp hg x
    change archModulusRadius F x = 0
    by_contra h
    have hp := (archModulus_pos_iff F x).mp ((archModulusRadius_pos_iff F x).mp
      (lt_of_le_of_ne (archModulusRadius_nonneg F x) (Ne.symm h)))
    rcases hx with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact hp.1 v hv
    · exact hp.2 v hv
  · rw [hφ, archModulusRadius_log]

/-- The fixed-cutoff radial lift is continuous for the all-exponent
Schwartz topology. Pointwise evaluation identifies its closed graph. -/
theorem exists_archimedeanFlat_logRadius_liftCLM (ψ : 𝓢(X F, ℂ)) (hψ : HasCompactSupport ψ)
    (hK : tsupport ψ ⊆ {x | 0 < archModulus F x}) :
    ∃ L : PositiveRealExponentialDecay univ →L[ℂ] 𝓢(X F, ℂ),
      (∀ f, L f ∈ archimedeanFlatTestSubspace F) ∧
      ∀ f x, L f x = ψ ((archModulusRadius F x)⁻¹ • x) * f.val (Real.log (archModulus F x)) := by
  let E := PositiveRealExponentialDecay (univ : Set ℝ)
  let A := 𝓢(X F, ℂ)
  let b (x : X F) := ψ ((archModulusRadius F x)⁻¹ • x)
  let t (x : X F) := Real.log (archModulus F x)
  choose L hFlat hL using exists_archimedeanFlat_logRadius_lift F ψ hψ hK
  let Lₗ : E →ₗ[ℂ] A :=
    { toFun := L
      map_add' := fun f g ↦ SchwartzMap.ext fun x ↦ by
        change L (f+g) x = L f x + L g x
        rw [hL, hL, hL]
        exact mul_add _ _ _
      map_smul' := fun c f ↦ SchwartzMap.ext fun x ↦ by
        change L (c • f) x = c * L f x
        rw [hL, hL]
        change b x * (c * f.val (t x)) = c * (b x * f.val (t x))
        ring }
  have hEval (y : ℝ) : Continuous (fun f : E ↦ f.val y) := by
    let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
    have hTwist : Continuous (fun f : E ↦ logExponentialDecayTwist univ a f) :=
      (continuous_apply a).comp (positiveRealExponentialDecay_isEmbedding univ univ_nonempty).continuous
    have hSchwartz : Continuous (fun g : 𝓢(ℝ, ℂ) ↦ g y) :=
      (BoundedContinuousFunction.lipschitz_eval_const y).continuous.comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous
    have h := hSchwartz.comp hTwist
    refine h.congr fun f ↦ ?_
    simpa [a] using logExponentialDecayTwist_apply univ a
      (show logExponentialDecaySubmodule univ from f) y
  have hgraph : IsClosed (Lₗ.graph : Set (E × A)) := by
    rw [show (Lₗ.graph : Set (E × A)) =
      ⋂ x : X F, {q : E × A | b x * q.1.val (t x) = q.2 x} from by
        ext q
        change q ∈ Lₗ.graph ↔ _
        rw [Lₗ.mem_graph_iff, mem_iInter]
        constructor
        · intro h x
          change b x * q.1.val (t x) = q.2 x
          rw [h]
          exact (hL q.1 x).symm
        · intro h
          apply SchwartzMap.ext
          intro x
          exact (h x).symm.trans (hL q.1 x).symm]
    refine isClosed_iInter fun x ↦ ?_
    have hA : Continuous (fun g : A ↦ g x) :=
      (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (X F) ℂ).continuous
    have h₂ := hA.comp (continuous_snd : Continuous (Prod.snd : E × A → A))
    exact isClosed_eq (continuous_const.mul ((hEval (t x)).comp continuous_fst)) h₂
  obtain ⟨_, hNorm, hMetric, hComplete⟩ :=
    positiveRealExponentialDecay_frechet univ ordConnected_univ univ_nonempty
  letI : TopologicalSpace.MetrizableSpace E := hMetric
  letI : PolynormableSpace ℂ E := hNorm
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : CompleteSpace E := hComplete
  letI : T2Space E := (positiveRealExponentialDecay_isEmbedding univ univ_nonempty).t2Space
  letI : CompleteSpace A := completeSpace_schwartzMap
  letI : FirstCountableTopology A := (schwartz_withSeminorms ℂ (X F) ℂ).firstCountableTopology
  exact ⟨⟨Lₗ, frechet_continuous_of_closed_graph Lₗ hgraph⟩, hFlat, hL⟩

/-- Fixing the logarithmic support gives one compact additive support for the
entire family of lifts, contained in the multiplicative archimedean locus. -/
theorem archimedeanLogRadius_fixedSupport
    (ψ : 𝓢(X F, ℂ)) (hψ : HasCompactSupport ψ)
    (hK : tsupport ψ ⊆ {x | 0 < archModulus F x}) (a b : ℝ) :
    ∃ K : Set (X F), IsCompact K ∧ K ⊆ {x | 0 < archModulus F x} ∧
      ∀ (f : ℝ → ℂ) (g : X F → ℂ),
        (∀ x, g x = ψ ((archModulusRadius F x)⁻¹ • x) * f (Real.log (archModulus F x))) →
        support f ⊆ Icc a b → tsupport g ⊆ K := by
  let dilate (p : ℝ × X F) := Real.exp (p.1 / (d F : ℝ)) • p.2
  let K := dilate '' (Icc a b ×ˢ tsupport ψ)
  have hcont : Continuous dilate :=
    (Real.continuous_exp.comp (continuous_fst.div_const _)).smul continuous_snd
  have hcompact : IsCompact K := (isCompact_Icc.prod hψ.isCompact).image hcont
  refine ⟨K, hcompact, ?_, fun f g hL hf ↦ closure_minimal ?_ hcompact.isClosed⟩
  · rintro _ ⟨⟨t, y⟩, ⟨_, hy⟩, rfl⟩
    change 0 < archModulus F (Real.exp (t / (d F : ℝ)) • y)
    rw [archModulus_smul_of_pos F _ (Real.exp_pos _)]
    exact mul_pos (pow_pos (Real.exp_pos _) _) (hK hy)
  · intro x hx
    have hx₀ : 0 < archModulus F x := by
      by_contra! h
      have hz := le_antisymm h (archModulus_nonneg F x)
      have hr : archModulusRadius F x = 0 := by
        simp [archModulusRadius, hz, (degree_pos F).ne']
      have hψ₀ : ψ 0 = 0 := by
        apply notMem_support.mp
        intro h₀
        have hp := (archModulus_pos_iff F 0).mp (hK (subset_closure h₀))
        obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
        by_cases hv : v.IsReal
        · exact hp.1 ⟨v, hv⟩ rfl
        · exact hp.2 ⟨v, InfinitePlace.not_isReal_iff_isComplex.mp hv⟩ rfl
      exact hx (by rw [hL, hr, inv_zero, zero_smul, hψ₀, zero_mul])
    have hr := (archModulusRadius_pos_iff F x).mpr hx₀
    rw [mem_support, hL, mul_ne_zero_iff] at hx
    refine ⟨⟨Real.log (archModulus F x), (archModulusRadius F x)⁻¹ • x⟩,
      ⟨hf hx.2, subset_closure hx.1⟩, ?_⟩
    have he : Real.exp (Real.log (archModulus F x) / (d F : ℝ)) = archModulusRadius F x := by
      rw [← archModulusRadius_log F x, mul_comm, mul_div_cancel_right₀ _ (degree_pos F).ne',
        Real.exp_log hr]
    change Real.exp (Real.log (archModulus F x) / (d F : ℝ)) •
      ((archModulusRadius F x)⁻¹ • x) = x
    rw [he, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

theorem exists_archimedeanFlat_logRadius_liftCLM_fixedSupport
    (ψ : 𝓢(X F, ℂ)) (hψ : HasCompactSupport ψ)
    (hK : tsupport ψ ⊆ {x | 0 < archModulus F x}) (a b : ℝ) :
    ∃ (K : Set (X F)) (L : PositiveRealExponentialDecay univ →L[ℂ] 𝓢(X F, ℂ)),
      IsCompact K ∧ K ⊆ {x | 0 < archModulus F x} ∧
      (∀ f, L f ∈ archimedeanFlatTestSubspace F) ∧
      (∀ f x, L f x = ψ ((archModulusRadius F x)⁻¹ • x) * f.val (Real.log (archModulus F x))) ∧
      ∀ f, support f.val ⊆ Icc a b → tsupport (L f) ⊆ K := by
  obtain ⟨L, hFlat, hL⟩ := exists_archimedeanFlat_logRadius_liftCLM F ψ hψ hK
  obtain ⟨K, hCompact, hSubset, hSupport⟩ := archimedeanLogRadius_fixedSupport F ψ hψ hK a b
  exact ⟨K, L, hCompact, hSubset, hFlat, hL, fun f ↦ hSupport f.val (L f) (hL f)⟩

private def radialBump {E : Type*} [NormedAddCommGroup E] (c : E) : ContDiffBump c :=
  ⟨1/4, 1/2, by norm_num, by norm_num⟩

/-- A nonnegative transverse cutoff around the identity, with support
compactly contained in the multiplicative archimedean locus. -/
theorem exists_archimedeanRadialCutoff :
    ∃ ψ : 𝓢(X F, ℂ), HasCompactSupport ψ ∧ (tsupport ψ ⊆ {x | 0 < archModulus F x}) ∧
      ψ 1 = 1 ∧ ∀ x, ∃ r : ℝ, 0 ≤ r ∧ ψ x = (r : ℂ) := by
  let br := radialBump (1 : ℝ)
  let bc := radialBump (1 : ℂ)
  let b (x : X F) : ℝ := (∏ v : R F, br (x.1 v)) * ∏ v : C F, bc (x.2 v)
  let ψ (x : X F) : ℂ := b x
  have hbr (v : R F) : ContDiff ℝ ∞ (fun x : X F ↦ br (x.1 v)) :=
    br.contDiff.comp (((ContinuousLinearMap.proj (R := ℝ) v).comp
      (ContinuousLinearMap.fst ℝ (R F → ℝ) (C F → ℂ))).contDiff)
  have hbc (v : C F) : ContDiff ℝ ∞ (fun x : X F ↦ bc (x.2 v)) :=
    bc.contDiff.comp (((ContinuousLinearMap.proj (R := ℝ) v).comp
      (ContinuousLinearMap.snd ℝ (R F → ℝ) (C F → ℂ))).contDiff)
  have hs : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp
    ((contDiff_prod fun v _ ↦ hbr v).mul (contDiff_prod fun v _ ↦ hbc v))
  have hsupport : Function.support ψ ⊆ Metric.closedBall (1 : X F) (1/2) := by
    intro x hx
    have hr (v : R F) : ‖x.1 v - 1‖ ≤ 1/2 := by
      by_contra! h
      apply hx
      have he : br (x.1 v) = 0 := br.zero_of_le_dist (by simpa [br, radialBump, dist_eq_norm] using h.le)
      change ((b x : ℝ) : ℂ) = 0
      rw [show b x = 0 by dsimp [b]; rw [Finset.prod_eq_zero (Finset.mem_univ v) he, zero_mul]]
      simp
    have hc (v : C F) : ‖x.2 v - 1‖ ≤ 1/2 := by
      by_contra! h
      apply hx
      have he : bc (x.2 v) = 0 := bc.zero_of_le_dist (by simpa [bc, radialBump, dist_eq_norm] using h.le)
      change ((b x : ℝ) : ℂ) = 0
      rw [show b x = 0 by dsimp [b]; rw [Finset.prod_eq_zero (Finset.mem_univ v) he, mul_zero]]
      simp
    rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, max_le_iff]
    exact ⟨(pi_norm_le_iff_of_nonneg (by norm_num)).mpr hr,
      (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hc⟩
  have hts : tsupport ψ ⊆ Metric.closedBall (1 : X F) (1/2) :=
    closure_minimal hsupport Metric.isClosed_closedBall
  have hK : HasCompactSupport ψ := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hts
  refine ⟨hK.toSchwartzMap hs, hK, ?_, ?_, ?_⟩
  · intro x hx
    apply (archModulus_pos_iff F x).mpr
    have hb : ‖x - 1‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hts hx
    refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
    · have h := ((norm_le_pi_norm (x - 1).1 v).trans (norm_fst_le (x-1))).trans hb
      change ‖x.1 v - 1‖ ≤ 1/2 at h
      rw [hv] at h
      norm_num at h
    · have h := ((norm_le_pi_norm (x - 1).2 v).trans (norm_snd_le (x-1))).trans hb
      change ‖x.2 v - 1‖ ≤ 1/2 at h
      rw [hv] at h
      norm_num at h
  · change (b 1 : ℂ) = 1
    have hr : br 1 = 1 := br.one_of_mem_closedBall (Metric.mem_closedBall_self br.rIn_pos.le)
    have hc : bc 1 = 1 := bc.one_of_mem_closedBall (Metric.mem_closedBall_self bc.rIn_pos.le)
    have he : b 1 = 1 := by
      change (∏ _ : R F, br 1) * (∏ _ : C F, bc 1) = 1
      rw [hr, hc, Finset.prod_const_one, Finset.prod_const_one, mul_one]
    rw [he, Complex.ofReal_one]
  · intro x
    refine ⟨b x, ?_, rfl⟩
    exact mul_nonneg (Finset.prod_nonneg fun _ _ ↦ br.nonneg) (Finset.prod_nonneg fun _ _ ↦ bc.nonneg)

end

end Masullo
