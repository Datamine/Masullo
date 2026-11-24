import GlobalSpectralJets
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! The Gaussian polynomial approximation follows the Apache-2.0
RiemannMasullo proof in Ch07_SchauderBasesZeta/Sec1b.lean at 3897f94. -/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField

namespace Masullo

noncomputable section

private abbrev B := SchwartzBergman (univ : Set ℝ)

/-- Entire functions with the topology inherited from compact-open maps. -/
def compactOpenEntireSubmodule : Submodule ℂ C(ℂ, ℂ) where
  carrier := {f | Differentiable ℂ (f : ℂ → ℂ)}
  zero_mem' := differentiable_const _
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.const_mul c

abbrev CompactOpenEntire := ↥compactOpenEntireSubmodule

@[reducible] local instance : TopologicalSpace (StrongDual ℂ CompactOpenEntire) :=
  ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℂ) (E := CompactOpenEntire) (F := ℂ)

private theorem bergman_differentiable (f : B) : Differentiable ℂ f.val := by
  simpa only [preimage_univ, differentiableOn_univ] using f.property.2.1

/-- The canonical inclusion preserves function values and is continuous
from the entire Schwartz–Bergman topology to compact convergence. -/
def bergmanToCompactOpenEntire : B →L[ℂ] CompactOpenEntire := by
  let M : B →ₗ[ℂ] C(ℂ, ℂ) :=
    { toFun := fun f ↦ ⟨f.val, (bergman_differentiable f).continuous⟩
      map_add' := fun _ _ ↦ ContinuousMap.ext fun _ ↦ rfl
      map_smul' := fun _ _ ↦ ContinuousMap.ext fun _ ↦ rfl }
  have hM : Continuous M := by
    let hF := schwartzBergman_frechet (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty
    letI : IsTopologicalAddGroup B := hF.choose
    apply continuous_of_continuousAt_zero M.toAddMonoidHom
    change Tendsto M (𝓝 0) (𝓝 (M 0))
    rw [map_zero, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
    obtain ⟨hE, _⟩ := bergmanNormalizedJet_family (-R) R (by linarith)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := Metric.equicontinuousAt_iff_right.mp (hE 0) ε hε
    filter_upwards [h] with f hf z hz
    have hz' : ‖z‖ ≤ R := by simpa using hKR hz
    have hzr := abs_le.mp ((Complex.abs_re_le_norm z).trans hz')
    let p : {z : ℂ // z.re ∈ Icc (-R) R} × ℕ := (⟨z, hzr⟩, 0)
    change dist 0 (f.val z) < ε
    simpa only [p, bergmanNormalizedJet_apply, Nat.factorial_zero, Nat.cast_one, inv_one,
      iteratedDeriv_zero, one_mul, map_zero, ContinuousMap.zero_apply] using hf p
  exact ⟨M.codRestrict _ (fun f ↦ bergman_differentiable f), hM.subtype_mk _⟩

@[simp] theorem bergmanToCompactOpenEntire_apply (f : B) (z : ℂ) :
    (bergmanToCompactOpenEntire f).val z = f.val z := rfl

private theorem bergman_mul_pow_mem (f : ℂ → ℂ)
    (hf : f ∈ schwartzBergmanSubmodule (univ : Set ℝ)) (k : ℕ) :
    (fun z ↦ z ^ k * f z) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  refine ⟨by simp, ((differentiable_id.pow k).differentiableOn.mul hf.2.1), ?_⟩
  intro a b hab hi N
  obtain ⟨C, hC⟩ := hf.2.2 a b hab hi (N + k)
  refine ⟨C, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simpa only [pow_add, mul_assoc] using hC ⟨z, hz, rfl⟩

private theorem bergman_approx_closedBall (f : CompactOpenEntire) (R : ℝ) (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) : ∃ a : B, ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖f.val z - a.val z‖ < ε := by
  let G : ℂ → ℂ := fun z ↦ Complex.exp (z ^ 2)
  have hG : G ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
    simpa only [Set.preimage_univ, Set.indicator_univ] using
      gaussian_mem_schwartzBergmanSubmodule univ isOpen_univ
  let w : ℂ → ℂ := fun z ↦ f.val z * Complex.exp (-(z ^ 2))
  have hd : Differentiable ℂ (f.val : ℂ → ℂ) := f.property
  have hwd : Differentiable ℂ w := hd.mul (by fun_prop)
  have hw (z : ℂ) : f.val z = G z * w z := by
    dsimp only [G, w]
    rw [mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  let Rn : ℝ≥0 := ⟨R + 1, by linarith⟩
  let Rm : ℝ≥0 := ⟨R + 1 / 2, by linarith⟩
  have hps := hwd.differentiableOn.hasFPowerSeriesOnBall (c := (0 : ℂ))
    (show (0 : ℝ≥0) < Rn by change 0 < R + 1; linarith)
  have hu := hps.tendstoUniformlyOn (r' := Rm)
    (ENNReal.coe_lt_coe.mpr (show Rm < Rn by change R + 1 / 2 < R + 1; linarith))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (f := G) (by fun_prop)
  have hδ : 0 < ε / (|C| + 1) := by positivity
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu _ hδ).exists
  let p := cauchyPowerSeries w 0 Rn
  have hpart (y : ℂ) : p.partialSum n y = ∑ k ∈ Finset.range n, y ^ k * p.coeff k := by
    simp [FormalMultilinearSeries.partialSum]
  have hmem : (fun z ↦ G z * ∑ k ∈ Finset.range n, z ^ k * p.coeff k) ∈
      schwartzBergmanSubmodule (univ : Set ℝ) := by
    have he : (fun z ↦ G z * ∑ k ∈ Finset.range n, z ^ k * p.coeff k) =
        ∑ k ∈ Finset.range n, p.coeff k • (fun z ↦ z ^ k * G z) := by
      funext z
      simp only [Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he]
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _
      (bergman_mul_pow_mem G hG k)
  refine ⟨⟨_, hmem⟩, fun z hz ↦ ?_⟩
  have hzm : z ∈ Metric.ball (0 : ℂ) Rm := mem_ball_zero_iff.mpr (by
    have hz' := mem_closedBall_zero_iff.mp hz
    change ‖z‖ < R + 1 / 2
    linarith)
  change ‖f.val z - G z * ∑ k ∈ Finset.range n, z ^ k * p.coeff k‖ < ε
  rw [hw z, ← mul_sub, norm_mul]
  have h1 := hn z hzm
  rw [zero_add, dist_eq_norm, hpart] at h1
  calc ‖G z‖ * ‖w z - ∑ k ∈ Finset.range n, z ^ k * p.coeff k‖
      ≤ |C| * (ε / (|C| + 1)) :=
        mul_le_mul ((hC z hz).trans (le_abs_self C)) h1.le (norm_nonneg _) (abs_nonneg _)
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg C]

/-- Gaussian Taylor polynomials are dense for compact convergence. -/
theorem bergmanToCompactOpenEntire_denseRange : DenseRange bergmanToCompactOpenEntire := by
  intro f
  have h (n : ℕ) := bergman_approx_closedBall f ((n : ℝ) + 1) (by positivity)
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose a ha using h
  refine mem_closure_of_tendsto (f := fun n ↦ bergmanToCompactOpenEntire (a n)) (b := atTop) ?_
    (Eventually.of_forall fun n ↦ mem_range_self (a n))
  apply tendsto_subtype_rng.mpr
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [hev, eventually_ge_atTop N] with n hn hnN z hz
  have hRn : R ≤ (n : ℝ) + 1 := by
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hnN
    linarith
  have hzball := Metric.closedBall_subset_closedBall hRn (hKR hz)
  simpa only [dist_eq_norm, bergmanToCompactOpenEntire_apply] using (ha n z hzball).trans hn

/-- Complex derivatives are continuous linear functionals for compact convergence. -/
def compactOpenEntireJet (z : ℂ) (m : ℕ) : StrongDual ℂ CompactOpenEntire where
  toFun f := iteratedDeriv m (f.val : ℂ → ℂ) z
  map_add' f g :=
    iteratedDeriv_add (show Differentiable ℂ (f.val : ℂ → ℂ) from f.property).contDiff.contDiffAt
      (show Differentiable ℂ (g.val : ℂ → ℂ) from g.property).contDiff.contDiffAt
  map_smul' c f := iteratedDeriv_const_smul_field c (f.val : ℂ → ℂ)
  cont := by
    apply continuous_iff_continuousAt.mpr
    intro f
    have hd (g : CompactOpenEntire) : Differentiable ℂ (g.val : ℂ → ℂ) := g.property
    have hlim (n : ℕ) : TendstoLocallyUniformlyOn
        (fun g : CompactOpenEntire ↦ iteratedDeriv n (g.val : ℂ → ℂ))
        (iteratedDeriv n (f.val : ℂ → ℂ)) (𝓝 f) univ := by
      induction n with
      | zero =>
        exact tendstoLocallyUniformlyOn_univ.mpr
          (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
            (show Tendsto (fun g : CompactOpenEntire ↦ g.val) (𝓝 f) (𝓝 f.val) from
              continuous_subtype_val.continuousAt))
      | succ n ih =>
        simpa only [iteratedDeriv_succ, Function.comp_def] using
          ih.deriv (Eventually.of_forall fun g ↦
            ((hd g).contDiff.differentiable_iteratedDeriv' n).differentiableOn) isOpen_univ
    exact (hlim m).tendsto_at (mem_univ z)

private abbrev Indices (g : ℂ → ℂ) := {i : ℂ × ℕ // (i.2 : ℕ∞) < analyticOrderAt g i.1}

/-- The compact-open principal ideal, specified by the vanishing jets. -/
def compactOpenEntireDivisor (g : ℂ → ℂ) : Submodule ℂ CompactOpenEntire :=
  ⨅ i : Indices g, (compactOpenEntireJet i.val.1 i.val.2).ker

theorem compactOpenEntireDivisor_mem_iff {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (f : CompactOpenEntire) :
    f ∈ compactOpenEntireDivisor g ↔
      ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ z, f.val z = g z * k z := by
  have hd : Differentiable ℂ (f.val : ℂ → ℂ) := f.property
  rw [entire_divisibility_iff_orders hg hd]
  simp only [compactOpenEntireDivisor, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe]
  constructor
  · intro h z
    rw [← ENat.forall_natCast_le_iff_le]
    intro n hn
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hd.analyticAt z)]
    intro m hm
    exact h ⟨(z, m), (by exact_mod_cast hm : (m : ℕ∞) < n).trans_le hn⟩
  · intro h i
    have hm : ((i.val.2 + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g i.val.1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENat.add_one_le_iff (ENat.natCast_ne_top i.val.2)).mpr i.property
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (hd.analyticAt i.val.1)).mp (hm.trans (h i.val.1)) i.val.2 (Nat.lt_succ_self _)

/-- The annihilator in the inherited strong-dual topology. -/
def compactOpenEntireAnnihilator (g : ℂ → ℂ) :
    Submodule ℂ (StrongDual ℂ CompactOpenEntire) :=
  (compactOpenEntireDivisor g).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ)

/-- Restricting an entire functional to Bergman tests gives the canonical
continuous injection with strongly dense range on the divisor quotient. -/
theorem exists_compactOpenEntire_restriction (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (a b : ℝ) (hab : a ≤ b) (hstrip : ∀ z : ℂ, 0 < analyticOrderAt g z → z.re ∈ Icc a b) :
    let D := bergmanDivisorSubmodule g
    let A := compactOpenEntireAnnihilator g
    ∃ T : A →L[ℂ] StrongDual ℂ (B ⧸ D),
      Injective T ∧ DenseRange T ∧
      ∀ (l : A) (f : B), T l (D.mkQ f) = l.val (bergmanToCompactOpenEntire f) := by
  intro D A
  let M := bergmanToCompactOpenEntire
  let W := compactOpenEntireDivisor g
  let Q := B ⧸ D
  have hD (f : B) : f ∈ D ↔ M f ∈ W := by
    rw [bergmanDivisorSubmodule_mem_iff hg, compactOpenEntireDivisor_mem_iff hg]
    rfl
  have hzero (l : A) (f : B) (hf : f ∈ D) : l.val (M f) = 0 :=
    (Submodule.mem_dualAnnihilator l.val.toLinearMap).mp l.property (M f) ((hD f).mp hf)
  let V : A →ₗ[ℂ] StrongDual ℂ Q :=
    { toFun := fun l ↦ D.liftQL (l.val.comp M) (hzero l)
      map_add' := fun l m ↦ by
        ext q
        obtain ⟨f, rfl⟩ := D.mkQ_surjective q
        rfl
      map_smul' := fun c l ↦ by
        ext q
        obtain ⟨f, rfl⟩ := D.mkQ_surjective q
        rfl }
  have hF := schwartzBergman_frechet (univ : Set ℝ) isOpen_univ ordConnected_univ univ_nonempty
  letI : IsTopologicalAddGroup B := hF.choose
  letI : PolynormableSpace ℂ B := hF.choose_spec.1
  have hN : NuclearLocallyConvex.{0,0} B := nuclearLocallyConvex_of_equiv entireLogMellin
    (positiveRealExponentialDecay_nuclear univ univ_nonempty)
  have he := quotientDual_strongEmbedding_of_nuclear D (bergmanDivisorSubmodule_isClosed hg) hN hF
  have hV : Continuous V := by
    apply he.isInducing.continuous_iff.mpr
    change Continuous (fun l : A ↦ (l.val.comp M : StrongDual ℂ B))
    let P : StrongDual ℂ CompactOpenEntire →L[ℂ] StrongDual ℂ B :=
      ContinuousLinearMap.precomp (E := B) (F := CompactOpenEntire) (G := ℂ)
        (σ := RingHom.id ℂ) (τ := RingHom.id ℂ) (ρ := RingHom.id ℂ) M
    exact (P.continuous.comp (continuous_subtype_val : Continuous (Subtype.val : A → _))).congr
      (fun _ ↦ rfl)
  let T : A →L[ℂ] StrongDual ℂ Q := ⟨V, hV⟩
  have hT (l : A) (f : B) : T l (D.mkQ f) = l.val (M f) := rfl
  refine ⟨T, ?_, ?_, hT⟩
  · intro l₁ l₂ hl
    apply Subtype.ext
    apply DFunLike.ext
    intro y
    have heq := bergmanToCompactOpenEntire_denseRange.equalizer l₁.val.continuous l₂.val.continuous (by
      funext f
      exact (hT l₁ f).symm.trans
        ((congrArg (fun l : StrongDual ℂ Q ↦ l (D.mkQ f)) hl).trans (hT l₂ f)))
    exact congrFun heq y
  · obtain ⟨J, hJ, _, _⟩ := bergmanDivisor_normalizedJets g a b hab
    have hJ' (i) (f : B) : J i (D.mkQ f) = bergmanNormalizedJet i.val.1 i.val.2 f :=
      (hJ i f).trans (bergmanNormalizedJet_apply _ _ _).symm
    have hdense := bergmanDivisor_normalizedJets_span_dense g hg a b hstrip J hJ'
    apply Dense.mono _ hdense
    change Submodule.span ℂ (range J) ≤ T.toLinearMap.range
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let t : Indices g := ⟨((i.val.1 : ℂ), i.val.2), i.property⟩
    let l₀ := compactOpenEntireJet t.val.1 t.val.2
    let l : A := ⟨((i.val.2.factorial : ℂ)⁻¹) • l₀,
      (Submodule.mem_dualAnnihilator _).mpr fun x hx ↦ by
        simp only [compactOpenEntireDivisor, Submodule.mem_iInf, LinearMap.mem_ker,
          ContinuousLinearMap.coe_coe] at hx
        have h : l₀ x = 0 := hx t
        change (i.val.2.factorial : ℂ)⁻¹ * l₀ x = 0
        rw [h, mul_zero]⟩
    refine ⟨l, ?_⟩
    ext q
    obtain ⟨f, rfl⟩ := D.mkQ_surjective q
    change T l (D.mkQ f) = J i (D.mkQ f)
    rw [hT, hJ', bergmanNormalizedJet_apply]
    rfl

section Global

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev K := normOneIdeleClass F
local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩
local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩

variable (ν : Measure (K F)) [ν.IsHaarMeasure] (η : Measure (Idele F)) [η.IsHaarMeasure]
variable [∀ v : Place F, MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : Place F, BorelSpace (v.adicCompletion F)ˣ]
  (μ : ∀ v : Place F, Measure (v.adicCompletion F)ˣ)
  [∀ v : Place F, (μ v).IsHaarMeasure] [∀ v : Place F, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (hν : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F ν))
variable (ω : PontryaginDual (K F))

private abbrev Test := (GlobalBruhat.polarEvaluation F).ker
private abbrev X := (Test F).map (globalIdelicZetaComponentKernel F η ω).mkQ
private abbrev H := GlobalCoprimeDecay F ω

include μ hν in
set_option maxHeartbeats 1400000 in
/-- Theorem 7.1.4.2(2), canonical global restriction. The domain is the
actual compact-open entire Hecke annihilator. The target is the strong dual
of the native decay quotient by the homogeneous theta image. -/
theorem exists_globalSpectral_nativeRestriction :
    ∃ (r : GlobalBruhat F) (M : H F ω ≃L[ℂ] B)
      (j : X F η ω →L[ℂ] H F ω),
      let A := compactOpenEntireAnnihilator (globalHeckeClearedZeta F ν ω r)
      let R := j.toLinearMap.range
      ∃ U : A →L[ℂ] StrongDual ℂ (H F ω ⧸ R),
        IsClosedEmbedding j ∧
        (∀ f : Test F, ∀ g, (j (globalPolarFreeTestClass F η ω f)).val.val g =
          adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f.val).val g) ∧
        Injective U ∧ DenseRange U ∧
        ∀ (l : A) (u : H F ω),
          U l (R.mkQ u) = l.val (bergmanToCompactOpenEntire (M u)) := by
  obtain ⟨r, hr, hmin⟩ := exists_globalHeckeOrderReference F η ν ω μ hν
  obtain ⟨M, j, q, hj, hjval, _, hq⟩ :=
    exists_globalSpectral_thetaMellinQuotient F ω ν η μ hν r hr hmin
  let g := globalHeckeClearedZeta F ν ω r
  have hg : Differentiable ℂ g := fun z ↦ (globalHeckeClearedZeta_analytic F ν ω r z).differentiableAt
  have hstrip (z : ℂ) (hz : 0 < analyticOrderAt g z) : z.re ∈ Icc (0 : ℝ) 1 := by
    by_contra h
    have hout : z.re < 0 ∨ 1 < z.re := by simpa only [mem_Icc, not_and_or, not_le] using h
    rw [show analyticOrderAt g z = 0 from
      globalHeckeClearedZeta_order_zero_off_strip F ν η μ hν ω r hmin z hout] at hz
    exact lt_irrefl _ hz
  obtain ⟨T, hi, hd, hT⟩ := exists_compactOpenEntire_restriction g hg 0 1 zero_le_one hstrip
  let e := strongDualPrecompEquiv q
  refine ⟨r, M, j, e.toContinuousLinearMap.comp T, hj, hjval, e.injective.comp hi,
    e.surjective.denseRange.comp hd e.continuous, ?_⟩
  intro l u
  change T l (q (j.toLinearMap.range.mkQ u)) = _
  rw [hq, hT]

end Global

#print axioms bergmanToCompactOpenEntire
#print axioms bergmanToCompactOpenEntire_denseRange
#print axioms exists_compactOpenEntire_restriction
#print axioms exists_globalSpectral_nativeRestriction

end

end Masullo
