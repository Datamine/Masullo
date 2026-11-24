import ExponentialPeriodization
import SchwartzDifferenceTails
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Filter Function MeasureTheory Set Topology
open scoped ContDiff FourierTransform SchwartzMap

noncomputable section

namespace Masullo

variable (d : ℝ) [Fact (0 < d)]

private theorem schwartzPeriodization_cyclicDifference (f : 𝓢(ℝ, ℂ)) :
    schwartzPeriodizationCLM d (schwartzCyclicDifference (d, 1) f) = 0 := by
  apply Subtype.ext
  funext x
  change (∑' m : ℤ, schwartzCyclicDifference (d, 1) f (x + d * m)) = 0
  have hs := schwartzIntegerTranslate_summable d f x
  let t (m : ℤ) := f (x + d * m)
  have he (m : ℤ) : x + d * (m : ℝ) + d = x + d * ((m + 1 : ℤ) : ℝ) := by push_cast; ring
  simp only [schwartzCyclicDifference_apply, Circle.coe_one, one_mul, he]
  change (∑' m : ℤ, (t m - t ((Equiv.addRight (1 : ℤ)) m))) = 0
  calc
    _ = (∑' m : ℤ, t m) - (∑' m : ℤ, t ((Equiv.addRight (1 : ℤ)) m)) :=
      hs.tsum_sub ((Equiv.addRight (1 : ℤ)).summable_iff.mpr hs)
    _ = 0 := sub_eq_zero.mpr ((Equiv.addRight (1 : ℤ)).tsum_eq t).symm

/-- The ordinary periodization vanishes exactly on the range of the
untwisted cyclic difference. -/
theorem schwartzPeriodization_ker_eq_cyclicDifference_range :
    (schwartzPeriodizationCLM d).ker = (schwartzCyclicDifference (d, 1)).range := by
  let P := schwartzPeriodizationCLM d
  let D := schwartzCyclicDifference (d, 1)
  obtain ⟨S₀, hS₀, hS₀K⟩ := exponentialPeriodization_split d
  let S := (expSchwartzEvaluation 0).comp S₀
  have hS : RightInverse S P := hS₀
  have hSc (f : SmoothPeriodic d) : HasCompactSupport (S f) :=
    HasCompactSupport.intro isCompact_Icc
      (fun _ hx ↦ notMem_support.mp fun h ↦ hx (hS₀K f h))
  have hc (f : 𝓢(ℝ, ℂ)) (hf : P f = 0) (hfK : HasCompactSupport f) : f ∈ D.range := by
    obtain ⟨a, ha⟩ := hfK.isCompact.bddBelow
    obtain ⟨b, hb⟩ := hfK.isCompact.bddAbove
    have hsub : support f ⊆ Icc a b := fun x hx ↦
      ⟨ha (subset_closure hx), hb (subset_closure hx)⟩
    have hz (x : ℝ) : integerPeriodization d f x = 0 :=
      congrArg (fun q : SmoothPeriodic d ↦ q.val x) hf
    obtain ⟨ψ, hψC, hψK, hψ⟩ :=
      compact_periodization_difference hsub (f.smooth ⊤) (Fact.out : 0 < d) hz
    have hψc : HasCompactSupport ψ :=
      HasCompactSupport.intro isCompact_Icc (fun _ hx ↦ notMem_support.mp fun h ↦ hx (hψK h))
    refine ⟨hψc.toSchwartzMap hψC, SchwartzMap.ext fun x ↦ ?_⟩
    exact (schwartzCyclicDifference_apply (d, 1) (hψc.toSchwartzMap hψC) x).trans
      (by
        change ψ x - ((1 : Circle) : ℂ) * ψ (x + d) = f x
        rw [Circle.coe_one, one_mul]
        exact hψ x)
  apply le_antisymm
  · intro f hf
    change P f = 0 at hf
    let fN (n : ℕ) := truncateSchwartz n f
    let g (n : ℕ) := fN n - S (P (fN n))
    have hmem (n : ℕ) : g n ∈ D.range := by
      apply hc
      · change P (fN n - S (P (fN n))) = 0
        rw [map_sub, hS, sub_self]
      · exact (truncateSchwartz_hasCompactSupport n f).sub (hSc _)
    have hfN : Tendsto fN atTop (𝓝 f) := truncateSchwartz_tendsto f
    have hzero : Tendsto (fun n ↦ S (P (fN n))) atTop (𝓝 0) := by
      have h := (S.continuous.comp P.continuous).continuousAt.tendsto.comp hfN
      simpa only [Function.comp_def, hf, map_zero] using h
    have hg : Tendsto g atTop (𝓝 f) := by simpa only [g, sub_zero] using hfN.sub hzero
    have hclosed : IsClosed (D.range : Set 𝓢(ℝ, ℂ)) :=
      (schwartzCyclicDifference_isClosedEmbedding (d, 1) Fact.out).isClosed_range
    exact hclosed.mem_of_tendsto hg (Eventually.of_forall hmem)
  · rintro _ ⟨f, rfl⟩
    exact schwartzPeriodization_cyclicDifference d f

variable {d} in
private def liftCompactSchwartz (I : Set ℝ) (hI : I.Nonempty) {K : Set ℝ} (hK : IsCompact K) :
    LogFixedTest K →L[ℂ] PositiveRealExponentialDecay I := by
  let L := realSchwartzCoe.comp (fixedSupportSchwartz K).subtype
  let T := L.codRestrict (logExponentialDecaySubmodule I) fun f ↦
    (Submodule.mem_iInf _).mpr fun a ↦ ⟨fixedExpSchwartzCoordinate hK a f,
      funext (fixedExpSchwartzCoordinate_apply hK a f)⟩
  refine ⟨T, (positiveRealExponentialDecay_isEmbedding I hI).isInducing.continuous_iff.mpr ?_⟩
  apply continuous_pi
  intro a
  refine (fixedExpSchwartzCoordinate hK a).continuous.congr fun f ↦ SchwartzMap.ext fun x ↦ ?_
  erw [logExponentialDecayTwist_apply, fixedExpSchwartzCoordinate_apply]
  rfl

omit [Fact (0 < d)] in
private theorem zeroInclusion_liftCompactSchwartz (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    {K : Set ℝ} (hK : IsCompact K) (f : LogFixedTest K) :
    positiveRealExponentialDecay_zeroInclusion I h0 (liftCompactSchwartz I ⟨0, h0⟩ hK f) =
      (f : 𝓢(ℝ, ℂ)) :=
  SchwartzMap.ext (positiveRealExponentialDecay_zeroInclusion_apply I h0 _)

private def schwartzPhase (a : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ Complex.exp (((a : ℂ) * Complex.I) * (x : ℂ)))

private theorem schwartzPhase_apply (a : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzPhase a f x = Complex.exp (((a : ℂ) * Complex.I) * (x : ℂ)) * f x :=
  SchwartzMap.smulLeftCLM_apply_apply (mellinPhase_hasTemperateGrowth a) f x

private theorem schwartzPhase_neg (a : ℝ) (f : 𝓢(ℝ, ℂ)) :
    schwartzPhase (-a) (schwartzPhase a f) = f := by
  apply SchwartzMap.ext
  intro x
  rw [schwartzPhase_apply, schwartzPhase_apply, ← mul_assoc, ← Complex.exp_add,
    show ((((-a : ℝ) : ℂ) * Complex.I) * (x : ℂ)) + ((a : ℂ) * Complex.I) * (x : ℂ) = 0
      by push_cast; ring, Complex.exp_zero, one_mul]

private theorem schwartzPhase_intertwines (c : Circle) (f : 𝓢(ℝ, ℂ)) :
    schwartzPhase (Complex.arg (c : ℂ) / d) (schwartzCyclicDifference (d, c) f) =
      schwartzCyclicDifference (d, 1) (schwartzPhase (Complex.arg (c : ℂ) / d) f) := by
  let a := Complex.arg (c : ℂ) / d
  have he : Complex.exp (((a : ℂ) * Complex.I) * (d : ℂ)) = (c : ℂ) := by
    have hd : d ≠ 0 := (Fact.out : 0 < d).ne'
    rw [mul_right_comm, ← Complex.ofReal_mul, show a * d = Complex.arg (c : ℂ) from
      div_mul_cancel₀ _ hd]
    simpa only [Circle.norm_coe, Complex.ofReal_one, one_mul] using
      Complex.norm_mul_exp_arg_mul_I (c : ℂ)
  apply SchwartzMap.ext
  intro x
  change schwartzPhase a (schwartzCyclicDifference (d, c) f) x =
    schwartzCyclicDifference (d, 1) (schwartzPhase a f) x
  rw [schwartzPhase_apply, schwartzCyclicDifference_apply, schwartzCyclicDifference_apply,
    schwartzPhase_apply, schwartzPhase_apply]
  simp only [Circle.coe_one, one_mul, Complex.ofReal_add, mul_add, Complex.exp_add,
    mul_sub, mul_assoc]
  rw [← mul_assoc (a : ℂ) Complex.I (d : ℂ), he]

/-- Vanishing of the Fourier samples at the twisted cyclic frequencies
implies division by the cyclic difference in the Schwartz space. -/
theorem schwartzCyclicDifference_mem_range_of_samples_zero (c : Circle) (f : 𝓢(ℝ, ℂ))
    (h : ∀ n : ℤ, (∫ x : ℝ,
      Complex.exp ((((Complex.arg (c : ℂ) / d - 2 * Real.pi * ((n : ℝ) / d) : ℝ) : ℂ) *
        Complex.I) * (x : ℂ)) * f x) = 0) :
    f ∈ (schwartzCyclicDifference (d, c)).range := by
  let a := Complex.arg (c : ℂ) / d
  let σ := schwartzPhase a
  let P := schwartzPeriodizationCLM d
  have hcoef (n : ℤ) : periodicFourierCoefficient d (P (σ f)) n = 0 := by
    rw [schwartzPeriodization_coefficient]
    have hF : (𝓕 (σ f)) ((n : ℝ) / d) = 0 := by
      rw [SchwartzMap.fourier_coe, Real.fourier_eq']
      convert h n using 1
      apply integral_congr_ae
      refine .of_forall fun x ↦ ?_
      change Complex.exp (((-2 * Real.pi * inner ℝ x ((n : ℝ) / d) : ℝ) : ℂ) *
        Complex.I) • σ f x =
        Complex.exp ((((Complex.arg (c : ℂ) / d - 2 * Real.pi * ((n : ℝ) / d) : ℝ) : ℂ) *
          Complex.I) * (x : ℂ)) * f x
      rw [Real.inner_apply, smul_eq_mul, show σ f x = _ from schwartzPhase_apply a f x,
        ← mul_assoc, ← Complex.exp_add]
      dsimp only [a]
      push_cast
      ring_nf
    rw [hF, smul_zero]
  have hs : HasSum (fun _ : ℤ ↦ (0 : SmoothPeriodic d)) (P (σ f)) := by
    simpa only [hcoef, zero_smul] using periodicFourierSeries_hasSum d (P (σ f))
  letI : T2Space (SmoothPeriodic d) :=
    (show IsEmbedding (periodicChart d Fact.out) from ⟨⟨rfl⟩, periodicChart_injective d Fact.out⟩).t2Space
  have hz : P (σ f) = 0 := hs.unique hasSum_zero
  have hr : σ f ∈ (schwartzCyclicDifference (d, 1)).range := by
    rw [← schwartzPeriodization_ker_eq_cyclicDifference_range d]
    exact hz
  obtain ⟨g, hg⟩ := hr
  let u := schwartzPhase (-a) g
  have hu : σ u = g := by
    simpa only [neg_neg] using schwartzPhase_neg (-a) g
  have hi : Injective σ := (show LeftInverse (schwartzPhase (-a)) σ from schwartzPhase_neg a).injective
  exact ⟨u, hi ((schwartzPhase_intertwines d c u).trans ((congrArg
    (schwartzCyclicDifference (d, 1)) hu).trans hg))⟩

/-- An ordinary cyclic-difference quotient class has a continuously chosen,
compactly supported representative in every weighted Schwartz space. -/
theorem schwartzCyclicDifference_weighted_representatives (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (c : Circle) :
    ∃ S : 𝓢(ℝ, ℂ) →L[ℂ] PositiveRealExponentialDecay I,
      (∀ f, f - positiveRealExponentialDecay_zeroInclusion I h0 (S f) ∈
        (schwartzCyclicDifference (d, c)).range) ∧
      ∀ f, support (S f).val ⊆ Icc (-d) d := by
  let K := Icc (-d) d
  have hd : 0 < d := Fact.out
  have hK : IsCompact K := isCompact_Icc
  have hcov : ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K := by
    rw [show K = Icc (-d) d by rfl, interior_Icc]
    exact openInterval_covers_integerTranslations hd (by linarith)
  obtain ⟨B, hB⟩ := exists_compactPeriodicSection d hK hcov
  let a := Complex.arg (c : ℂ) / d
  let R := (schwartzPhase (-a)).comp (fixedSupportSchwartz K).subtypeL
  let R₀ : LogFixedTest K →L[ℂ] LogFixedTest K :=
    R.codRestrict _ fun f x hx ↦ by
      apply f.property
      intro h
      apply hx
      change schwartzPhase (-a) (f : 𝓢(ℝ, ℂ)) x = 0
      rw [schwartzPhase_apply, show (f : 𝓢(ℝ, ℂ)) x = 0 from h, mul_zero]
  let P := schwartzPeriodizationCLM d
  let S := (liftCompactSchwartz I ⟨0, h0⟩ hK).comp (R₀.comp (B.comp (P.comp (schwartzPhase a))))
  refine ⟨S, fun f ↦ ?_, fun f ↦ (R₀ (B (P (schwartzPhase a f)))).property⟩
  let y := P (schwartzPhase a f)
  have hy : schwartzPhase a f - (B y : 𝓢(ℝ, ℂ)) ∈ P.ker := by
    change P (schwartzPhase a f - (B y : 𝓢(ℝ, ℂ))) = 0
    rw [map_sub]
    change y - periodizationCLM d hK (B y) = 0
    rw [hB, sub_self]
  rw [show P = schwartzPeriodizationCLM d by rfl, schwartzPeriodization_ker_eq_cyclicDifference_range] at hy
  obtain ⟨z, hz⟩ := hy
  refine ⟨schwartzPhase (-a) z, ?_⟩
  have hleft : LeftInverse (schwartzPhase (-a)) (schwartzPhase a) := schwartzPhase_neg a
  have hi : Injective (schwartzPhase a) := hleft.injective
  apply hi
  have hinter := schwartzPhase_intertwines d c (schwartzPhase (-a) z)
  change schwartzPhase a (schwartzCyclicDifference (d, c) (schwartzPhase (-a) z)) = _
  rw [show schwartzPhase a (schwartzCyclicDifference (d, c) (schwartzPhase (-a) z)) =
    schwartzCyclicDifference (d, 1) (schwartzPhase a (schwartzPhase (-a) z)) from hinter, map_sub]
  have hneg (x : 𝓢(ℝ, ℂ)) : schwartzPhase a (schwartzPhase (-a) x) = x := by
    simpa only [neg_neg] using schwartzPhase_neg (-a) x
  change schwartzCyclicDifference (d, 1) z = schwartzPhase a f - (B y : 𝓢(ℝ, ℂ)) at hz
  rw [hneg, hz]
  change _ = schwartzPhase a f -
    schwartzPhase a (positiveRealExponentialDecay_zeroInclusion I h0
      (liftCompactSchwartz I ⟨0, h0⟩ hK (R₀ (B y))))
  rw [zeroInclusion_liftCompactSchwartz]
  change _ = schwartzPhase a f - schwartzPhase a (schwartzPhase (-a) (B y : 𝓢(ℝ, ℂ)))
  rw [hneg]

omit [Fact (0 < d)] in
/-- For a finite product of twisted differences, representatives can be chosen
continuously with one logarithmic support interval for the entire quotient. -/
theorem schwartzCyclicDifferenceProduct_weighted_representatives
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    ∃ S : 𝓢(ℝ, ℂ) →L[ℂ] PositiveRealExponentialDecay I,
      (∀ f, f - positiveRealExponentialDecay_zeroInclusion I h0 (S f) ∈
        (schwartzCyclicDifferenceProduct gs).range) ∧
      ∀ f, support (S f).val ⊆ Icc (-(gs.map Prod.fst).sum) (gs.map Prod.fst).sum := by
  let J := positiveRealExponentialDecay_zeroInclusion I h0
  induction gs with
  | nil =>
    refine ⟨0, fun f ↦ ⟨f - J 0, ?_⟩, fun f x hx ↦ ?_⟩
    · simp [schwartzCyclicDifferenceProduct]
    · exact (hx rfl).elim
  | cons g gs ih =>
    have htail (a : ℝ × Circle) (ha : a ∈ gs) : 0 < a.1 :=
      hgs a (List.mem_cons_of_mem _ ha)
    obtain ⟨S, hS, hKS⟩ := ih htail
    have hg := hgs g List.mem_cons_self
    letI : Fact (0 < g.1) := ⟨hg⟩
    obtain ⟨S₀, hS₀, hKS₀⟩ := schwartzCyclicDifference_weighted_representatives g.1 I h0 g.2
    let A := schwartzCyclicDifference g
    let A₀ := logDecayCyclicDifference I ⟨0, h0⟩ g
    -- Remove the first representative and divide the residual by the first difference.
    let M := ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) - J.comp S₀
    let M₀ := M.codRestrict A.range (fun f ↦ hS₀ f)
    have hA := schwartzCyclicDifference_isClosedEmbedding g (hgs g List.mem_cons_self)
    let e := LinearEquiv.ofInjective A.toLinearMap hA.injective
    have he : Continuous e.symm := hA.isEmbedding.isInducing.continuous_iff.mpr (by
      change Continuous (fun x : A.range ↦ (e (e.symm x)).val)
      simp only [e.apply_symm_apply]
      exact continuous_subtype_val)
    let E : A.range →L[ℂ] 𝓢(ℝ, ℂ) := ⟨e.symm.toLinearMap, he⟩
    let T := E.comp M₀
    have hT (f : 𝓢(ℝ, ℂ)) : A (T f) = f - J (S₀ f) :=
      congrArg Subtype.val (e.apply_symm_apply (M₀ f))
    have hJ (f : PositiveRealExponentialDecay I) : J (A₀ f) = A (J f) :=
      zeroInclusion_intertwines_cyclicDifferenceProduct I h0 [g] f
    refine ⟨S₀ + A₀.comp (S.comp T), fun f ↦ ?_, fun f x hx ↦ ?_⟩
    · obtain ⟨v, hv⟩ := hS (T f)
      refine ⟨v, ?_⟩
      change A (schwartzCyclicDifferenceProduct gs v) = f - J (S₀ f + A₀ (S (T f)))
      change schwartzCyclicDifferenceProduct gs v = T f - J (S (T f)) at hv
      rw [hv, map_sub, hT, map_add, hJ, sub_sub]
    · change x ∈ Icc (-(g.1 + (gs.map Prod.fst).sum)) (g.1 + (gs.map Prod.fst).sum)
      have hwidth : 0 ≤ (gs.map Prod.fst).sum :=
        List.sum_nonneg fun a ha ↦ by
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          exact (htail k hk).le
      by_contra hxK
      have hzero₀ : (S₀ f).val x = 0 := notMem_support.mp fun h ↦
        hxK (by
          obtain ⟨hl, hu⟩ := hKS₀ f h
          exact ⟨by linarith, by linarith⟩)
      have hzero : (S (T f)).val x = 0 := notMem_support.mp fun h ↦
        hxK (by
          obtain ⟨hl, hu⟩ := hKS (T f) h
          exact ⟨by linarith, by linarith⟩)
      have hzeroShift : (S (T f)).val (x + g.1) = 0 := notMem_support.mp fun h ↦
        hxK (by
          obtain ⟨hl, hu⟩ := hKS (T f) h
          exact ⟨by linarith, by linarith⟩)
      apply hx
      change (S₀ f).val x + ((S (T f)).val x -
        (g.2 : ℂ) * (S (T f)).val (x + g.1)) = 0
      simp only [hzero₀, hzero, hzeroShift, mul_zero, sub_zero, add_zero]

/-- In real logarithmic coordinates the canonical comparison for any list
of positive cyclic differences is a continuous linear equivalence. -/
def logDecayCyclicDifferenceProduct_quotientEquiv (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    (PositiveRealExponentialDecay I ⧸ (logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs).range)
      ≃L[ℂ] (𝓢(ℝ, ℂ) ⧸ (schwartzCyclicDifferenceProduct gs).range) := by
  let W := (logDecayCyclicDifferenceProduct I ⟨0, h0⟩ gs).range
  let V := (schwartzCyclicDifferenceProduct gs).range
  let J := positiveRealExponentialDecay_zeroInclusion I h0
  let C := logDecayCyclicDifferenceProduct_quotientComparison I h0 gs hgs
  have hC := logDecayCyclicDifferenceProduct_quotientComparison_injective I h0 gs hgs
  let exS := schwartzCyclicDifferenceProduct_weighted_representatives I h0 gs hgs
  let S := exS.choose
  let R := W.mkQL.comp S
  have hCR (f : 𝓢(ℝ, ℂ)) : C (R f) = V.mkQ f := by
    change V.mkQ (J (S f)) = V.mkQ f
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [← neg_sub]
    exact V.neg_mem (exS.choose_spec.1 f)
  let U := V.liftQL R (fun f hf ↦ by
    change R f = 0
    apply hC
    rw [hCR, map_zero]
    exact (Submodule.Quotient.mk_eq_zero V).mpr hf)
  have hright : RightInverse U C := by
    intro q
    obtain ⟨f, rfl⟩ := V.mkQ_surjective q
    exact hCR f
  have hleft : LeftInverse U C := fun q ↦ hC (hright (C q))
  exact ⟨LinearEquiv.ofLinear C.toLinearMap U.toLinearMap
    (LinearMap.ext hright) (LinearMap.ext hleft), C.continuous, U.continuous⟩

@[simp] theorem logDecayCyclicDifferenceProduct_quotientEquiv_mk (I : Set ℝ)
    (h0 : (0 : ℝ) ∈ I) (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1)
    (f : PositiveRealExponentialDecay I) :
    logDecayCyclicDifferenceProduct_quotientEquiv I h0 gs hgs (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (positiveRealExponentialDecay_zeroInclusion I h0 f) := rfl

/-- The first quotient comparison for nested sets of weights in scalar
logarithmic coordinates, in particular from all exponents to an interval. -/
def logDecayCyclicDifferenceProduct_quotientRestrict (I J : Set ℝ) (hI : (0 : ℝ) ∈ I)
    (hJ : (0 : ℝ) ∈ J) (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1) :
    (PositiveRealExponentialDecay I ⧸ (logDecayCyclicDifferenceProduct I ⟨0, hI⟩ gs).range)
      ≃L[ℂ]
    (PositiveRealExponentialDecay J ⧸ (logDecayCyclicDifferenceProduct J ⟨0, hJ⟩ gs).range) :=
  (logDecayCyclicDifferenceProduct_quotientEquiv I hI gs hgs).trans
    (logDecayCyclicDifferenceProduct_quotientEquiv J hJ gs hgs).symm

theorem logDecayCyclicDifferenceProduct_quotientRestrict_mk (I J : Set ℝ)
    (hI : (0 : ℝ) ∈ I) (hJ : (0 : ℝ) ∈ J) (hJI : J ⊆ I)
    (gs : List (ℝ × Circle)) (hgs : ∀ g ∈ gs, 0 < g.1)
    (f : PositiveRealExponentialDecay I) :
    logDecayCyclicDifferenceProduct_quotientRestrict I J hI hJ gs hgs (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (⟨f.val, (Submodule.mem_iInf _).mpr fun a ↦
        (Submodule.mem_iInf _).mp f.property ⟨a, hJI a.property⟩⟩ : PositiveRealExponentialDecay J) := by
  let E := logDecayCyclicDifferenceProduct_quotientEquiv J hJ gs hgs
  apply E.injective
  change E (E.symm (logDecayCyclicDifferenceProduct_quotientEquiv I hI gs hgs
    (Submodule.Quotient.mk f))) = E (Submodule.Quotient.mk _)
  rw [E.apply_symm_apply, logDecayCyclicDifferenceProduct_quotientEquiv_mk]
  have he (u : PositiveRealExponentialDecay J) :
      E (Submodule.Quotient.mk u) =
        Submodule.Quotient.mk (positiveRealExponentialDecay_zeroInclusion J hJ u) :=
    logDecayCyclicDifferenceProduct_quotientEquiv_mk J hJ gs hgs u
  refine Eq.trans ?_ (he _).symm
  congr 1

end Masullo
