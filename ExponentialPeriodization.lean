import SchwartzPeriodization
import ExponentialSchwartzCutoffs
import PeriodicDifference
import Mathlib.Analysis.MellinInversion

open Bornology Filter Function MeasureTheory Set Topology
open scoped ContDiff FourierTransform SchwartzMap

namespace Masullo

noncomputable section

variable (d : ℝ) [Fact (0 < d)]

/-- Periodization on exponentially decaying profiles is the ordinary
Schwartz periodization on the weight-zero coordinate. -/
def exponentialPeriodization : ExpSchwartz →L[ℂ] SmoothPeriodic d :=
  (schwartzPeriodizationCLM d).comp (expSchwartzEvaluation 0)

@[simp] theorem exponentialPeriodization_apply (f : ExpSchwartz) (x : ℝ) :
    (exponentialPeriodization d f).val x =
      ∑' m : ℤ, expSchwartzEvaluation 0 f (x + d * m) := rfl

@[simp] theorem expSchwartzEvaluation_extendFixed_zero {K : Set ℝ}
    (hK : IsCompact K) (f : LogFixedTest K) :
    expSchwartzEvaluation 0 (extendFixedExpSchwartz hK f).val = f.val := by
  ext x
  change fixedExpSchwartzCoordinate hK 0 f x = f.val x
  rw [fixedExpSchwartzCoordinate_apply]
  simp

/-- Compact fixed-support lifts give a continuous linear section on the
exponential Schwartz space. -/
theorem exponentialPeriodization_hasSection {K : Set ℝ} (hK : IsCompact K)
    (hcov : ∀ x : ℝ, ∃ n : ℤ, x + d * (n : ℝ) ∈ interior K) :
    ∃ S : SmoothPeriodic d →L[ℂ] ExpSchwartz,
      RightInverse S (exponentialPeriodization d) ∧
        ∀ f, support (expSchwartzEvaluation 0 (S f)) ⊆ K := by
  obtain ⟨S, hS⟩ := exists_compactPeriodicSection d hK hcov
  refine ⟨(ExpSchwartzFixed K).subtypeL.comp ((extendFixedExpSchwartz hK).comp S), ?_, ?_⟩
  · intro f
    apply Subtype.ext
    funext x
    have he := congrArg (fun g : SmoothPeriodic d => g.val x) (hS f)
    change (schwartzPeriodizationCLM d
      (expSchwartzEvaluation 0 (extendFixedExpSchwartz hK (S f)).val)).val x = f.val x
    rw [expSchwartzEvaluation_extendFixed_zero]
    exact he
  · intro f
    change support (expSchwartzEvaluation 0 (extendFixedExpSchwartz hK (S f)).val) ⊆ K
    rw [expSchwartzEvaluation_extendFixed_zero]
    exact (S f).property

theorem exponentialPeriodization_split :
    ∃ S : SmoothPeriodic d →L[ℂ] ExpSchwartz,
      RightInverse S (exponentialPeriodization d) ∧
        ∀ f, support (expSchwartzEvaluation 0 (S f)) ⊆ Icc (-d) d := by
  have hpos : 0 < d := Fact.out
  refine exponentialPeriodization_hasSection d (K := Icc (-d) d) isCompact_Icc ?_
  rw [interior_Icc]
  exact openInterval_covers_integerTranslations hpos (by linarith)

private def exponentialPeriodizationSection : SmoothPeriodic d →L[ℂ] ExpSchwartz :=
  (exponentialPeriodization_split d).choose

private theorem exponentialPeriodizationSection_right :
    RightInverse (exponentialPeriodizationSection d) (exponentialPeriodization d) :=
  (exponentialPeriodization_split d).choose_spec.1

private theorem exponentialPeriodizationSection_compact (f : SmoothPeriodic d) :
    HasCompactSupport (expSchwartzEvaluation 0 (exponentialPeriodizationSection d f)) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx =>
    notMem_support.mp (fun h => hx ((exponentialPeriodization_split d).choose_spec.2 f h)))

theorem exponentialPeriodization_surjective : Surjective (exponentialPeriodization d) :=
  (exponentialPeriodizationSection_right d).surjective

theorem exponentialPeriodization_isOpenMap : IsOpenMap (exponentialPeriodization d) := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨f, hf, rfl⟩
  let P := exponentialPeriodization d
  let S := exponentialPeriodizationSection d
  have hS : RightInverse S P := exponentialPeriodizationSection_right d
  let V (z : SmoothPeriodic d) := f + S (z - P f)
  letI : IsTopologicalAddGroup (SmoothPeriodic d) :=
    (smoothPeriodic_withDerivativeSeminorms d).topologicalAddGroup
  have hV : Continuous V := continuous_const.add (S.continuous.comp (continuous_id.sub continuous_const))
  have hfix : V (P f) = f := by simp [V, S, P]
  have hmem : P f ∈ V ⁻¹' U := by
    change V (P f) ∈ U
    rwa [hfix]
  have hVU : V ⁻¹' U ∈ 𝓝 (P f) := (hV.isOpen_preimage _ hU).mem_nhds hmem
  refine mem_of_superset hVU (fun z hz => ⟨V z, hz, ?_⟩)
  change P (f + S (z - P f)) = z
  rw [map_add, hS, add_sub_cancel]

/-- A continuous linear section identifies the kernel quotient with the
smooth periodic target. -/
def exponentialPeriodizationQuotient :
    (ExpSchwartz ⧸ (exponentialPeriodization d).ker) ≃L[ℂ] SmoothPeriodic d := by
  let P := exponentialPeriodization d
  let S := exponentialPeriodizationSection d
  let F := P.ker.liftQL P le_rfl
  let R := P.ker.mkQL.comp S
  have hright (f : SmoothPeriodic d) : F (R f) = f := exponentialPeriodizationSection_right d f
  have hleft (q : ExpSchwartz ⧸ P.ker) : R (F q) = q := by
    obtain ⟨f, rfl⟩ := P.ker.mkQ_surjective q
    change Submodule.Quotient.mk (S (P f)) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq]
    change P (S (P f) - f) = 0
    rw [map_sub, exponentialPeriodizationSection_right d (P f), sub_self]
  exact { toLinearEquiv := LinearEquiv.ofLinear F.toLinearMap R.toLinearMap
            (LinearMap.ext hright) (LinearMap.ext hleft)
          continuous_toFun := F.continuous
          continuous_invFun := R.continuous }

@[simp] theorem exponentialPeriodizationQuotient_mk (f : ExpSchwartz) :
    exponentialPeriodizationQuotient d ((exponentialPeriodization d).ker.mkQ f) =
      exponentialPeriodization d f := rfl

/-- Differences of exponentially decaying functions with one period translate. -/
def exponentialPeriodizationDifferences : Set ExpSchwartz :=
  {g | ∃ f : ExpSchwartz, ∀ x, expSchwartzEvaluation 0 g x =
    expSchwartzEvaluation 0 f x - expSchwartzEvaluation 0 f (x + d)}

private theorem exponentialPeriodization_difference_vanishes {g : ExpSchwartz}
    (hg : g ∈ exponentialPeriodizationDifferences d) :
    exponentialPeriodization d g = 0 := by
  obtain ⟨f, hf⟩ := hg
  apply Subtype.ext
  funext x
  rw [exponentialPeriodization_apply]
  simp only [hf]
  have hs := schwartzIntegerTranslate_summable d (expSchwartzEvaluation 0 f) x
  let t (m : ℤ) := expSchwartzEvaluation 0 f (x + d * m)
  have he (m : ℤ) : x + d * (m : ℝ) + d = x + d * ((m + 1 : ℤ) : ℝ) := by push_cast; ring
  simp_rw [he]
  change (∑' m : ℤ, (t m - t ((Equiv.addRight (1 : ℤ)) m))) = 0
  calc
    _ = (∑' m : ℤ, t m) - (∑' m : ℤ, t ((Equiv.addRight (1 : ℤ)) m)) :=
      hs.tsum_sub ((Equiv.addRight (1 : ℤ)).summable_iff.mpr hs)
    _ = 0 := sub_eq_zero.mpr ((Equiv.addRight (1 : ℤ)).tsum_eq t).symm

private theorem exponentialPeriodization_compact_in_differences {f : ExpSchwartz}
    (hf : exponentialPeriodization d f = 0)
    (hc : HasCompactSupport (expSchwartzEvaluation 0 f)) :
    f ∈ exponentialPeriodizationDifferences d := by
  let g := expSchwartzEvaluation 0 f
  obtain ⟨a, ha⟩ := hc.isCompact.bddBelow
  obtain ⟨b, hb⟩ := hc.isCompact.bddAbove
  have hsub : support g ⊆ Icc a b := fun x hx =>
    ⟨ha (subset_closure hx), hb (subset_closure hx)⟩
  have hz (x : ℝ) : integerPeriodization d g x = 0 :=
    congrArg (fun v : SmoothPeriodic d => v.val x) hf
  obtain ⟨ψ, hψC, hψsupp, hψ⟩ :=
    compact_periodization_difference hsub (g.smooth ⊤) (Fact.out : 0 < d) hz
  let ψc : HasCompactSupport ψ :=
    HasCompactSupport.intro isCompact_Icc (fun _ hx =>
      notMem_support.mp (fun h => hx (hψsupp h)))
  let u : LogFixedTest (Icc (a + d) b) := ⟨ψc.toSchwartzMap hψC, hψsupp⟩
  let U : ExpSchwartz := (extendFixedExpSchwartz isCompact_Icc u).val
  refine ⟨U, fun x => ?_⟩
  have he : expSchwartzEvaluation 0 U = u.val := expSchwartzEvaluation_extendFixed_zero _ u
  rw [he]
  exact (hψ x).symm

/-- The actual kernel is the closed linear span of period differences. -/
theorem exponentialPeriodization_ker :
    (exponentialPeriodization d).ker =
      (Submodule.span ℂ (exponentialPeriodizationDifferences d)).topologicalClosure := by
  let P := exponentialPeriodization d
  let S := exponentialPeriodizationSection d
  have hS := exponentialPeriodizationSection_right d
  have hW := smoothPeriodic_withDerivativeSeminorms d
  letI : IsTopologicalAddGroup (SmoothPeriodic d) := hW.topologicalAddGroup
  have hchart : IsEmbedding (periodicChart d Fact.out) :=
    ⟨⟨rfl⟩, periodicChart_injective d Fact.out⟩
  letI : T2Space (SmoothPeriodic d) := hchart.t2Space
  apply le_antisymm
  · intro f hf
    change P f = 0 at hf
    let fN (n : ℕ) := truncateExpSchwartz n f
    let g (n : ℕ) := fN n - S (P (fN n))
    have hg0 (n : ℕ) : P (g n) = 0 := by
      change P (fN n - S (P (fN n))) = 0
      rw [map_sub, show P (S (P (fN n))) = P (fN n) from hS _, sub_self]
    have hgc (n : ℕ) : HasCompactSupport (expSchwartzEvaluation 0 (g n)) := by
      change HasCompactSupport (⇑(expSchwartzEvaluation 0 (fN n - S (P (fN n)))))
      rw [map_sub]
      exact (truncateExpSchwartz_hasCompactSupport n f).sub
        (exponentialPeriodizationSection_compact d _)
    have hfN : Tendsto fN atTop (𝓝 f) := truncateExpSchwartz_tendsto f
    have hl : Tendsto (fun n => S (P (fN n))) atTop (𝓝 (0 : ExpSchwartz)) := by
      have h := (S.continuous.continuousAt.tendsto.comp
        (P.continuous.continuousAt.tendsto.comp hfN))
      simpa [hf, Function.comp_def] using h
    have hg : Tendsto g atTop (𝓝 f) := by simpa [g] using hfN.sub hl
    let M := Submodule.span ℂ (exponentialPeriodizationDifferences d)
    have hmem (n : ℕ) : g n ∈ M := Submodule.subset_span
      (exponentialPeriodization_compact_in_differences d (hg0 n) (hgc n))
    exact mem_closure_of_tendsto hg (Eventually.of_forall hmem)
  · apply Submodule.topologicalClosure_minimal
    · exact Submodule.span_le.2 (fun f hf => exponentialPeriodization_difference_vanishes d hf)
    · exact P.isClosed_ker

/-- The annihilator in the strong dual of the original test space, with
its induced topology. -/
def exponentialPeriodizationAnnihilator : Submodule ℂ (StrongDual ℂ ExpSchwartz) where
  carrier := {L | ∀ f, exponentialPeriodization d f = 0 → L f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro L K hL hK f hf
    simp only [mem_setOf_eq] at hL hK
    change L f + K f = 0
    rw [hL f hf, hK f hf, add_zero]
  smul_mem' := by
    intro c L hL f hf
    simp only [mem_setOf_eq] at hL
    change c * L f = 0
    rw [hL f hf, mul_zero]

/-- Pullback along the periodization identifies the strong dual of the
circle with the annihilator equipped with its inherited strong topology. -/
def exponentialPeriodizationDualEquiv :
    StrongDual ℂ (SmoothPeriodic d) ≃L[ℂ] exponentialPeriodizationAnnihilator d := by
  let P := exponentialPeriodization d
  let S := exponentialPeriodizationSection d
  have hS : RightInverse S P := exponentialPeriodizationSection_right d
  let pull : StrongDual ℂ (SmoothPeriodic d) →L[ℂ] StrongDual ℂ ExpSchwartz :=
    ContinuousLinearMap.precomp ℂ P
  let restrict : StrongDual ℂ ExpSchwartz →L[ℂ] StrongDual ℂ (SmoothPeriodic d) :=
    ContinuousLinearMap.precomp ℂ S
  let F := pull.codRestrict (exponentialPeriodizationAnnihilator d) (fun L => by
      intro x hx
      change L (P x) = 0
      rw [show P x = 0 from hx, map_zero])
  let R := restrict.comp (exponentialPeriodizationAnnihilator d).subtypeL
  have hr (L : StrongDual ℂ (SmoothPeriodic d)) : R (F L) = L := by
    apply ContinuousLinearMap.ext
    intro g
    change L (P (S g)) = L g
    rw [hS g]
  have hf (L : exponentialPeriodizationAnnihilator d) : F (R L) = L := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    change L.val (S (P f)) = L.val f
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply L.property
    rw [map_sub, hS (P f), sub_self]
  exact
    { toLinearEquiv := LinearEquiv.ofLinear F.toLinearMap R.toLinearMap (LinearMap.ext hf) (LinearMap.ext hr)
      continuous_toFun := F.continuous
      continuous_invFun := R.continuous }

@[simp] theorem exponentialPeriodizationDualEquiv_apply
    (L : StrongDual ℂ (SmoothPeriodic d)) (f : ExpSchwartz) :
    (exponentialPeriodizationDualEquiv d L).val f = L (exponentialPeriodization d f) := rfl

/-- The two strong topologies on the periodization annihilator agree. -/
def exponentialPeriodizationQuotientDualEquiv :
    StrongDual ℂ (ExpSchwartz ⧸ (exponentialPeriodization d).ker) ≃L[ℂ]
      exponentialPeriodizationAnnihilator d :=
  ((exponentialPeriodizationQuotient d).arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)).trans
    (exponentialPeriodizationDualEquiv d)

@[simp] theorem exponentialPeriodizationQuotientDualEquiv_apply
    (L : StrongDual ℂ (ExpSchwartz ⧸ (exponentialPeriodization d).ker)) (f : ExpSchwartz) :
    (exponentialPeriodizationQuotientDualEquiv d L).val f =
      L ((exponentialPeriodization d).ker.mkQ f) := by
  change L ((exponentialPeriodizationQuotient d).symm (exponentialPeriodization d f)) = _
  rw [← exponentialPeriodizationQuotient_mk d f, ContinuousLinearEquiv.symm_apply_apply]

/-- In logarithmic coordinates the purely imaginary Mellin profile is the
ordinary Fourier profile at the opposite frequency. -/
theorem mellin_logProfile_ofReal_mul_I (f : ℝ → ℂ) (y : ℝ) :
    mellin (f ∘ Real.log) ((2 * Real.pi * y : ℝ) * Complex.I) = (𝓕 f) (-y) := by
  rw [mellin_eq_fourier]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, zero_mul, Real.exp_zero,
    one_smul, Function.comp_apply, Real.log_exp, Complex.mul_I_im, Complex.ofReal_re]
  rw [mul_div_cancel_left₀ _ hpi]
  simp only [Real.fourier_real_eq_integral_exp_smul]
  let u (x : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * (x * (-y))) * Complex.I) • f x
  have hu := Measure.integral_comp_mul_left u (-1)
  simp only [neg_mul, one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at hu
  calc
    _ = (∫ x : ℝ, u (-x)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [u]
      congr 2
      push_cast
      ring
    _ = _ := by simpa only [u, ← mul_assoc] using hu

/-- Periodization pulls back the normalized coefficient to the Mellin
evaluation at the negative Fourier frequency, divided by the period. -/
theorem exponentialPeriodization_coefficient_mellin (f : ExpSchwartz) (m : ℤ) :
    periodicFourierCoefficient d (exponentialPeriodization d f) m =
      d⁻¹ • mellin (fun t => expSchwartzEvaluation 0 f (Real.log t)) (-periodicFrequency d m) := by
  rw [show exponentialPeriodization d f = schwartzPeriodizationCLM d (expSchwartzEvaluation 0 f) from rfl,
    schwartzPeriodization_coefficient]
  have hd : d ≠ 0 := (Fact.out : 0 < d).ne'
  have he : -periodicFrequency d m = ((2 * Real.pi * (-(m : ℝ) / d) : ℝ) : ℂ) * Complex.I := by
    unfold periodicFrequency
    push_cast
    ring
  rw [he]
  change _ = d⁻¹ • mellin ((fun x => expSchwartzEvaluation 0 f x) ∘ Real.log) _
  rw [mellin_logProfile_ofReal_mul_I, neg_div, neg_neg, SchwartzMap.fourier_coe]

end
end Masullo
