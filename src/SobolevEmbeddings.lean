/-
Adapted from the Apache-2.0 RiemannMasullo project at
db376192baf52253727c46e2b211619d4e6a3941, Ch09_HardySobolev/Sec1.lean
and ForMathlib/MeasureTheory/Function/ContinuousMapDense.lean.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import LCAFourierInversion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.ContinuousMap.CompactlySupported

open Filter Function MeasureTheory Set Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal ZeroAtInfty
open InnerProductSpace

namespace Masullo

noncomputable section

section Weighted

variable {A : Type*}

/-- Paper: Definition 9.1.1.1, p. 396. On the group where the weight is evaluated,
a Sobolev weight is nonnegative, continuous, and subadditive up to one positive constant.
Deviation: The argument group is explicit. For the paper's weight on G it is the dual of G. -/
def IsSobolevWeight [Mul A] [TopologicalSpace A] (w : A → ℝ≥0) : Prop :=
  Continuous w ∧ ∃ C : ℝ≥0, 0 < C ∧ ∀ x y, w (x * y) ≤ C * (w x + w y)

/-- Paper: Definition 9.1.1.1, p. 396. Every constant nonnegative weight is a Sobolev weight.
Deviation: Sanity check on the weight condition. -/
theorem isSobolevWeight_const [Mul A] [TopologicalSpace A] (c : ℝ≥0) :
    IsSobolevWeight (fun _ : A ↦ c) :=
  ⟨continuous_const, 1, one_pos, fun _ _ ↦ by rw [one_mul]; exact le_self_add⟩

/-- Paper: Definition 9.1.1.1, p. 396. The measure for degree s has density
`(1 + w²)^(s/2)` with respect to the measure on the group carrying the weight. -/
def sobolevMeasure [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) (s : ℝ) : Measure A :=
  ν.withDensity fun x ↦ ENNReal.ofReal ((1 + (w x : ℝ) ^ 2) ^ (s / 2))

/-- Paper: Definition 9.1.1.1, p. 396. At degree zero, the weighted measure is the original
measure.
Deviation: Sanity check on the normalization in (9.1.1.3). -/
theorem sobolevMeasure_zero [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) :
    sobolevMeasure ν w 0 = ν := by
  simp [sobolevMeasure]


/-- Paper: Definition 9.1.1.1, p. 396. The Sobolev space consists of square-integrable
classes for the weighted measure. Use the dual group and the Plancherel measure for H^s_w(G).
Deviation: The completed space is realized directly as the weighted L² from Lemma 9.1.1.2.
An element in this model already represents the Fourier-side function. -/
abbrev WeightedSobolev [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) (s : ℝ) :=
  Lp ℂ 2 (sobolevMeasure ν w s)

/-- Paper: Definition 9.1.1.1, p. 396. In the weighted L² model the norm is the square root
of the integral of the squared modulus times the prescribed density.
Deviation: Sanity check on (9.1.1.3), written directly for Fourier-side representatives. -/
theorem weightedSobolev_norm [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A]
    (ν : Measure A) {w : A → ℝ≥0} (hw : Continuous w) (s : ℝ)
    (f : WeightedSobolev ν w s) :
    Integrable (fun x ↦ ‖f x‖ ^ 2 * (1 + (w x : ℝ) ^ 2) ^ (s / 2)) ν ∧
    ‖f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 * (1 + (w x : ℝ) ^ 2) ^ (s / 2) ∂ν) := by
  let μ : Measure A := sobolevMeasure ν w s
  let ρ : A → ℝ := fun x ↦ (1 + (w x : ℝ) ^ 2) ^ (s / 2)
  have hρ_cont : Continuous ρ := by
    refine Continuous.rpow_const (continuous_const.add
      ((NNReal.continuous_coe.comp hw).pow 2)) ?_
    intro x
    refine Or.inl (ne_of_gt ?_)
    exact lt_of_lt_of_le one_pos (le_add_of_nonneg_right (sq_nonneg _))
  have hρ_nonneg (x : A) : 0 ≤ ρ x := by
    dsimp only [ρ]
    exact Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg _)) _
  have hdens : Measurable (fun x ↦ ENNReal.ofReal (ρ x)) :=
    (ENNReal.continuous_ofReal.comp hρ_cont).measurable
  have hμ : μ = ν.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) := rfl
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (ρ x) < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hint_sq : Integrable (fun x ↦ ‖(f : A → ℂ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hint : Integrable (fun x ↦ ‖f x‖ ^ 2 * ρ x) ν := by
    rw [hμ] at hint_sq
    refine ((integrable_withDensity_iff hdens hflt).1 hint_sq).congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hρ_nonneg x)]
  refine ⟨hint, ?_⟩
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := f)]
  refine congrArg Real.sqrt ?_
  rw [L2.inner_def (f := f) (g := f), ← integral_re (L2.integrable_inner f f)]
  simp_rw [inner_self_eq_norm_sq]
  calc
    ∫ x, ‖(f : A → ℂ) x‖ ^ 2 ∂sobolevMeasure ν w s
        = ∫ x, ‖(f : A → ℂ) x‖ ^ 2 ∂ν.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) := rfl
    _ = ∫ x, (ENNReal.ofReal (ρ x)).toReal • ‖(f : A → ℂ) x‖ ^ 2 ∂ν :=
      integral_withDensity_eq_integral_toReal_smul hdens hflt _
    _ = ∫ x, ‖f x‖ ^ 2 * (1 + (w x : ℝ) ^ 2) ^ (s / 2) ∂ν := by
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      dsimp
      rw [ENNReal.toReal_ofReal (hρ_nonneg x), mul_comm]

end Weighted

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (ν : Measure (PontryaginDual G)) {w : PontryaginDual G → ℝ≥0} {s : ℝ}

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Definition 9.1.1.1, p. 396. Continuous compactly supported functions embed as a
dense complex-linear subspace of the Fourier-side Sobolev space.
Deviation: The norm in (9.1.1.3) is applied to the test functions as Fourier-side data. -/
theorem weightedSobolev_compactSupport_dense [ν.IsHaarMeasure] [ν.Regular]
    (hw : Continuous w) :
    ∃ J : (C_c(PontryaginDual G, ℂ)) →ₗ[ℂ] WeightedSobolev ν w s,
      DenseRange J ∧ Function.Injective J ∧
        ∀ f, (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by
  let ρ (χ : PontryaginDual G) : ℝ := (1 + (w χ : ℝ) ^ 2) ^ (s / 2)
  have hρpos (χ : PontryaginDual G) : 0 < ρ χ := Real.rpow_pos_of_pos (by positivity) _
  have hbase : Continuous (fun χ ↦ 1 + (w χ : ℝ) ^ 2) :=
    continuous_const.add ((NNReal.continuous_coe.comp hw).pow 2)
  have hρ : Continuous ρ := hbase.rpow_const fun χ ↦ Or.inl (by positivity)
  let νw := sobolevMeasure ν w s
  let : IsLocallyFiniteMeasure νw := IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have hννw : ν ≪ νw :=
    withDensity_absolutelyContinuous' hρ.measurable.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun χ ↦ (ENNReal.ofReal_pos.mpr (hρpos χ)).ne')
  have mem (f : C_c(PontryaginDual G, ℂ)) : MemLp (f : PontryaginDual G → ℂ) 2 νw :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  let J : (C_c(PontryaginDual G, ℂ)) →ₗ[ℂ] WeightedSobolev ν w s :=
    { toFun := fun f ↦ (mem f).toLp f
      map_add' := fun f g ↦ MemLp.toLp_add (mem f) (mem g)
      map_smul' := fun c f ↦ MemLp.toLp_const_smul c (mem f) }
  have hJ (f : C_c(PontryaginDual G, ℂ)) :
      (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) :=
    hννw.ae_eq (mem f).coeFn_toLp
  have hJinj : Function.Injective J := by
    intro f g hfg
    apply DFunLike.coe_injective
    exact Measure.eq_of_ae_eq ((hJ f).symm.trans (hfg ▸ hJ g)) f.continuous g.continuous
  refine ⟨J, ?_, hJinj, hJ⟩
  -- Multiplying by the square root of the density transfers the weighted L² seminorm.
  let m (χ : PontryaginDual G) : ℂ := Real.sqrt (ρ χ)
  have hm : Continuous m := Complex.continuous_ofReal.comp hρ.sqrt
  have hmne (χ : PontryaginDual G) : m χ ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hρpos χ)).ne'
  have hnorm (u : PontryaginDual G → ℂ) (hu : AEStronglyMeasurable u νw) :
      eLpNorm u 2 νw = eLpNorm (fun χ ↦ m χ * u χ) 2 ν := by
    have huν := hu.mono_ac hννw
    change eLpNorm u 2 νw = eLpNorm (m * u) 2 ν
    rw [eLpNorm_eq_eLpNorm' (p := 2) (by simp) ENNReal.ofNat_ne_top,
      eLpNorm_eq_eLpNorm' (p := 2) (by simp) ENNReal.ofNat_ne_top]
    simp only [eLpNorm', ENNReal.toReal_ofNat, ENNReal.rpow_two]
    congr 1
    change (∫⁻ χ, ‖u χ‖ₑ ^ 2 ∂ν.withDensity (fun χ ↦ ENNReal.ofReal (ρ χ))) = _
    rw [lintegral_withDensity_eq_lintegral_mul₀ hρ.measurable.aemeasurable.ennreal_ofReal
      (huν.enorm.pow_const 2)]
    apply lintegral_congr
    intro χ
    have hmSq : ‖m χ‖ₑ ^ 2 = ENNReal.ofReal (ρ χ) := by
      rw [← ofReal_norm, show ‖m χ‖ = Real.sqrt (ρ χ) by simp [m],
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hρpos χ).le]
    simp only [Pi.mul_apply, enorm_mul, mul_pow, hmSq]
  intro f
  refine EMetric.mem_closure_iff.mpr fun ε hε ↦ ?_
  have hf := Lp.memLp f
  have hmf : MemLp (fun χ ↦ m χ * f χ) 2 ν := by
    refine ⟨hm.aestronglyMeasurable.mul (hf.aestronglyMeasurable.mono_ac hννw), ?_⟩
    rw [← hnorm _ hf.aestronglyMeasurable]
    exact hf.eLpNorm_lt_top
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨g, hgDist, hgCont, hgSupp⟩ :=
    exists_compactTest_eLpNorm_sub_le ENNReal.ofNat_ne_top hmf hδ.ne'
  let a : C_c(PontryaginDual G, ℂ) :=
    ⟨⟨fun χ ↦ (m χ)⁻¹ * g χ, (hm.inv₀ hmne).mul hgCont⟩, hgSupp.mul_left⟩
  refine ⟨J a, ⟨a, rfl⟩, ?_⟩
  have hfa : ((f : PontryaginDual G → ℂ) - (J a : PontryaginDual G → ℂ)) =ᵐ[νw]
      (f : PontryaginDual G → ℂ) - (a : PontryaginDual G → ℂ) :=
    Filter.EventuallyEq.rfl.sub (mem a).coeFn_toLp
  change edist f (J a) < ε
  rw [Lp.edist_def, eLpNorm_congr_ae hfa,
    hnorm _ (hf.aestronglyMeasurable.sub (mem a).aestronglyMeasurable)]
  have hdiff : (fun χ ↦ m χ * (f χ - a χ)) = (fun χ ↦ m χ * f χ) - g := by
    funext χ
    simp [a, mul_sub, hmne χ]
  change eLpNorm (fun χ ↦ m χ * (f χ - a χ)) 2 ν < ε
  rw [hdiff]
  exact hgDist.trans_lt hδε

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [BorelSpace G]
  [BorelSpace (PontryaginDual G)] [μ.IsHaarMeasure] [μ.Regular] in
/-- Paper: Proposition 9.1.1.3(1), p. 396. In nonnegative degree the Sobolev space
includes continuously and contractively into Haar L² via inverse Plancherel. -/
theorem weightedSobolev_toL2 (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (_hs : 0 ≤ s) :
    ∃ J : WeightedSobolev ν w s →L[ℂ] Lp ℂ 2 μ,
      Function.Injective J ∧ ‖J‖ ≤ 1 ∧
        ∀ f, (U (J f) : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by
  let νw := sobolevMeasure ν w s
  have hle : ν ≤ νw := calc
    ν = ν.withDensity 1 := withDensity_one.symm
    _ ≤ νw := by
      apply withDensity_mono
      refine ae_of_all _ fun χ ↦ ?_
      simpa only [Pi.one_apply, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg (w χ : ℝ)))
          (div_nonneg _hs (by norm_num)))
  have hνw : νw ≪ ν := withDensity_absolutelyContinuous _ _
  have mem (f : WeightedSobolev ν w s) : MemLp (f : PontryaginDual G → ℂ) 2 ν :=
    (Lp.memLp f).mono_measure hle
  let I : WeightedSobolev ν w s →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f ↦ (mem f).toLp f
      map_add' f g :=
        (MemLp.toLp_congr (mem (f + g)) ((mem f).add (mem g))
          (ae_mono hle (Lp.coeFn_add f g))).trans (MemLp.toLp_add (mem f) (mem g))
      map_smul' c f :=
        (MemLp.toLp_congr (mem (c • f)) ((mem f).const_smul c)
          (ae_mono hle (Lp.coeFn_smul c f))).trans (MemLp.toLp_const_smul c (mem f)) }
  let K := U.symm.toLinearEquiv.toLinearMap.comp I
  have hK (f : WeightedSobolev ν w s) : ‖K f‖ ≤ 1 * ‖f‖ := by
    change ‖U.symm (I f)‖ ≤ _
    rw [U.symm.norm_map, one_mul]
    change ‖(mem f).toLp f‖ ≤ ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_lt_top.ne (eLpNorm_mono_measure _ hle)
  let J := K.mkContinuous 1 hK
  have hJ (f : WeightedSobolev ν w s) :
      (U (J f) : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by
    change (U (U.symm (I f)) : PontryaginDual G → ℂ) =ᵐ[ν] _
    rw [U.apply_symm_apply]
    exact (mem f).coeFn_toLp
  refine ⟨J, ?_, K.mkContinuous_norm_le zero_le_one hK, hJ⟩
  intro f g hfg
  exact Lp.ext (hνw.ae_eq ((hJ f).symm.trans (hfg ▸ hJ g)))

-- higher-degree weighted integral.

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [BorelSpace (PontryaginDual G)] in
/-- Paper: Proposition 9.1.1.3(2), p. 397. For s' > s ≥ 0, the inclusion from
degree s' to degree s is contractive and preserves the Fourier-side representative.
Deviation: The variable in (9.1.1.6) ranges over the source of the displayed inclusion. -/
theorem weightedSobolev_ofHigherDegree (_hs : 0 ≤ s) {s' : ℝ} (_hss' : s < s') :
    ∃ J : WeightedSobolev ν w s' →L[ℂ] WeightedSobolev ν w s,
      Function.Injective J ∧ ‖J‖ ≤ 1 ∧
        ∀ f, (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by
  have hmono {a b : ℝ} (hab : a ≤ b) : sobolevMeasure ν w a ≤ sobolevMeasure ν w b := by
    apply withDensity_mono
    refine ae_of_all _ fun χ ↦ ENNReal.ofReal_le_ofReal ?_
    exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _))
      (div_le_div_of_nonneg_right hab (by norm_num))
  have hle := hmono _hss'.le
  have hνle : ν ≤ sobolevMeasure ν w s := calc
    ν = sobolevMeasure ν w 0 := (sobolevMeasure_zero ν w).symm
    _ ≤ sobolevMeasure ν w s := hmono _hs
  have h_ac : sobolevMeasure ν w s' ≪ ν := withDensity_absolutelyContinuous _ _
  have hle' : sobolevMeasure ν w s ≤ (1 : ℝ≥0∞) • sobolevMeasure ν w s' := by
    simpa only [one_smul] using hle
  have hone : (1 : ℝ≥0∞) ≠ ∞ := ENNReal.one_ne_top
  let I : WeightedSobolev ν w s' →L[ℝ] WeightedSobolev ν w s :=
    Lp.LpToLpOfMeasureLeSMul hone hle'
  have hI (f : WeightedSobolev ν w s') :
      (I f : PontryaginDual G → ℂ) =ᵐ[sobolevMeasure ν w s] (f : PontryaginDual G → ℂ) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul hone hle' f
  let J : WeightedSobolev ν w s' →L[ℂ] WeightedSobolev ν w s :=
    { toFun := I
      map_add' := I.map_add
      map_smul' := fun c f ↦ Lp.ext <|
        (hI (c • f)).trans <| Filter.EventuallyEq.trans (ae_mono hle (Lp.coeFn_smul c f)) <|
          ((hI f).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (I f)).symm
      cont := I.continuous }
  have hJ (f : WeightedSobolev ν w s') :
      (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) :=
    ae_mono hνle (hI f)
  refine ⟨J, ?_, ?_, hJ⟩
  · intro f g hfg
    exact Lp.ext (h_ac.ae_eq ((hJ f).symm.trans (hfg ▸ hJ g)))
  · rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ) J]
    change ‖I‖ ≤ 1
    simpa [I] using Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) hone hle'

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 9.1.1.3(3), p. 397. Cauchy–Schwarz with the density and its
reciprocal controls the unweighted integral of the norm of a Fourier-side Sobolev element. -/
private theorem weightedSobolev_integrable
    (hw : IsSobolevWeight w)
    (h : Integrable (fun χ ↦ (1 + (w χ : ℝ) ^ 2) ^ (-s / 2)) ν)
    (f : WeightedSobolev ν w s) :
    Integrable (f : PontryaginDual G → ℂ) ν ∧
      (∫ χ, ‖f χ‖ ∂ν) ≤ ‖f‖ * Real.sqrt (∫ χ, (1 + (w χ : ℝ) ^ 2) ^ (-s / 2) ∂ν) := by
  let ρ (χ : PontryaginDual G) : ℝ := (1 + (w χ : ℝ) ^ 2) ^ (s / 2)
  have hρ (χ : PontryaginDual G) : 0 < ρ χ := Real.rpow_pos_of_pos (by positivity) _
  have hrecip (χ : PontryaginDual G) : (1 + (w χ : ℝ) ^ 2) ^ (-s / 2) = (ρ χ)⁻¹ := by
    rw [neg_div, Real.rpow_neg (by positivity)]
  have hρc : Continuous ρ := by
    have hbase : Continuous (fun χ ↦ 1 + (w χ : ℝ) ^ 2) :=
      continuous_const.add ((NNReal.continuous_coe.comp hw.1).pow 2)
    exact hbase.rpow_const fun χ ↦ Or.inl (by positivity)
  have hAC : ν ≪ sobolevMeasure ν w s :=
    withDensity_absolutelyContinuous' hρc.measurable.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun χ ↦ (ENNReal.ofReal_pos.mpr (hρ χ)).ne')
  have hf := weightedSobolev_norm ν hw.1 s f
  let a (χ : PontryaginDual G) := ‖f χ‖ * Real.sqrt (ρ χ)
  let b (χ : PontryaginDual G) := Real.sqrt (ρ χ)⁻¹
  have ha (χ : PontryaginDual G) : 0 ≤ a χ := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hb (χ : PontryaginDual G) : 0 ≤ b χ := Real.sqrt_nonneg _
  have ha_sq (χ : PontryaginDual G) : a χ ^ 2 = ‖f χ‖ ^ 2 * ρ χ := by
    change (‖f χ‖ * Real.sqrt (ρ χ)) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (hρ χ).le]
  have hb_sq (χ : PontryaginDual G) : b χ ^ 2 = (1 + (w χ : ℝ) ^ 2) ^ (-s / 2) := by
    change (Real.sqrt (ρ χ)⁻¹) ^ 2 = _
    rw [Real.sq_sqrt (inv_nonneg.mpr (hρ χ).le), hrecip]
  have haLp : MemLp a 2 ν := by
    have haM : AEStronglyMeasurable a ν :=
      ((Lp.aestronglyMeasurable f).mono_ac hAC).norm.mul hρc.sqrt.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm haM).2
    simpa only [Real.norm_of_nonneg (ha _), ha_sq] using hf.1
  have hbLp : MemLp b 2 ν := by
    have hbM : AEStronglyMeasurable b ν :=
      (hρc.inv₀ fun χ ↦ (hρ χ).ne').sqrt.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm hbM).2
    simpa only [Real.norm_of_nonneg (hb _), hb_sq] using h
  have hab (χ : PontryaginDual G) : a χ * b χ = ‖f χ‖ := by
    dsimp only [a, b]
    rw [mul_assoc, ← Real.sqrt_mul (hρ χ).le,
      mul_inv_cancel₀ (hρ χ).ne', Real.sqrt_one, mul_one]
  have hint : Integrable (fun χ ↦ ‖f χ‖) ν := by
    have hm : MemLp (a * b) 1 ν := MemLp.mul' (p := 2) (q := 2) (r := 1) hbLp haLp
    simpa only [Pi.mul_def, hab] using memLp_one_iff_integrable.mp hm
  refine ⟨⟨(Lp.aestronglyMeasurable f).mono_ac hAC,
    (hasFiniteIntegral_norm_iff _).mp hint.hasFiniteIntegral⟩, ?_⟩
  have hbound := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp a (ENNReal.ofReal 2) ν by simpa using haLp)
    (show MemLp b (ENNReal.ofReal 2) ν by simpa using hbLp)
  rw [hf.2]
  simpa only [Real.norm_of_nonneg (ha _), Real.norm_of_nonneg (hb _), hab, Real.rpow_two,
    ha_sq, hb_sq, ← Real.sqrt_eq_rpow] using hbound

/-- Paper: Proposition 9.1.1.3(3), p. 397. When the reciprocal density is integrable,
the inverse Plancherel class of each Sobolev element has a unique representative
vanishing at infinity. The representative map is a bounded linear injection. -/
theorem weightedSobolev_toZeroAtInfty [ν.IsHaarMeasure] [ν.Regular]
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν) (hU : IsFourierPlancherel μ ν U)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s)
    (_h : Integrable (fun χ ↦ (1 + (w χ : ℝ) ^ 2) ^ (-s / 2)) ν) :
    ∃ (J : WeightedSobolev ν w s →L[ℂ] Lp ℂ 2 μ)
      (E : WeightedSobolev ν w s →L[ℂ] C₀(G, ℂ)) (C : ℝ),
      (∀ f, (U (J f) : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ)) ∧
      Function.Injective E ∧ 0 < C ∧ ‖E‖ ≤ C ∧
      ∀ f g, g = E f ↔ (g : G → ℂ) =ᵐ[μ] (J f : G → ℂ) := by
  obtain ⟨J, hJinj, -, hJ⟩ := weightedSobolev_toL2 μ ν U _hs
  have hL1 (f : WeightedSobolev ν w s) := weightedSobolev_integrable ν _hw _h f
  choose F hF hFormula using fun f ↦
    lcaInverseFourier_zeroAtInfty μ ν U hU (J f) f (hL1 f).1 (hJ f)
  have unique (f : WeightedSobolev ν w s) (g : C₀(G, ℂ))
      (hg : (g : G → ℂ) =ᵐ[μ] (J f : G → ℂ)) : g = F f :=
    DFunLike.coe_injective (Measure.eq_of_ae_eq (hg.trans (hF f).symm)
      g.continuous (F f).continuous)
  let L : WeightedSobolev ν w s →ₗ[ℂ] C₀(G, ℂ) :=
    { toFun := F
      map_add' := fun f g ↦ (unique (f + g) (F f + F g) (by
        rw [J.map_add]
        exact ((hF f).add (hF g)).trans (Lp.coeFn_add (J f) (J g)).symm)).symm
      map_smul' := fun c f ↦ (unique (c • f) (c • F f) (by
        rw [J.map_smul]
        exact ((hF f).fun_comp (c • ·)).trans (Lp.coeFn_smul c (J f)).symm)).symm }
  let C := Real.sqrt (∫ χ, (1 + (w χ : ℝ) ^ 2) ^ (-s / 2) ∂ν) + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) one_pos
  have hBound (f : WeightedSobolev ν w s) : ‖L f‖ ≤ C * ‖f‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (mul_nonneg hC.le (norm_nonneg _))).mpr
    intro x
    change ‖F f x‖ ≤ C * ‖f‖
    rw [hFormula]
    calc
      _ ≤ ∫ χ, ‖f χ‖ ∂ν := by
        simpa only [norm_mul, Circle.norm_coe, mul_one] using
          norm_integral_le_integral_norm (μ := ν) (fun χ ↦ f χ * (χ x : ℂ))
      _ ≤ C * ‖f‖ := ((hL1 f).2).trans (by
        rw [mul_comm C]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))
  let E := L.mkContinuous C hBound
  refine ⟨J, E, C, hJ, ?_, hC, L.mkContinuous_norm_le hC.le hBound, ?_⟩
  · intro f g hfg
    change F f = F g at hfg
    apply hJinj
    exact Lp.ext ((hF f).symm.trans (hfg ▸ hF g))
  · intro f g
    change g = F f ↔ _
    exact ⟨fun h ↦ h ▸ hF f, unique f g⟩


end
end Masullo
