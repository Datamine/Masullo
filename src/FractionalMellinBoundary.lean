import FractionalMellinTrace

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct InnerProductSpace

namespace Masullo

noncomputable section

variable {K : Type*} [MeasurableSpace K] (μ : Measure K) [SFinite μ]

local notation "dx" => (volume : Measure ℝ)
local notation "P[" a "," b "," s "]" => Lp ℂ 2 (μ.prod (stripMeasure a b s))

omit [SFinite μ] in
private theorem prod_strip_eq_amplitude (b s : ℝ) :
    μ.prod (stripMeasure b b s) =
      amplitudeMeasure (μ.prod dx) (fun p : K × ℝ => stripSobolevAmplitude b b s p.2) := by
  unfold stripMeasure amplitudeMeasure
  exact prod_withDensity_right
    ((stripSobolevAmplitude_continuous b b s).measurable.pow_const 2).ennreal_ofReal

private def stripProductAmplitudeIso (b s : ℝ) : P[b,b,s] ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod dx) := by
  let r := fun p : K × ℝ => stripSobolevAmplitude b b s p.2
  have hr : Measurable r := (stripSobolevAmplitude_continuous b b s).measurable.comp measurable_snd
  have hp (p : K × ℝ) : 0 < r p := stripSobolevAmplitude_pos b b s p.2
  let A := amplitudeL2Iso (μ.prod dx) r hr hp
  have he : amplitudeMeasure (μ.prod dx) r = μ.prod (stripMeasure b b s) :=
    (prod_strip_eq_amplitude μ b s).symm
  let C : P[b,b,s] ≃ₗᵢ[ℂ] Lp ℂ 2 (amplitudeMeasure (μ.prod dx) r) :=
    he ▸ LinearIsometryEquiv.refl ℂ _
  exact C.trans A

omit [SFinite μ] in
private theorem stripProductAmplitudeIso_ae (b s : ℝ) (f : P[b,b,s]) :
    (stripProductAmplitudeIso μ b s f : K × ℝ → ℂ) =ᵐ[μ.prod dx]
      fun p => stripSobolevAmplitude b b s p.2 • f p := by
  let r := fun p : K × ℝ => stripSobolevAmplitude b b s p.2
  let B := amplitudeMeasure (μ.prod dx) r
  let W := μ.prod (stripMeasure b b s)
  have he : B = W := (prod_strip_eq_amplitude μ b s).symm
  have hr : Measurable r := (stripSobolevAmplitude_continuous b b s).measurable.comp measurable_snd
  have hp (p : K × ℝ) : 0 < r p := stripSobolevAmplitude_pos b b s p.2
  let C : Lp ℂ 2 W ≃ₗᵢ[ℂ] Lp ℂ 2 B := he ▸ LinearIsometryEquiv.refl ℂ _
  have hC : ∀ᵐ p ∂μ.prod dx, C f p = f p := by
    have hcast (W' : Measure (K × ℝ)) (eq : B = W') (v : Lp ℂ 2 W') :
        let D : Lp ℂ 2 W' ≃ₗᵢ[ℂ] Lp ℂ 2 B := eq ▸ LinearIsometryEquiv.refl ℂ _
        ∀ p : K × ℝ, D v p = v p := by
      subst W'
      dsimp only
      intro _
      rfl
    exact .of_forall (hcast W he f)
  change (amplitudeL2Iso (μ.prod dx) r hr hp (C f) : K × ℝ → ℂ) =ᵐ[μ.prod dx] _
  exact (amplitudeL2Iso_ae (μ.prod dx) r hr hp (C f)).trans
    (hC.mono fun p h => congrArg (r p • ·) h)

private def stripProductTwist (b s : ℝ) : P[b,b,s] ≃ₗᵢ[ℂ] P[0,0,s] :=
  (stripProductAmplitudeIso μ b s).trans (stripProductAmplitudeIso μ 0 s).symm

omit [SFinite μ] in
private theorem stripProductTwist_ae (b s : ℝ) (f : P[b,b,s]) :
    (stripProductTwist μ b s f : K × ℝ → ℂ) =ᵐ[μ.prod dx]
      fun p => Real.exp (b * p.2) • f p := by
  let g := stripProductTwist μ b s f
  have he : stripProductAmplitudeIso μ 0 s g = stripProductAmplitudeIso μ b s f :=
    (stripProductAmplitudeIso μ 0 s).apply_symm_apply _
  have h₁ := stripProductAmplitudeIso_ae μ 0 s g
  rw [he] at h₁
  filter_upwards [h₁, stripProductAmplitudeIso_ae μ b s f] with p hp hq
  change _ = stripSobolevAmplitude 0 0 s p.2 • g p at hp
  have hr : stripSobolevAmplitude b b s p.2 =
      stripSobolevAmplitude 0 0 s p.2 * Real.exp (b * p.2) := by
    simp [stripSobolevAmplitude, mul_comm]
  have h := hp.symm.trans hq
  rw [hr, ← smul_smul] at h
  exact (smul_right_injective _ (stripSobolevAmplitude_pos 0 0 s p.2).ne') h

omit [SFinite μ] in
private theorem base_to_stripProduct (a b s : ℝ) : μ.prod dx ≪ μ.prod (stripMeasure a b s) :=
  Measure.AbsolutelyContinuous.rfl.prod (absolutelyContinuous_amplitudeMeasure dx _
    (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s))

omit [SFinite μ] in
private theorem stripProduct_to_base (a b s : ℝ) : μ.prod (stripMeasure a b s) ≪ μ.prod dx :=
  Measure.AbsolutelyContinuous.rfl.prod (amplitudeMeasure_absolutelyContinuous dx _)

private theorem stripProductTwist_product (b s : ℝ)
    (u : Lp ℂ 2 μ) (v : StripSobolev b b s) :
    stripProductTwist μ b s (lpTwoProduct u v) = lpTwoProduct u (fractionalMellinLine b s v) := by
  apply Lp.ext
  apply (stripProduct_to_base μ 0 0 s).ae_le
  have hs := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := dx)).ae
    (fractionalMellinLine_ae b s v)
  filter_upwards [stripProductTwist_ae μ b s (lpTwoProduct u v),
    (base_to_stripProduct μ b b s).ae_le (lpTwoProduct_ae u v),
    (base_to_stripProduct μ 0 0 s).ae_le (lpTwoProduct_ae u (fractionalMellinLine b s v)),
    hs] with p h₁ h₂ h₃ h₄
  change fractionalMellinLine b s v p.2 = Real.exp (b * p.2) • v p.2 at h₄
  rw [h₁, h₂, h₃, h₄, Complex.real_smul, Complex.real_smul, mul_left_comm]

/-- The inverse Fourier coordinate of the tensor trace is the actual
exponentially twisted product profile. -/
theorem fractionalMellinTensor_coordinates_ae (b s : ℝ) (f : P[b,b,s]) :
    (completedLpTwoTensorEquiv (fractionalMellinTensor μ b s f) : K × ℝ → ℂ)
      =ᵐ[μ.prod dx] fun p => Real.exp (b * p.2) • f p := by
  suffices he : completedLpTwoTensorEquiv (fractionalMellinTensor μ b s f) =
      stripProductTwist μ b s f by
    rw [he]
    exact stripProductTwist_ae μ b s f
  let E := Lp ℂ 2 μ ⊗[ℂ] StripSobolev b b s
  let T : Completion E ≃ₗᵢ[ℂ] P[b,b,s] := completedLpTwoTensorEquiv
  let U : FractionalMellinTensor μ s ≃ₗᵢ[ℂ] P[0,0,s] := completedLpTwoTensorEquiv
  let A := TensorProduct.congrIsometry (.refl ℂ (Lp ℂ 2 μ)) (fractionalMellinLine b s)
  let R := stripProductTwist μ b s
  obtain ⟨v, rfl⟩ := T.surjective f
  change U (completionCongrIsometry A (T.symm (T v))) = R (T v)
  rw [LinearIsometryEquiv.symm_apply_apply]
  refine Completion.denseRange_coe.induction_on v
    (isClosed_eq (U.continuous.comp (completionCongrIsometry A).continuous)
      (R.continuous.comp T.continuous)) ?_
  intro x
  let J := U.toLinearMap.comp (Completion.toComplₗᵢ.toLinearMap.comp A.toLinearMap)
  let L := R.toLinearMap.comp (T.toLinearMap.comp Completion.toComplₗᵢ.toLinearMap)
  rw [completionCongrIsometry_coe]
  change J x = L x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | tmul u v =>
    have hU : U (A (u ⊗ₜ[ℂ] v) : FractionalMellinTensor μ s) =
        lpTwoProduct u (fractionalMellinLine b s v) :=
      completedLpTwoTensorEquiv_tmul u (fractionalMellinLine b s v)
    have hT : T ((u ⊗ₜ[ℂ] v : E) : Completion E) = lpTwoProduct u v :=
      completedLpTwoTensorEquiv_tmul u v
    exact hU.trans ((stripProductTwist_product μ b s u v).symm.trans (congrArg R hT.symm))


theorem fractionalIntervalTrace_coordinates_ae {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) (f : P[a,b,s]) :
    (completedLpTwoTensorEquiv (fractionalIntervalTrace μ hab s ht f) : K × ℝ → ℂ)
      =ᵐ[μ.prod dx] fun p => Real.exp (t * p.2) • f p := by
  have hle : μ.prod (stripMeasure t t s) ≤ μ.prod (stripMeasure a b s) := by
    rw [modulatedInterval_prod_weightedMeasure μ (a := t) le_rfl,
      modulatedInterval_prod_weightedMeasure μ hab]
    apply withDensity_mono
    exact .of_forall fun p => ENNReal.ofReal_le_ofReal
      (hardySobolevWeight_mono_interval ht.1 ht.2 ht.1 ht.2 s p.2)
  let u := lpTwoMeasureInclusion hle f
  have hu : (u : K × ℝ → ℂ) =ᵐ[μ.prod dx] f :=
    (base_to_stripProduct μ t t s).ae_le (lpTwoMeasureInclusion_ae hle f)
  exact (fractionalMellinTensor_coordinates_ae μ t s u).trans
    (hu.mono fun p hp => congrArg (Real.exp (t * p.2) • ·) hp)

private def traceMidpoint {a b : ℝ} (t u : Icc a b) : Icc a b :=
  ⟨((t : ℝ) + (u : ℝ)) / 2, by constructor <;> linarith [t.property.1, t.property.2,
    u.property.1, u.property.2]⟩

/-- The mixed trace inner product at two abscissae is the energy at their
midpoint. The formula is an identity in the completed trace Hilbert space. -/
theorem fractionalIntervalTrace_inner_midpoint {a b : ℝ} (hab : a ≤ b) (s : ℝ)
    (t u : Icc a b) (f : P[a,b,s]) :
    ⟪completedLpTwoTensorEquiv (fractionalIntervalTrace μ hab s t.property f),
      completedLpTwoTensorEquiv (fractionalIntervalTrace μ hab s u.property f)⟫_ℂ =
    (intervalWeightedLineEnergy μ a b s f (((t : ℝ) + (u : ℝ)) / 2) : ℂ) := by
  let mid := traceMidpoint t u
  let Q : FractionalMellinTensor μ s ≃ₗᵢ[ℂ] P[0,0,s] := completedLpTwoTensorEquiv
  let M (v : Icc a b) := fractionalIntervalTrace μ hab s v.property f
  have hi (v : Icc a b) : (Q (M v) : K × ℝ → ℂ) =ᵐ[μ.prod (stripMeasure 0 0 s)]
      fun p => Real.exp ((v : ℝ) * p.2) • f p :=
    (stripProduct_to_base μ 0 0 s).ae_le (fractionalIntervalTrace_coordinates_ae μ hab s v.property f)
  have hm : ⟪Q (M t), Q (M u)⟫_ℂ = ⟪Q (M mid), Q (M mid)⟫_ℂ := by
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hi t, hi u, hi mid] with p ht hu hc
    rw [ht, hu, hc]
    simp only [RCLike.inner_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    have hExp : Real.exp ((t : ℝ) * p.2) * Real.exp ((u : ℝ) * p.2) =
        Real.exp ((mid : ℝ) * p.2) * Real.exp ((mid : ℝ) * p.2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      change (t : ℝ) * p.2 + (u : ℝ) * p.2 =
        (((t : ℝ) + (u : ℝ)) / 2) * p.2 + (((t : ℝ) + (u : ℝ)) / 2) * p.2
      ring
    have hC := congrArg (fun x : ℝ => (x : ℂ)) hExp
    simp only [Complex.ofReal_mul] at hC
    calc
      _ = (↑(Real.exp ((t : ℝ) * p.2)) * ↑(Real.exp ((u : ℝ) * p.2)) : ℂ) *
          (f p * (starRingEnd ℂ) (f p)) := by ring
      _ = _ := by rw [hC]; ring
  change ⟪Q (M t), Q (M u)⟫_ℂ = (intervalWeightedLineEnergy μ a b s f (mid : ℝ) : ℂ)
  rw [hm, inner_self_eq_norm_sq_to_K, LinearIsometryEquiv.norm_map]
  exact (Complex.ofReal_pow ‖M mid‖ 2).symm.trans
    (congrArg (fun x : ℝ => (x : ℂ)) (fractionalIntervalTrace_energy μ hab s mid.property f))

/-- Interior lines of a completed compact-strip class approach its endpoint
traces in the full fractional Sobolev tensor norm. -/
theorem fractionalIntervalTrace_continuous {a b : ℝ} (hab : a ≤ b) (s : ℝ) (f : P[a,b,s]) :
    Continuous (fun t : Icc a b => fractionalIntervalTrace μ hab s t.property f) := by
  let E := intervalWeightedLineEnergy μ a b s f
  let M (t : Icc a b) := fractionalIntervalTrace μ hab s t.property f
  have hE : Continuous (fun t : Icc a b => E t) :=
    continuousOn_iff_continuous_domRestrict.mp (intervalWeightedLineEnergy_continuousOn μ hab s f)
  let Q : FractionalMellinTensor μ s ≃ₗᵢ[ℂ] P[0,0,s] := completedLpTwoTensorEquiv
  have hdist (t u : Icc a b) :
      dist (M t) (M u) ^ 2 = E t - 2 * E ((t.val + u.val) / 2) + E u := by
    rw [← Q.isometry.dist_eq, dist_eq_norm, @norm_sub_sq ℂ]
    change ‖Q (M t)‖ ^ 2 - 2 * (⟪Q (M t), Q (M u)⟫_ℂ).re + ‖Q (M u)‖ ^ 2 = _
    have hi : ⟪Q (M t), Q (M u)⟫_ℂ = (E ((t.val + u.val) / 2) : ℂ) :=
      fractionalIntervalTrace_inner_midpoint μ hab s t u f
    rw [hi, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
    simp only [Complex.ofReal_re, M, fractionalIntervalTrace_energy, E]
  rw [continuous_iff_continuousAt]
  intro u
  have hmid : Continuous (fun t : Icc a b => traceMidpoint t u) :=
    (continuous_subtype_val.add continuous_const |>.div_const 2).subtype_mk _
  have hsame : traceMidpoint u u = u := Subtype.ext (by change (u.val + u.val) / 2 = u.val; ring)
  have hSq : Tendsto (fun t : Icc a b => dist (M t) (M u) ^ 2) (𝓝 u) (𝓝 0) := by
    simp_rw [hdist]
    have hC : Continuous (fun t : Icc a b => E t - 2 * E (traceMidpoint t u) + E u) :=
      (hE.sub ((hE.comp hmid).const_mul 2)).add continuous_const
    have hz : E u - 2 * E (traceMidpoint u u) + E u = 0 := by rw [hsame]; ring
    have ht := hC.tendsto u
    change Tendsto (fun t : Icc a b => E t - 2 * E (traceMidpoint t u) + E u) _ (𝓝 _) at ht
    rw [hz] at ht
    exact ht
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (dist_nonneg : 0 ≤ dist _ _), Real.sqrt_zero] using hSq.sqrt


omit [SFinite μ] in
private theorem memLp_of_intervalENorm_ne_top {I : Set ℝ} {a b s : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a ≤ b) {f : K × ℝ → ℂ} (hf : Measurable f)
    (h : hardySobolevIntervalENorm (μ.prod dx) Prod.snd I s f ≠ ⊤) :
    MemLp f 2 (μ.prod (stripMeasure a b s)) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [modulatedInterval_prod_weightedMeasure μ hab]
  exact lt_of_le_of_lt (le_iSup₂_of_le (⟨a, ha⟩ : I) (⟨b, hb⟩ : I) le_rfl) h.lt_top

omit [SFinite μ] in
private theorem rightHalfLine_memLp (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), 0 < p.2 → f p = 0)
    {a d : ℝ} (ha : b ≤ a) (hd : b ≤ d) (had : a ≤ d) :
    MemLp (f : K × ℝ → ℂ) 2 (μ.prod (stripMeasure a d s)) := by
  have hF := (Lp.stronglyMeasurable f).measurable
  apply memLp_of_intervalENorm_ne_top μ (I := Ici b) ha hd had hF
  rw [hardySobolevIntervalENorm_Ici_of_ae _ measurable_snd hF
    ((base_to_stripProduct μ b b s).ae_le hf), ← modulatedInterval_prod_weightedMeasure μ le_rfl]
  exact (Lp.memLp f).eLpNorm_lt_top.ne

omit [SFinite μ] in
private theorem leftHalfLine_memLp (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), p.2 < 0 → f p = 0)
    {a d : ℝ} (ha : a ≤ b) (hd : d ≤ b) (had : a ≤ d) :
    MemLp (f : K × ℝ → ℂ) 2 (μ.prod (stripMeasure a d s)) := by
  have hF := (Lp.stronglyMeasurable f).measurable
  apply memLp_of_intervalENorm_ne_top μ (I := Iic b) ha hd had hF
  rw [hardySobolevIntervalENorm_Iic_of_ae _ measurable_snd hF
    ((base_to_stripProduct μ b b s).ae_le hf), ← modulatedInterval_prod_weightedMeasure μ le_rfl]
  exact (Lp.memLp f).eLpNorm_lt_top.ne

/-- Fractional vertical traces for a class on a right-half-line abscissa base. -/
def fractionalRightHalfLineTrace (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), 0 < p.2 → f p = 0)
    (t : Ici b) : FractionalMellinTensor μ s :=
  fractionalMellinTensor μ (t : ℝ) s
    ((rightHalfLine_memLp μ b s f hf t.property t.property le_rfl).toLp (f : K × ℝ → ℂ))

/-- Fractional vertical traces for a class on a left-half-line abscissa base. -/
def fractionalLeftHalfLineTrace (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), p.2 < 0 → f p = 0)
    (t : Iic b) : FractionalMellinTensor μ s :=
  fractionalMellinTensor μ (t : ℝ) s
    ((leftHalfLine_memLp μ b s f hf t.property t.property le_rfl).toLp (f : K × ℝ → ℂ))


theorem fractionalRightHalfLineTrace_endpoint (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), 0 < p.2 → f p = 0) :
    fractionalRightHalfLineTrace μ b s f hf ⟨b, self_mem_Ici⟩ =
      fractionalMellinTensor μ b s f := by
  unfold fractionalRightHalfLineTrace
  rw [Lp.toLp_coeFn]

theorem fractionalLeftHalfLineTrace_endpoint (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), p.2 < 0 → f p = 0) :
    fractionalLeftHalfLineTrace μ b s f hf ⟨b, self_mem_Iic⟩ =
      fractionalMellinTensor μ b s f := by
  unfold fractionalLeftHalfLineTrace
  rw [Lp.toLp_coeFn]

private theorem line_norm_le_of_intervalNorm {J : Set ℝ} {t s : ℝ} (ht : t ∈ J)
    {f : K × ℝ → ℂ} (hf : MemLp f 2 (μ.prod (stripMeasure t t s)))
    {b : ℝ} (u : Lp ℂ 2 (μ.prod (stripMeasure b b s)))
    (he : hardySobolevIntervalENorm (μ.prod dx) Prod.snd J s f = ‖u‖ₑ) :
    ‖fractionalMellinTensor μ t s (hf.toLp f)‖ ≤ ‖u‖ := by
  rw [LinearIsometryEquiv.norm_map, Lp.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg _)
  rw [ofReal_norm, ← he, modulatedInterval_prod_weightedMeasure μ (a := t) le_rfl]
  exact le_iSup₂_of_le (⟨t, ht⟩ : J) (⟨t, ht⟩ : J) le_rfl

/-- All interior trace norms on a right-half-line base are bounded by the
finite endpoint norm. -/
theorem fractionalRightHalfLineTrace_norm_le (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), 0 < p.2 → f p = 0) (t : Ici b) :
    ‖fractionalRightHalfLineTrace μ b s f hf t‖ ≤ ‖f‖ := by
  change ‖fractionalMellinTensor μ t s
    ((rightHalfLine_memLp μ b s f hf t.property t.property le_rfl).toLp (f : K × ℝ → ℂ))‖ ≤ ‖f‖
  apply line_norm_le_of_intervalNorm μ t.property _ f
  rw [hardySobolevIntervalENorm_Ici_of_ae _ measurable_snd (Lp.stronglyMeasurable f).measurable
    ((base_to_stripProduct μ b b s).ae_le hf), ← modulatedInterval_prod_weightedMeasure μ le_rfl,
    Lp.enorm_def]

/-- All interior trace norms on a left-half-line base are bounded by the
finite endpoint norm. -/
theorem fractionalLeftHalfLineTrace_norm_le (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), p.2 < 0 → f p = 0) (t : Iic b) :
    ‖fractionalLeftHalfLineTrace μ b s f hf t‖ ≤ ‖f‖ := by
  change ‖fractionalMellinTensor μ t s
    ((leftHalfLine_memLp μ b s f hf t.property t.property le_rfl).toLp (f : K × ℝ → ℂ))‖ ≤ ‖f‖
  apply line_norm_le_of_intervalNorm μ t.property _ f
  rw [hardySobolevIntervalENorm_Iic_of_ae _ measurable_snd (Lp.stronglyMeasurable f).measurable
    ((base_to_stripProduct μ b b s).ae_le hf), ← modulatedInterval_prod_weightedMeasure μ le_rfl,
    Lp.enorm_def]

private theorem fractionalHalfLine_compare {a d t s : ℝ} (h : a ≤ d) (ht : t ∈ Icc a d)
    {f : K × ℝ → ℂ} (hl : MemLp f 2 (μ.prod (stripMeasure t t s)))
    (hb : MemLp f 2 (μ.prod (stripMeasure a d s))) :
    fractionalMellinTensor μ t s (hl.toLp f) =
      fractionalIntervalTrace μ h s ht (hb.toLp f) := by
  let Q : FractionalMellinTensor μ s ≃ₗᵢ[ℂ] P[0,0,s] := completedLpTwoTensorEquiv
  apply Q.injective
  apply Lp.ext
  apply (stripProduct_to_base μ 0 0 s).ae_le
  have h₁ : (Q (fractionalMellinTensor μ t s (hl.toLp f)) : K × ℝ → ℂ) =ᵐ[μ.prod dx]
      fun p => Real.exp (t * p.2) • (hl.toLp f) p :=
    fractionalMellinTensor_coordinates_ae μ t s (hl.toLp f)
  have h₂ : (Q (fractionalIntervalTrace μ h s ht (hb.toLp f)) : K × ℝ → ℂ) =ᵐ[μ.prod dx]
      fun p => Real.exp (t * p.2) • (hb.toLp f) p :=
    fractionalIntervalTrace_coordinates_ae μ h s ht (hb.toLp f)
  filter_upwards [h₁, h₂, (base_to_stripProduct μ t t s).ae_le hl.coeFn_toLp,
    (base_to_stripProduct μ a d s).ae_le hb.coeFn_toLp] with p h₁ h₂ hl hb
  rw [h₁, h₂, hl, hb]

set_option maxHeartbeats 900000 in
/-- Right half-plane traces converge in the fractional trace norm to the
finite endpoint trace. -/
theorem fractionalRightHalfLineTrace_continuousAt (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), 0 < p.2 → f p = 0) :
    ContinuousAt (fractionalRightHalfLineTrace μ b s f hf) (⟨b, self_mem_Ici⟩ : Ici b) := by
  have h : b ≤ b + 1 := by linarith
  let w := rightHalfLine_memLp μ b s f hf le_rfl h h
  let C (t : Ici b) : Icc b (b + 1) :=
    ⟨min (t : ℝ) (b + 1), le_min t.property h, min_le_right _ _⟩
  let M (t : Icc b (b + 1)) := fractionalIntervalTrace μ h s t.property (w.toLp (f : K × ℝ → ℂ))
  let T := fractionalRightHalfLineTrace μ b s f hf
  let z : Ici b := ⟨b, self_mem_Ici⟩
  have hC : Continuous C := (continuous_subtype_val.min continuous_const).subtype_mk _
  have hM : Continuous M := fractionalIntervalTrace_continuous μ h s (w.toLp (f : K × ℝ → ℂ))
  have he : ∀ᶠ t : Ici b in 𝓝 z, (t : ℝ) < b + 1 := by
    have hval : Continuous (fun t : Ici b => (t : ℝ)) := continuous_subtype_val
    exact (hval.tendsto z).eventually (Iio_mem_nhds (show (z : ℝ) < b + 1 by dsimp [z]; linarith))
  have hmatch : M ∘ C =ᶠ[𝓝 z] T := by
    filter_upwards [he] with t ht
    have ht' : (t : ℝ) ∈ Icc b (b + 1) := ⟨t.property, ht.le⟩
    have hCt : C t = ⟨(t : ℝ), ht'⟩ := Subtype.ext (min_eq_left ht.le)
    exact (congrArg M hCt).trans
      (fractionalHalfLine_compare μ h ht'
        (rightHalfLine_memLp μ b s f hf t.property t.property le_rfl) w).symm
  exact (hM.comp hC).continuousAt.congr hmatch

set_option maxHeartbeats 900000 in
/-- Left half-plane traces converge in the fractional trace norm to the
finite endpoint trace. -/
theorem fractionalLeftHalfLineTrace_continuousAt (b s : ℝ) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), p.2 < 0 → f p = 0) :
    ContinuousAt (fractionalLeftHalfLineTrace μ b s f hf) (⟨b, self_mem_Iic⟩ : Iic b) := by
  have h : b - 1 ≤ b := by linarith
  let w := leftHalfLine_memLp μ b s f hf h le_rfl h
  let C (t : Iic b) : Icc (b - 1) b :=
    ⟨max (t : ℝ) (b - 1), le_max_right _ _, max_le t.property h⟩
  let M (t : Icc (b - 1) b) := fractionalIntervalTrace μ h s t.property (w.toLp (f : K × ℝ → ℂ))
  let T := fractionalLeftHalfLineTrace μ b s f hf
  let z : Iic b := ⟨b, self_mem_Iic⟩
  have hC : Continuous C := (continuous_subtype_val.max continuous_const).subtype_mk _
  have hM : Continuous M := fractionalIntervalTrace_continuous μ h s (w.toLp (f : K × ℝ → ℂ))
  have he : ∀ᶠ t : Iic b in 𝓝 z, b - 1 < (t : ℝ) := by
    have hval : Continuous (fun t : Iic b => (t : ℝ)) := continuous_subtype_val
    exact (hval.tendsto z).eventually (Ioi_mem_nhds (show b - 1 < (z : ℝ) by dsimp [z]; linarith))
  have hmatch : M ∘ C =ᶠ[𝓝 z] T := by
    filter_upwards [he] with t ht
    have ht' : (t : ℝ) ∈ Icc (b - 1) b := ⟨ht.le, t.property⟩
    have hCt : C t = ⟨(t : ℝ), ht'⟩ := Subtype.ext (max_eq_left ht.le)
    exact (congrArg M hCt).trans
      (fractionalHalfLine_compare μ h ht'
        (leftHalfLine_memLp μ b s f hf t.property t.property le_rfl) w).symm
  exact (hM.comp hC).continuousAt.congr hmatch


/-- The analytic trace subspace whose inverse Fourier profile is supported
in the specified logarithmic region. This definition is independent of the
choice of finite boundary abscissa. -/
def fractionalMellinSupportedSpace (s : ℝ) (R : Set ℝ) :
    Submodule ℂ (FractionalMellinTensor μ s) :=
  (lpTwoRadialSupport μ (stripMeasure 0 0 s) R).comap completedLpTwoTensorEquiv.toLinearMap

theorem fractionalMellinSupportedSpace_mem_iff (b s : ℝ) (R : Set ℝ) (f : P[b,b,s]) :
    fractionalMellinTensor μ b s f ∈ fractionalMellinSupportedSpace μ s R ↔
      f ∈ lpTwoRadialSupport μ (stripMeasure b b s) R := by
  let Q : FractionalMellinTensor μ s ≃ₗᵢ[ℂ] P[0,0,s] := completedLpTwoTensorEquiv
  let g := Q (fractionalMellinTensor μ b s f)
  have hae : (g : K × ℝ → ℂ) =ᵐ[μ.prod dx] fun p => Real.exp (b * p.2) • f p :=
    fractionalMellinTensor_coordinates_ae μ b s f
  change (∀ᵐ p ∂μ.prod (stripMeasure 0 0 s), p.2 ∉ R → g p = 0) ↔
    (∀ᵐ p ∂μ.prod (stripMeasure b b s), p.2 ∉ R → f p = 0)
  constructor
  · intro h
    apply (stripProduct_to_base μ b b s).ae_le
    filter_upwards [(base_to_stripProduct μ 0 0 s).ae_le h, hae] with p hz hp hR
    have hh : Real.exp (b * p.2) • f p = 0 := hp.symm.trans (hz hR)
    exact (smul_eq_zero.mp hh).resolve_left (Real.exp_pos _).ne'
  · intro h
    apply (stripProduct_to_base μ 0 0 s).ae_le
    filter_upwards [(base_to_stripProduct μ b b s).ae_le h, hae] with p hz hp hR
    exact hp.trans (by rw [hz hR, smul_zero])

/-- The endpoint Mellin map is an isometric equivalence onto the supported
analytic trace space, for either closed support ray and all real orders. -/
def fractionalMellinSupportedEquiv (b s : ℝ) (R : Set ℝ) :
    lpTwoRadialSupport μ (stripMeasure b b s) R ≃ₗᵢ[ℂ] fractionalMellinSupportedSpace μ s R := by
  let T := fractionalMellinTensor μ b s
  let H := lpTwoRadialSupport μ (stripMeasure b b s) R
  let M := T.toLinearIsometry.comp (Submodule.subtypeₗᵢ H)
  let J : H →ₗᵢ[ℂ] fractionalMellinSupportedSpace μ s R :=
    ⟨M.toLinearMap.codRestrict _ (fun f =>
      (fractionalMellinSupportedSpace_mem_iff μ b s R f.val).mpr f.property), M.norm_map⟩
  apply LinearIsometryEquiv.ofSurjective J
  intro g
  let f := T.symm g.val
  have hf : T f = g.val := T.apply_symm_apply _
  have hmem : f ∈ lpTwoRadialSupport μ (stripMeasure b b s) R :=
    (fractionalMellinSupportedSpace_mem_iff μ b s R f).mp (hf.symm ▸ g.property)
  exact ⟨⟨f, hmem⟩, Subtype.ext hf⟩

section Character

variable [TopologicalSpace K] [BorelSpace K] [CommGroup K] [IsFiniteMeasure μ]

set_option maxHeartbeats 900000 in
/-- A right-half-plane trace is the true character Mellin integral at
almost every height on every interior line. -/
theorem fractionalRightHalfLineTrace_values_ae (b : ℝ) {s : ℝ} (hs : 0 ≤ s) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), 0 < p.2 → f p = 0)
    (t : Ici b) (ht : b < (t : ℝ)) (χ : PontryaginDual K) :
    (fractionalMellinTensorValues μ hs χ (fractionalRightHalfLineTrace μ b s f hf t) : ℝ → ℂ)
      =ᵐ[dx] fun y => ∫ p : K × ℝ, (χ p.1 : ℂ) * f p *
        mellinEvaluationKernel 0 (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) p.2 ∂μ.prod dx := by
  have h : b ≤ (t : ℝ) + 1 := by linarith
  have ht' : (t : ℝ) ∈ Ioo b ((t : ℝ) + 1) := ⟨ht, by linarith⟩
  let w := rightHalfLine_memLp μ b s f hf le_rfl h h
  have hc := fractionalHalfLine_compare μ h (Ioo_subset_Icc_self ht')
    (rightHalfLine_memLp μ b s f hf t.property t.property le_rfl) w
  change (fractionalMellinTensorValues μ hs χ (fractionalMellinTensor μ t s _) : ℝ → ℂ) =ᵐ[dx] _
  rw [hc]
  refine (fractionalIntervalTrace_values_ae μ h hs ht' χ (w.toLp (f : K × ℝ → ℂ))).trans
    (.of_forall fun y => ?_)
  apply integral_congr_ae
  have he : (w.toLp (f : K × ℝ → ℂ) : K × ℝ → ℂ) =ᵐ[μ.prod dx] f :=
    (base_to_stripProduct μ b ((t : ℝ) + 1) s).ae_le w.coeFn_toLp
  filter_upwards [he] with p hp
  exact congrArg (fun v : ℂ => (χ p.1 : ℂ) * v *
    mellinEvaluationKernel 0 (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) p.2) hp

set_option maxHeartbeats 900000 in
/-- A left-half-plane trace is the true character Mellin integral at
almost every height on every interior line. -/
theorem fractionalLeftHalfLineTrace_values_ae (b : ℝ) {s : ℝ} (hs : 0 ≤ s) (f : P[b,b,s])
    (hf : ∀ᵐ p ∂μ.prod (stripMeasure b b s), p.2 < 0 → f p = 0)
    (t : Iic b) (ht : (t : ℝ) < b) (χ : PontryaginDual K) :
    (fractionalMellinTensorValues μ hs χ (fractionalLeftHalfLineTrace μ b s f hf t) : ℝ → ℂ)
      =ᵐ[dx] fun y => ∫ p : K × ℝ, (χ p.1 : ℂ) * f p *
        mellinEvaluationKernel 0 (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) p.2 ∂μ.prod dx := by
  have h : (t : ℝ) - 1 ≤ b := by linarith
  have ht' : (t : ℝ) ∈ Ioo ((t : ℝ) - 1) b := ⟨by linarith, ht⟩
  let w := leftHalfLine_memLp μ b s f hf h le_rfl h
  have hc := fractionalHalfLine_compare μ h (Ioo_subset_Icc_self ht')
    (leftHalfLine_memLp μ b s f hf t.property t.property le_rfl) w
  change (fractionalMellinTensorValues μ hs χ (fractionalMellinTensor μ t s _) : ℝ → ℂ) =ᵐ[dx] _
  rw [hc]
  refine (fractionalIntervalTrace_values_ae μ h hs ht' χ (w.toLp (f : K × ℝ → ℂ))).trans
    (.of_forall fun y => ?_)
  apply integral_congr_ae
  have he : (w.toLp (f : K × ℝ → ℂ) : K × ℝ → ℂ) =ᵐ[μ.prod dx] f :=
    (base_to_stripProduct μ ((t : ℝ) - 1) b s).ae_le w.coeFn_toLp
  filter_upwards [he] with p hp
  exact congrArg (fun v : ℂ => (χ p.1 : ℂ) * v *
    mellinEvaluationKernel 0 (⟨(t : ℝ), 2 * Real.pi * y⟩ : ℂ) p.2) hp

end Character

end
end Masullo
