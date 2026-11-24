import HardySobolevDuality

open Filter Function MeasureTheory Set Topology
open scoped CompactlySupported ENNReal NNReal

namespace Masullo

noncomputable section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (ℓ : C(X, ℝ)) (a b s : ℝ)

private abbrev intervalAmplitude (x : X) := stripSobolevAmplitude a b s (ℓ x)

omit [MeasurableSpace X] [BorelSpace X] in
private theorem intervalAmplitude_continuous : Continuous (intervalAmplitude ℓ a b s) :=
  (stripSobolevAmplitude_continuous a b s).comp ℓ.continuous

omit [MeasurableSpace X] [BorelSpace X] in
private theorem intervalAmplitude_pos (x : X) : 0 < intervalAmplitude ℓ a b s x :=
  stripSobolevAmplitude_pos a b s (ℓ x)

/-- The interval completion for the logarithmic modulus and base measure. -/
abbrev IntervalL2 :=
  Lp ℂ 2 (amplitudeMeasure μ (intervalAmplitude ℓ a b s))

/-- The second factor uses the reciprocal of the same interval density. -/
abbrev ReciprocalIntervalL2 :=
  Lp ℂ 2 (amplitudeMeasure μ (fun x => (intervalAmplitude ℓ a b s x)⁻¹))

omit [BorelSpace X] in
theorem intervalL2_measure (hab : a ≤ b) :
    amplitudeMeasure μ (intervalAmplitude ℓ a b s) = hardySobolevMeasure μ ℓ a b s := by
  simp only [amplitudeMeasure, hardySobolevMeasure, intervalAmplitude, stripSobolevAmplitude_sq hab]

omit [BorelSpace X] in
theorem reciprocalIntervalL2_measure (hab : a ≤ b) :
    amplitudeMeasure μ (fun x => (intervalAmplitude ℓ a b s x)⁻¹) =
      μ.withDensity (fun x => ENNReal.ofReal ((hardySobolevWeight a b s (ℓ x))⁻¹)) := by
  simp only [amplitudeMeasure, inv_pow, intervalAmplitude, stripSobolevAmplitude_sq hab]

private abbrev intervalCoordinates :=
  amplitudeL2Iso μ (intervalAmplitude ℓ a b s)
    (intervalAmplitude_continuous ℓ a b s).measurable (intervalAmplitude_pos ℓ a b s)

private abbrev reciprocalIntervalCoordinates :=
  amplitudeL2Iso μ (fun x => (intervalAmplitude ℓ a b s x)⁻¹)
    (intervalAmplitude_continuous ℓ a b s).measurable.inv
    (fun x => inv_pos.mpr (intervalAmplitude_pos ℓ a b s x))

/-- Proposition 9.2.2.11 on the corrected pair of completions.
The logarithmic modulus can be any continuous real function. -/
def modulatedIntervalDuality :
    ReciprocalIntervalL2 μ ℓ a b s ≃ₗᵢ[ℂ] StrongDual ℂ (IntervalL2 μ ℓ a b s) :=
  (reciprocalIntervalCoordinates μ ℓ a b s).trans
    ((sobolevBilinearDual μ).trans (precomposeDualIso (intervalCoordinates μ ℓ a b s)))

private theorem intervalCoordinates_mul_ae (f : IntervalL2 μ ℓ a b s)
    (g : ReciprocalIntervalL2 μ ℓ a b s) :
    (fun x => intervalCoordinates μ ℓ a b s f x * reciprocalIntervalCoordinates μ ℓ a b s g x)
      =ᵐ[μ] fun x => f x * g x := by
  filter_upwards [amplitudeL2Iso_ae μ _ _ _ f, amplitudeL2Iso_ae μ _ _ _ g] with x hf hg
  rw [show intervalCoordinates μ ℓ a b s f x = _ from hf,
    show reciprocalIntervalCoordinates μ ℓ a b s g x = _ from hg,
    Complex.real_smul, Complex.real_smul, mul_mul_mul_comm, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (intervalAmplitude_pos ℓ a b s x).ne', Complex.ofReal_one, one_mul]

theorem modulatedIntervalDuality_integrable (f : IntervalL2 μ ℓ a b s)
    (g : ReciprocalIntervalL2 μ ℓ a b s) : Integrable (fun x => f x * g x) μ :=
  (MemLp.integrable_mul (p := 2) (q := 2) (Lp.memLp (intervalCoordinates μ ℓ a b s f))
    (Lp.memLp (reciprocalIntervalCoordinates μ ℓ a b s g))).congr
      (intervalCoordinates_mul_ae μ ℓ a b s f g)

theorem modulatedIntervalDuality_apply (f : IntervalL2 μ ℓ a b s)
    (g : ReciprocalIntervalL2 μ ℓ a b s) :
    modulatedIntervalDuality μ ℓ a b s g f = ∫ x, f x * g x ∂μ := by
  change sobolevBilinearDual μ (reciprocalIntervalCoordinates μ ℓ a b s g)
    (intervalCoordinates μ ℓ a b s f) = _
  rw [sobolevBilinearDual_apply]
  exact integral_congr_ae (intervalCoordinates_mul_ae μ ℓ a b s f g)

theorem modulatedIntervalDuality_continuous :
    Continuous (fun (p : IntervalL2 μ ℓ a b s × ReciprocalIntervalL2 μ ℓ a b s) =>
      ∫ x, p.1 x * p.2 x ∂μ) := by
  simp_rw [← modulatedIntervalDuality_apply]
  exact ((modulatedIntervalDuality μ ℓ a b s).continuous.comp continuous_snd).clm_apply
    continuous_fst

/-- A dual functional expressed by its weighted bilinear Riesz vector
is represented in the reciprocal space by multiplying by the interval density. -/
theorem modulatedIntervalDuality_symm_ae (hab : a ≤ b) (ψ : IntervalL2 μ ℓ a b s) :
    ((modulatedIntervalDuality μ ℓ a b s).symm
      (sobolevBilinearDual (amplitudeMeasure μ (intervalAmplitude ℓ a b s)) ψ) : X → ℂ)
      =ᵐ[μ] fun x => hardySobolevWeight a b s (ℓ x) • ψ x := by
  let r := intervalAmplitude ℓ a b s
  let V := reciprocalIntervalCoordinates μ ℓ a b s
  let U := intervalCoordinates μ ℓ a b s
  let Λ := sobolevBilinearDual (amplitudeMeasure μ r) ψ
  let ρ (x : X) : ℝ≥0 := Real.toNNReal (r x ^ 2)
  have hr := (intervalAmplitude_continuous ℓ a b s).measurable
  have hpos := intervalAmplitude_pos ℓ a b s
  have hρ : Measurable ρ := (hr.pow_const 2).real_toNNReal
  have hchange (p : IntervalL2 μ ℓ a b s) :
      Λ p = sobolevBilinearDual μ (U ψ) (U p) := by
    change sobolevBilinearDual (amplitudeMeasure μ r) ψ p = _
    rw [sobolevBilinearDual_apply, sobolevBilinearDual_apply]
    calc
      _ = ∫ x, ρ x • (p x * ψ x) ∂μ :=
        integral_withDensity_eq_integral_smul hρ (fun x => p x * ψ x)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [amplitudeL2Iso_ae μ r hr hpos p,
          amplitudeL2Iso_ae μ r hr hpos ψ] with x hp hψ
        change U p x = _ at hp
        change U ψ x = _ at hψ
        rw [hp, hψ, NNReal.smul_def, show (ρ x : ℝ) = r x ^ 2 from
          Real.coe_toNNReal _ (sq_nonneg _), Complex.real_smul, Complex.real_smul,
          Complex.real_smul, mul_mul_mul_comm, ← Complex.ofReal_mul, pow_two]
  have hrep : (modulatedIntervalDuality μ ℓ a b s).symm Λ = V.symm (U ψ) := by
    apply (modulatedIntervalDuality μ ℓ a b s).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext p
    change Λ p = sobolevBilinearDual μ (V (V.symm (U ψ))) (U p)
    rw [V.apply_symm_apply]
    exact hchange p
  change ((modulatedIntervalDuality μ ℓ a b s).symm Λ : X → ℂ) =ᵐ[μ] _
  rw [hrep]
  have hV : μ ≪ amplitudeMeasure μ (fun x => (r x)⁻¹) :=
    absolutelyContinuous_amplitudeMeasure μ _ hr.inv (fun x => inv_pos.mpr (hpos x))
  filter_upwards [hV.ae_le (amplitudeL2Iso_symm_ae μ _ hr.inv
    (fun x => inv_pos.mpr (hpos x)) (U ψ)), amplitudeL2Iso_ae μ r hr hpos ψ] with x hv hu
  change V.symm (U ψ) x = _ at hv
  change U ψ x = _ at hu
  rw [hv, hu]
  change (r x)⁻¹⁻¹ • (r x • ψ x) = _
  rw [inv_inv, smul_smul, ← pow_two]
  exact congrArg (· • ψ x) (stripSobolevAmplitude_sq hab s (ℓ x))

section Tests

variable [T2Space X] [LocallyCompactSpace X] [μ.Regular]

private def amplitudeTest (r : C(X, ℝ)) (hr : ∀ x, 0 < r x) (f : C_c(X, ℂ)) :
    Lp ℂ 2 (amplitudeMeasure μ r) :=
  (amplitudeL2Iso μ r r.continuous.measurable hr).symm
    (sobolevWeightedTest μ ⟨fun x => (r x : ℂ), Complex.continuous_ofReal.comp r.continuous⟩ f)

private theorem amplitudeTest_dense (r : C(X, ℝ)) (hr : ∀ x, 0 < r x) :
    DenseRange (amplitudeTest μ r hr) := by
  apply (amplitudeL2Iso μ r r.continuous.measurable hr).symm.surjective.denseRange.comp
    _ (amplitudeL2Iso μ r r.continuous.measurable hr).symm.continuous
  exact denseRange_sobolevWeightedTest μ _ fun x => Complex.ofReal_ne_zero.mpr (hr x).ne'

omit [T2Space X] [LocallyCompactSpace X] in
private theorem amplitudeTest_ae (r : C(X, ℝ)) (hr : ∀ x, 0 < r x) (f : C_c(X, ℂ)) :
    (amplitudeTest μ r hr f : X → ℂ) =ᵐ[μ] f := by
  let c : C(X, ℂ) := ⟨fun x => (r x : ℂ), Complex.continuous_ofReal.comp r.continuous⟩
  filter_upwards [(absolutelyContinuous_amplitudeMeasure μ r r.continuous.measurable hr).ae_le
    (amplitudeL2Iso_symm_ae μ r r.continuous.measurable hr (sobolevWeightedTest μ c f)),
    sobolevWeightedTest_ae μ c f] with x h h'
  change amplitudeTest μ r hr f x = _ at h
  rw [h, h', Complex.real_smul]
  change (↑((r x)⁻¹) : ℂ) * ((r x : ℂ) * f x) = f x
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hr x).ne',
    Complex.ofReal_one, one_mul]

/-- The same compactly supported core works in both weighted spaces, with
the original integral pairing. -/
theorem modulatedIntervalDuality_denseTests :
    ∃ (i : C_c(X, ℂ) → IntervalL2 μ ℓ a b s)
      (j : C_c(X, ℂ) → ReciprocalIntervalL2 μ ℓ a b s),
      DenseRange i ∧ DenseRange j ∧
      (∀ u, (i u : X → ℂ) =ᵐ[μ] u) ∧ (∀ v, (j v : X → ℂ) =ᵐ[μ] v) ∧
      (∀ u v, modulatedIntervalDuality μ ℓ a b s (j v) (i u) = ∫ x, u x * v x ∂μ) ∧
      ∀ Q : IntervalL2 μ ℓ a b s × ReciprocalIntervalL2 μ ℓ a b s → ℂ,
        Continuous Q → (∀ u v, Q (i u, j v) = ∫ x, u x * v x ∂μ) →
        Q = fun p => ∫ x, p.1 x * p.2 x ∂μ := by
  let r : C(X, ℝ) := ⟨_, intervalAmplitude_continuous ℓ a b s⟩
  let t : C(X, ℝ) := ⟨fun x => (r x)⁻¹,
    r.continuous.inv₀ fun x => (intervalAmplitude_pos ℓ a b s x).ne'⟩
  have hr : ∀ x, 0 < r x := intervalAmplitude_pos ℓ a b s
  have ht : ∀ x, 0 < t x := fun x => inv_pos.mpr (hr x)
  have hd := amplitudeTest_dense μ r hr
  have he := amplitudeTest_dense μ t ht
  have hpair (u v : C_c(X, ℂ)) :
      modulatedIntervalDuality μ ℓ a b s (amplitudeTest μ t ht v) (amplitudeTest μ r hr u) =
        ∫ x, u x * v x ∂μ := by
    rw [modulatedIntervalDuality_apply]
    apply integral_congr_ae
    filter_upwards [amplitudeTest_ae μ r hr u, amplitudeTest_ae μ t ht v] with x hu hv
    rw [hu, hv]
  refine ⟨amplitudeTest μ r hr, amplitudeTest μ t ht, hd, he,
    amplitudeTest_ae μ r hr, amplitudeTest_ae μ t ht, hpair, ?_⟩
  intro Q hQ hEq
  apply (hd.prodMap he).equalizer hQ (modulatedIntervalDuality_continuous μ ℓ a b s)
  funext p
  exact (hEq p.1 p.2).trans ((hpair p.1 p.2).symm.trans
    (modulatedIntervalDuality_apply μ ℓ a b s _ _))

end Tests

end

end Masullo
