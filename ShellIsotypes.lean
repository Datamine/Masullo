import ShellConvergence
import NormOneExact
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Complex.Circle

open Filter Function MeasureTheory NumberField Set Topology

namespace Masullo

noncomputable section

variable {F : Type*} [Field F] [NumberField F]
  [MeasurableSpace (IdeleClass F)] [BorelSpace (IdeleClass F)]

/-- The norm-one fiber integral on the actual quotient of the ideles. -/
def shellCharacterAverage (μ : Measure (normOneIdeleClass F))
    (ω : IdeleClass F →* Circle) (u : IdeleClass F → ℂ) (g : IdeleClass F) : ℂ :=
  ∫ h : normOneIdeleClass F, u (g * h.val) * (ω (g * h.val) : ℂ) ∂μ

theorem shellCharacterAverage_mul_normOne (μ : Measure (normOneIdeleClass F)) [μ.IsHaarMeasure]
    (ω : IdeleClass F →* Circle) (u : IdeleClass F → ℂ)
    (g : IdeleClass F) (a : normOneIdeleClass F) :
    shellCharacterAverage μ ω u (g * a.val) = shellCharacterAverage μ ω u g := by
  let A (h : normOneIdeleClass F) := u (g * h.val) * (ω (g * h.val) : ℂ)
  let e := (Homeomorph.mulLeft a).toMeasurableEquiv
  have hmap : μ.map e = μ := Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := μ) a
  have hh : (∫ h, A (a * h) ∂μ) = ∫ h, A h ∂μ := by
    have he := e.measurableEmbedding.integral_map (μ := μ) A
    rw [hmap] at he
    exact he.symm
  simpa only [shellCharacterAverage, mul_assoc, Subgroup.coe_mul, A] using hh

/-- The fiber average descends to the quotient by the norm-one class group. -/
def shellCharacterAverageDescend (μ : Measure (normOneIdeleClass F)) [μ.IsHaarMeasure]
    (ω : IdeleClass F →* Circle) (u : IdeleClass F → ℂ) :
    IdeleClass F ⧸ normOneIdeleClass F → ℂ :=
  Quotient.lift (shellCharacterAverage μ ω u) fun x y h => by
    change (QuotientGroup.leftRel (normOneIdeleClass F)).r x y at h
    rw [QuotientGroup.leftRel_apply] at h
    let a : normOneIdeleClass F := ⟨x⁻¹ * y, h⟩
    have he : y = x * a.val := by simp [a]
    rw [he, shellCharacterAverage_mul_normOne]

/-- The corrected fiber-average limit in Corollary 11.1.1.5. Absolute
integrability is assumed for a common majorant summed on each orbit, and
pointwise convergence on the class group comes from Corollary 11.1.1.4. -/
theorem shellCharacterAverage_tendsto (μ : Measure (normOneIdeleClass F)) [μ.IsHaarMeasure]
    (ω : IdeleClass F →* Circle) (hω : Continuous ω) (f : ℕ → Adeles F → ℂ)
    (hf : ∀ k, f k ∈ bruhatSubmodule F) (l : Idele F → ℂ)
    (hlim : ∀ c : IdeleClass F, Tendsto (fun k => adelicTheta F (f k) c) atTop (𝓝 (shellLimitClass l c)))
    (B : IdeleClass F → normOneIdeleClass F → ℝ)
    (hB : ∀ g, Integrable (B g) μ)
    (hb : ∀ k g h, ‖adelicTheta F (f k) (g * h.val)‖ ≤ B g h) :
    (∀ g, Integrable (fun h : normOneIdeleClass F =>
      shellLimitClass l (g * h.val) * (ω (g * h.val) : ℂ)) μ) ∧
    (∀ k g, Integrable (fun h : normOneIdeleClass F =>
      adelicTheta F (f k) (g * h.val) * (ω (g * h.val) : ℂ)) μ) ∧
    ∀ q : IdeleClass F ⧸ normOneIdeleClass F,
      Tendsto (fun k => shellCharacterAverageDescend μ ω (adelicTheta F (f k)) q) atTop
        (𝓝 (shellCharacterAverageDescend μ ω (shellLimitClass l) q)) := by
  have hcont (k : ℕ) : Continuous (adelicTheta F (f k)) :=
    adelicTheta_continuous F (bruhat_theta_continuous_and_invariant (hf k)).1
  have hmeas : Measurable (shellLimitClass l) :=
    measurable_of_tendsto_metrizable (fun k => (hcont k).measurable) (tendsto_pi_nhds.mpr hlim)
  have hW (g : IdeleClass F) : Continuous (fun h : normOneIdeleClass F => g * h.val) :=
    (continuous_const (y := g)).mul
      (continuous_subtype_val : Continuous (Subtype.val : normOneIdeleClass F → IdeleClass F))
  have hPhase (g : IdeleClass F) : Measurable (fun h : normOneIdeleClass F => (ω (g * h.val) : ℂ)) :=
    (continuous_subtype_val.comp (hω.comp (hW g))).measurable
  have hL (g : IdeleClass F) (h : normOneIdeleClass F) :
      Tendsto (fun k => adelicTheta F (f k) (g * h.val) * (ω (g * h.val) : ℂ)) atTop
        (𝓝 (shellLimitClass l (g * h.val) * (ω (g * h.val) : ℂ))) :=
    (hlim (g * h.val)).mul tendsto_const_nhds
  have hFB (k : ℕ) (g : IdeleClass F) (h : normOneIdeleClass F) :
      ‖adelicTheta F (f k) (g * h.val) * (ω (g * h.val) : ℂ)‖ ≤ B g h := by
    rw [norm_mul, Circle.norm_coe, mul_one]
    exact hb k g h
  have hFs (k : ℕ) (g : IdeleClass F) : StronglyMeasurable (fun h : normOneIdeleClass F =>
      adelicTheta F (f k) (g * h.val) * (ω (g * h.val) : ℂ)) :=
    (((hcont k).measurable.comp (hW g).measurable).mul (hPhase g)).stronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · intro g
    apply (hB g).mono ((hmeas.comp (hW g).measurable).mul (hPhase g)).aestronglyMeasurable
    exact Eventually.of_forall fun h =>
      (le_of_tendsto (tendsto_norm.comp (hL g h)) (Eventually.of_forall fun k => hFB k g h)).trans
        (le_abs_self _)
  · intro k g
    exact (hB g).mono (hFs k g).aestronglyMeasurable
      (Eventually.of_forall fun h => (hFB k g h).trans (le_abs_self _))
  · intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    change Tendsto (fun k => shellCharacterAverage μ ω (adelicTheta F (f k)) g) atTop
      (𝓝 (shellCharacterAverage μ ω (shellLimitClass l) g))
    exact tendsto_integral_of_dominated_convergence (B g)
      (fun k => (hFs k g).aestronglyMeasurable) (hB g)
      (fun k => Eventually.of_forall (hFB k g)) (Eventually.of_forall (hL g))

/-- When the Haar measure on norm-one classes is normalized by the
representative region, the class average is exactly the manuscript's
integral over that region. -/
theorem shellCharacterAverage_transversal
    [MeasurableSpace ((ideleNorm F).ker)] [BorelSpace ((ideleNorm F).ker)]
    [BorelSpace (normOneIdeleClass F)]
    (μ : Measure ((ideleNorm F).ker)) (D : Set ((ideleNorm F).ker))
    (ω : IdeleClass F →* Circle) (hω : Continuous ω)
    (u : IdeleClass F → ℂ) (hu : Measurable u) (g : Idele F) :
    shellCharacterAverage ((μ.restrict D).map (normOneIdelesToClasses F)) ω u (ideleClassMap F g) =
      ∫ h in D, u (ideleClassMap F (g * h.val)) * (ω (ideleClassMap F (g * h.val)) : ℂ) ∂μ := by
  let p := normOneIdelesToClasses F
  have hp : Continuous p := ((ideleClassMap_continuous F).comp continuous_subtype_val).subtype_mk _
  let V (h : normOneIdeleClass F) :=
    u (ideleClassMap F g * h.val) * (ω (ideleClassMap F g * h.val) : ℂ)
  have hg : Continuous (fun h : normOneIdeleClass F => ideleClassMap F g * h.val) :=
    (continuous_const (y := ideleClassMap F g)).mul
      (continuous_subtype_val : Continuous (Subtype.val : normOneIdeleClass F → IdeleClass F))
  have hV : Measurable V :=
    (hu.comp hg.measurable).mul (continuous_subtype_val.comp (hω.comp hg)).measurable
  unfold shellCharacterAverage
  rw [integral_map hp.measurable.aemeasurable hV.aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun h => by simp only [V, p, map_mul]; rfl

/-- Corollary 11.1.1.5 after requiring a summable bound on every
representative's orbit. In the normalization of
`shellCharacterAverage_transversal`, these are the printed fiber integrals. -/
theorem adeleShell_character_quotient_limit
    (μ : Measure (normOneIdeleClass F)) [μ.IsHaarMeasure]
    (ω : IdeleClass F →* Circle) (hω : Continuous ω) (f : ℕ → Adeles F → ℂ)
    (hf : ∀ k, f k ∈ bruhatSubmodule F) (l : Idele F → ℂ)
    (hl : ∀ g : Idele F, Tendsto (fun k => f k g.val) atTop (𝓝 (l g)))
    (D : Set (Idele F)) (hD : SurjOn (ideleClassMap F) D univ)
    (b : Idele F → Fˣ → ℝ) (hbs : ∀ g ∈ D, Summable (b g))
    (hb : ∀ g ∈ D, ∀ k ξ, ‖thetaSummand F (f k) g ξ‖ ≤ b g ξ)
    (r : IdeleClass F → Idele F) (hr : ∀ c, r c ∈ D ∧ ideleClassMap F (r c) = c)
    (hI : ∀ c, Integrable (fun h : normOneIdeleClass F => ∑' ξ : Fˣ, b (r (c * h.val)) ξ) μ) :
    (∀ g : Idele F, Summable (fun ξ : Fˣ => ‖l (principalIdele F ξ * g)‖)) ∧
    (∀ g, Integrable (fun h : normOneIdeleClass F =>
      shellLimitClass l (g * h.val) * (ω (g * h.val) : ℂ)) μ) ∧
    (∀ k g, Integrable (fun h : normOneIdeleClass F =>
      adelicTheta F (f k) (g * h.val) * (ω (g * h.val) : ℂ)) μ) ∧
    ∀ q : IdeleClass F ⧸ normOneIdeleClass F,
      Tendsto (fun k => shellCharacterAverageDescend μ ω (adelicTheta F (f k)) q) atTop
        (𝓝 (shellCharacterAverageDescend μ ω (shellLimitClass l) q)) := by
  obtain ⟨ha, hp⟩ := adeleShell_class_pointwise f l hl D hD
    fun g hg => ⟨b g, hbs g hg, hb g hg⟩
  refine ⟨ha, shellCharacterAverage_tendsto μ ω hω f hf l hp _ hI ?_⟩
  intro k g h
  let x := r (g * h.val)
  have hx := hr (g * h.val)
  change ‖adelicTheta F (f k) (g * h.val)‖ ≤ ∑' ξ : Fˣ, b x ξ
  rw [← hx.2, adelicTheta_mk]
  have hS : Summable (fun ξ : Fˣ => ‖thetaSummand F (f k) x ξ‖) :=
    (hbs x hx.1).of_norm_bounded fun ξ => by
      simpa only [norm_norm] using hb x hx.1 k ξ
  exact (norm_tsum_le_tsum_norm hS).trans (hS.tsum_le_tsum (hb x hx.1 k) (hbs x hx.1))

end

end Masullo
