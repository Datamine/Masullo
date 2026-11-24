import BruhatSplitRadialSeminorms

open Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {H G : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H]
  [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Directional words commute with taking the same test in two group
presentations. The direction on the receiving group is the image direction. -/
theorem bruhatDerivativeWord_comp_hom
    (e : H →ₜ* G) (cs : List (Multiplicative ℝ →ₜ* H))
    (u : BruhatSchwartz H) (v : BruhatSchwartz G) (huv : ∀ x : H, u.val x = v.val (e x)) :
    ∀ x : H, (WholeBruhatStage.bruhatDerivativeWord cs u).val x =
      (WholeBruhatStage.bruhatDerivativeWord (cs.map fun c => e.comp c) v).val (e x) := by
  induction cs with
  | nil => exact huv
  | cons c cs ih =>
    intro x
    let a := WholeBruhatStage.bruhatDerivativeWord cs u
    let b := WholeBruhatStage.bruhatDerivativeWord (cs.map fun c => e.comp c) v
    change bruhatOrbitDeriv c a.val x = bruhatOrbitDeriv (e.comp c) b.val (e x)
    unfold bruhatOrbitDeriv
    congr 1
    funext t
    rw [ih, map_mul]
    rfl

variable [MeasurableSpace H] [BorelSpace H] [MeasurableSpace G] [BorelSpace G]

/-- Transport of the numerical integral, with the section and norm-one
measure transported along the same homomorphism. -/
theorem bruhatSplitRadialNorm_map_normOne
    (e : H →ₜ* G) {K : Subgroup H} {L : Subgroup G}
    (j : K →ₜ* L) (hj : ∀ k, (j k).val = e k.val)
    (σ : Multiplicative ℝ →ₜ* H) (ν : Measure K)
    (p : ℝ≥0∞) (Q : Polynomial ℂ)
    (u : BruhatSchwartz H) (v : BruhatSchwartz G) (huv : ∀ x : H, u.val x = v.val (e x)) :
    bruhatSplitRadialNorm σ ν p Q u =
      bruhatSplitRadialNorm (e.comp σ) (Measure.map j ν) p Q v := by
  unfold bruhatSplitRadialNorm
  apply congrArg (fun z : ℝ => z ^ (1 / p.toReal))
  apply integral_congr_ae
  refine ae_of_all _ fun t => ?_
  apply congrArg (t⁻¹ * ·)
  let x := Multiplicative.ofAdd (Real.log t)
  let f (l : L) := ‖Q.eval (↑|Real.log t| : ℂ) * v.val ((e.comp σ) x * l.val)‖ ^ p.toReal
  have hf : Continuous f := by
    unfold f
    apply Continuous.rpow_const _ (fun _ => Or.inr ENNReal.toReal_nonneg)
    exact (continuous_const.mul ((bruhatSchwartz_continuous v).comp
      (continuous_const.mul continuous_subtype_val))).norm
  change _ = ∫ l, f l ∂Measure.map j ν
  have hjm : AEMeasurable (j : K → L) ν := j.continuous.measurable.aemeasurable
  have hfm : AEStronglyMeasurable f (Measure.map (j : K → L) ν) := hf.aestronglyMeasurable
  rw [integral_map hjm hfm]
  apply integral_congr_ae
  refine ae_of_all ν fun k => ?_
  dsimp only [f]
  rw [huv, map_mul, hj]
  rfl

omit [BorelSpace G] in
/-- Rescaling the norm-one measure rescales the numerical seminorm by the
corresponding p-th root. -/
theorem bruhatSplitRadialNorm_smul_measure {K : Subgroup G}
    (τ : Multiplicative ℝ →ₜ* G) (ν : Measure K) (c : ℝ≥0∞)
    (p : ℝ≥0∞) (Q : Polynomial ℂ) (u : BruhatSchwartz G) :
    bruhatSplitRadialNorm τ (c • ν) p Q u =
      c.toReal ^ (1 / p.toReal) * bruhatSplitRadialNorm τ ν p Q u := by
  let A (t : ℝ) := ∫ k : K,
    ‖Q.eval (↑|Real.log t| : ℂ) * u.val (τ (Multiplicative.ofAdd (Real.log t)) * k.val)‖ ^
      p.toReal ∂ν
  have hA (t : ℝ) : 0 ≤ A t :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hi : 0 ≤ ∫ t in Ioi (0 : ℝ), t⁻¹ * A t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => mul_nonneg (inv_nonneg.mpr ht.le) (hA t)
  unfold bruhatSplitRadialNorm
  simp_rw [integral_smul_measure, smul_eq_mul]
  change ((∫ t in Ioi (0 : ℝ), t⁻¹ * (c.toReal * A t)) ^ (1 / p.toReal)) =
    c.toReal ^ (1 / p.toReal) * (∫ t in Ioi (0 : ℝ), t⁻¹ * A t) ^ (1 / p.toReal)
  simp_rw [mul_left_comm _ c.toReal]
  rw [integral_const_mul, Real.mul_rpow ENNReal.toReal_nonneg hi]

end
end Masullo
