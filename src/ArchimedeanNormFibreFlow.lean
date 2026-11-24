import ArchimedeanNormFibreAverage
import AdelicDerivatives

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped SchwartzMap NumberField Classical

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The archimedean component of the canonical idelic norm section. -/
def archNormRay (t : ℝ) : InfiniteIdeles F :=
  (Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom)
    (ideleExpSection F (Multiplicative.ofAdd t))

theorem archNormRay_continuous : Continuous (archNormRay F) :=
  (Continuous.units_map _ continuous_fst).comp ((ideleExpSection_continuous F).comp continuous_ofAdd)

theorem archNormRay_norm (t : ℝ) : ‖(archNormRay F t).val‖ = Real.exp t := by
  have h := ideleNorm_expSection F (Multiplicative.ofAdd t)
  change (∏ v : InfinitePlace F, ‖(ideleExpSection F (Multiplicative.ofAdd t)).val.1 v‖ ^ v.mult) *
    (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(ideleExpSection F (Multiplicative.ofAdd t)).val.2 v‖) =
      Real.exp t at h
  rw [(ideleExpSection_components F (Multiplicative.ofAdd t)).2] at h
  have he : (fun v : HeightOneSpectrum (𝓞 F) => ‖(1 : FiniteAdeleRing (𝓞 F) F) v‖) = fun _ => 1 := by
    funext v
    change ‖(1 : v.adicCompletion F)‖ = 1
    exact norm_one
  rw [he, finprod_one, mul_one] at h
  change ‖(ideleExpSection F (Multiplicative.ofAdd t)).val.1‖ = _
  rw [InfiniteAdeleRing.norm_def]
  exact h

/-- The logarithmic derivative along the norm section acts on Schwartz tests
by the scalar Euler vector field divided by the field degree. -/
def archNormRayEuler : 𝓢(mixedEmbedding.mixedSpace F, ℂ) →L[ℂ] 𝓢(mixedEmbedding.mixedSpace F, ℂ) :=
  schwartzLinearField ((Module.finrank ℚ F : ℝ)⁻¹ • ContinuousLinearMap.id ℝ (mixedEmbedding.mixedSpace F))

theorem archNormRay_test_hasDerivAt (f : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (a : InfiniteIdeles F) (t : ℝ) :
    HasDerivAt (fun u => f (InfiniteAdeleRing.ringEquiv_mixedSpace F (a * archNormRay F u).val))
      (archNormRayEuler F f (InfiniteAdeleRing.ringEquiv_mixedSpace F (a * archNormRay F t).val)) t := by
  let d := (Module.finrank ℚ F : ℝ)
  let x := InfiniteAdeleRing.ringEquiv_mixedSpace F a.val
  have he (u : ℝ) : InfiniteAdeleRing.ringEquiv_mixedSpace F (a * archNormRay F u).val =
      Real.exp (u / d) • x := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (a.val * (ideleExpSection F (Multiplicative.ofAdd u)).val.1) = _
    rw [mul_comm, map_mul, ideleExpSection_mixed, smul_mul_assoc, one_mul]
    rfl
  have hs : HasDerivAt (fun u : ℝ => Real.exp (u / d)) (d⁻¹ * Real.exp (t / d)) t := by
    simpa only [id_eq, one_div, mul_comm] using ((hasDerivAt_id t).div_const d).exp
  have hd := (f.hasFDerivAt (Real.exp (t / d) • x)).comp_hasDerivAt t (hs.smul_const x)
  simp only [he, archNormRayEuler, schwartzLinearField_apply]
  change HasDerivAt (fun u => f (Real.exp (u / d) • x))
    ((fderiv ℝ (fun y => f y) (Real.exp (t / d) • x)) (d⁻¹ • (Real.exp (t / d) • x))) t
  rw [smul_smul]
  exact hd

end
end Masullo
