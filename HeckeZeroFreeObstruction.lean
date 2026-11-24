import FiniteHeckeZeroFree
import HeckeIdealAsymptotics

open Filter Function NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- A nonzero imaginary character height rules out a quadratic character. -/
theorem heckeHeight_sq_ne_one {χ : PontryaginDual (IdeleClass F)} {t : ℝ}
    (ht : HasHeckeHeight F χ t) (hne : t ≠ 0) : χ ^ 2 ≠ 1 := by
  intro h
  have hi : χ⁻¹ = χ := calc
    _ = χ⁻¹ * χ ^ 2 := by rw [h, mul_one]
    _ = χ := by rw [pow_two, ← mul_assoc, inv_mul_cancel, one_mul]
  have h' := HasHeckeHeight.inv F ht
  rw [hi] at h'
  obtain ⟨u, _, hu⟩ := existsUnique_heckeHeight F χ
  exact hne (by linarith [hu t ht, hu (-t) h'])

/-- The norm character of frequency `y` is trivial on norm one and has
height `-y` in the manuscript's spectral convention. -/
theorem ideleNormCircle_heckeHeight (y : ℝ) :
    heckeNormOneRestriction F (ideleNormCircle F y) = 1 ∧
      HasHeckeHeight F (ideleNormCircle F y) (-y) := by
  have h : heckeNormOneRestriction F (ideleNormCircle F y) = 1 := by
    apply DFunLike.ext
    intro g
    change Circle.exp (y * Real.log (ideleClassNorm F g.val)) = 1
    have hg : ideleClassNorm F g.val = 1 := g.property
    rw [hg, Real.log_one, mul_zero, Circle.exp_zero]
  refine ⟨h, fun g ↦ ?_⟩
  change ((Circle.exp (y * Real.log (ideleClassNorm F g)) : Circle) : ℂ) =
    (normOneEulerCharacter F (heckeNormOneRestriction F (ideleNormCircle F y)) g : ℂ) *
      Complex.exp (-(((-y : ℝ) : ℂ) * Complex.I) * (Real.log (ideleClassNorm F g) : ℂ))
  rw [h, show normOneEulerCharacter F 1 g = 1 from rfl, Circle.coe_one, one_mul, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- A nonreal zero of the canonical trivial finite continuation becomes a
real zero of a nonquadratic norm twist, at the same real part and with
the same order. This is the obstruction to the printed real-zero clause
of B.6.1.1 over the entire interval from one-half to one. -/
theorem finiteHecke_real_zero_of_nonreal_trivial_zero {Z : ℂ → ℂ}
    (hZ : MeromorphicOn Z univ) (he : EqOn Z (globalFiniteHeckeEuler F 1) {z | 1 < z.re})
    {x y : ℝ} (hy : y ≠ 0) (hz : 0 < meromorphicOrderAt Z ⟨x, y⟩) :
    ∃ (χ : PontryaginDual (IdeleClass F)) (L : ℂ → ℂ), χ ^ 2 ≠ 1 ∧
      MeromorphicOn L univ ∧ EqOn L (manuscriptFiniteHeckeEuler F χ) {z | 1 < z.re} ∧
      meromorphicOrderAt L (x : ℂ) = meromorphicOrderAt Z ⟨x, y⟩ ∧
      0 < meromorphicOrderAt L (x : ℂ) := by
  let χ := ideleNormCircle F y
  obtain ⟨hr, ht⟩ := ideleNormCircle_heckeHeight F y
  let q (z : ℂ) := z - (((-y : ℝ) : ℂ) * Complex.I)
  have hq (z : ℂ) : AnalyticAt ℂ q z := analyticAt_id.sub analyticAt_const
  have hRe (z : ℂ) : (q z).re = z.re := by simp [q, Complex.mul_re]
  have hqₓ : q (x : ℂ) = ⟨x, y⟩ := by
    apply Complex.ext <;> simp [q, Complex.mul_re, Complex.mul_im]
  have hOrder : meromorphicOrderAt (Z ∘ q) (x : ℂ) = meromorphicOrderAt Z ⟨x, y⟩ := by
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (hq _) (by simp [q]), hqₓ]
  refine ⟨χ, Z ∘ q, heckeHeight_sq_ne_one F ht (neg_ne_zero.mpr hy),
    fun z _ ↦ (hZ (q z) (mem_univ _)).comp_analyticAt (g := q) (hq z), ?_, hOrder, hOrder ▸ hz⟩
  intro z h
  rw [show χ = ideleNormCircle F y from rfl, manuscriptFiniteHeckeEuler_shift F _ ht, hr]
  exact he (show 1 < (q z).re by rwa [hRe])

end

end Masullo
