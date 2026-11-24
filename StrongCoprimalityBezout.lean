module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec5
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec5

/-! Corollary 7.5.0.3, p. 379. Build in the archived original revision
`3897f9497d5cff426d6548150bb3c67bc96d87eb` with Lean 4.36.0. -/

open IsDedekindDomain NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

noncomputable section

variable {F : Type*} [Field F] [NumberField F]
  (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))

private theorem inverseEulerFactor_norm_le
    (v : HeightOneSpectrum (𝓞 F)) (a : ℝ) (z : ℂ) (hz : a ≤ z.re) :
    ‖(finiteHeckeEulerFactor χ v z)⁻¹‖ ≤ 1 + (v.asIdeal.absNorm : ℝ) ^ (-a) := by
  classical
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  unfold finiteHeckeEulerFactor
  split_ifs
  · rw [inv_inv]
    refine (norm_sub_le _ _).trans ?_
    simp only [norm_one, norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul]
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
    exact add_le_add_right (Real.rpow_le_rpow_of_exponent_le hq.le (neg_le_neg hz)) 1
  · simpa only [inv_one, norm_one, le_add_iff_nonneg_right] using
      Real.rpow_nonneg (zero_le_one.trans hq.le) (-a)

private theorem reciprocalEulerProduct_mul_mem
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : SchwartzBergman (univ : Set ℝ)) :
    (fun z ↦ reciprocalPartialHeckeEulerProduct χ S z * v.val z) ∈
      schwartzBergmanSubmodule univ := by
  classical
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, ?_, ?_⟩
  · exact (strongCoprimality_mem_differenceRange_iff_euler χ S).differentiableOn.mul v.property.2.1
  · intro a b hab hI N
    obtain ⟨C, hC⟩ := v.property.2.2 a b hab hI N
    let A := ∏ p ∈ S, (1 + (p.asIdeal.absNorm : ℝ) ^ (-a))
    have hA : 0 ≤ A := by dsimp [A]; positivity
    refine ⟨A * C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖z ^ N * (reciprocalPartialHeckeEulerProduct χ S z * v.val z)‖ ≤ A * C
    rw [mul_left_comm, norm_mul]
    have hE : ‖reciprocalPartialHeckeEulerProduct χ S z‖ ≤ A := by
      rw [reciprocalPartialHeckeEulerProduct, norm_prod]
      exact Finset.prod_le_prod₀ (fun p _ ↦ norm_nonneg _)
        (fun p _ ↦ inverseEulerFactor_norm_le χ p a z hz.1)
    exact mul_le_mul hE (hC ⟨z, hz, rfl⟩) (norm_nonneg _) hA

open Classical in
/-- The reciprocal Euler polynomial and the pole-cleared completed Hecke
function give the Bézout representation on the entire Schwartz–Bergman space.
The sign converts the two conventions for the pole polynomial. -/
public theorem strongCoprimality_bezout_direct
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : Function.RightInverse τ (ideleNorm F))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (φ : SchwartzBergman (univ : Set ℝ)) :
    let L := regularizedCompletedHeckeL χ τ hτ (continuedCompletedHeckeL χ)
      (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2
    let δ : ℕ := if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0
    ∃ (u : ℂ → ℂ) (v : SchwartzBergman (univ : Set ℝ)), Differentiable ℂ u ∧
      (fun s ↦ (-1 : ℂ) ^ δ * L.val s * u s) ∈ schwartzBergmanSubmodule univ ∧
      ∀ s, (-1 : ℂ) ^ δ * L.val s * u s + reciprocalPartialHeckeEulerProduct χ S s * v.val s =
        φ.val s := by
  classical
  intro L δ
  obtain ⟨v, u, hu, he⟩ := strongCoprimality_exists_sub_mem_product χ τ hτ S hS φ
  have hsign (s : ℂ) : (-1 : ℂ) ^ δ * L.val s * ((-1 : ℂ) ^ δ * u s) = L.val s * u s := by
    calc
      _ = ((-1 : ℂ) ^ δ * (-1 : ℂ) ^ δ) * (L.val s * u s) := by ring
      _ = _ := by rw [← mul_pow]; simp
  refine ⟨fun s ↦ (-1 : ℂ) ^ δ * u s, v, hu.const_mul _, ?_, ?_⟩
  · have hfun : (fun s ↦ (-1 : ℂ) ^ δ * L.val s * ((-1 : ℂ) ^ δ * u s)) =
        φ.val - (fun s ↦ reciprocalPartialHeckeEulerProduct χ S s * v.val s) := by
      funext s
      rw [hsign]
      change L.val s * u s = φ.val s - _
      exact eq_sub_of_add_eq (he s).symm
    rw [hfun]
    exact Submodule.sub_mem _ φ.property (reciprocalEulerProduct_mul_mem χ S v)
  · intro s
    rw [hsign]
    exact (he s).symm

#print axioms strongCoprimality_bezout_direct

end

end RiemannMasullo
