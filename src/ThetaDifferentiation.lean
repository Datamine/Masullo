import AdelicBounds
import AdelicDerivatives
import Mathlib.Analysis.Calculus.SmoothSeries

open Filter NumberField Set Topology
open scoped NumberField Classical

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

theorem algebraicBruhat_log_orbit_hasDerivAt
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (a : Adeles F) (r : ℝ) :
    HasDerivAt (fun t : ℝ => f.val ((γ (Multiplicative.ofAdd t)).val * a))
      ((algebraicBruhatDeriv F γ hγ f).val ((γ (Multiplicative.ofAdd r)).val * a)) r := by
  let b := (γ (Multiplicative.ofAdd r)).val * a
  have he : HasDerivAt Real.exp 1 0 := by simpa only [Real.exp_zero] using Real.hasDerivAt_exp 0
  have h1 := algebraicBruhatDeriv_hasDerivAt F γ hγ f b
  have h2 : HasDerivAt (fun t => f.val (positiveParameterOrbit F γ b t))
      ((algebraicBruhatDeriv F γ hγ f).val b) (Real.exp 0) := by
    simpa only [Real.exp_zero] using h1
  have h0 : HasDerivAt (fun s : ℝ => f.val ((γ (Multiplicative.ofAdd s)).val * b))
      ((algebraicBruhatDeriv F γ hγ f).val b) 0 := by
    simpa only [Function.comp_def, positiveParameterOrbit, Real.log_exp, one_smul] using h2.scomp 0 he
  have hs : HasDerivAt (fun s : ℝ => f.val ((γ (Multiplicative.ofAdd s)).val * b))
      ((algebraicBruhatDeriv F γ hγ f).val b) (r - r) := by simpa only [sub_self] using h0
  have hshift := hs.comp_sub_const r r
  have ht : (fun t : ℝ => f.val ((γ (Multiplicative.ofAdd t)).val * a)) =
      fun t : ℝ => f.val ((γ (Multiplicative.ofAdd (t - r))).val * b) := by
    funext t
    dsimp [b]
    rw [← mul_assoc, ← Units.val_mul, ← map_mul]
    change f.val ((γ (Multiplicative.ofAdd t)).val * a) =
      f.val ((γ (Multiplicative.ofAdd ((t - r) + r))).val * a)
    rw [sub_add_cancel]
  rw [ht]
  exact hshift

private theorem thetaSummand_hasDerivAt
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (g : Idele F) (ξ : Fˣ) (r : ℝ) :
    HasDerivAt (fun t => thetaSummand F f.val (γ (Multiplicative.ofAdd t) * g) ξ)
      (thetaSummand F (algebraicBruhatDeriv F γ hγ f).val (γ (Multiplicative.ofAdd r) * g) ξ) r := by
  let a := (principalIdele F ξ * g).val
  have h := algebraicBruhat_log_orbit_hasDerivAt F γ hγ f a r
  have he (t : ℝ) : (principalIdele F ξ * (γ (Multiplicative.ofAdd t) * g)).val =
      (γ (Multiplicative.ofAdd t)).val * a := by
    change (principalIdele F ξ).val * ((γ (Multiplicative.ofAdd t)).val * g.val) =
      (γ (Multiplicative.ofAdd t)).val * ((principalIdele F ξ).val * g.val)
    rw [mul_left_comm]
  simpa only [thetaSummand, he] using h

/-- The theta series can be differentiated term by term along every idelic one-parameter subgroup.
The derivative series has a summable bound on each compact parameter interval. -/
theorem thetaOnIdeles_log_orbit_hasDerivAt
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (g : Idele F) (r : ℝ) :
    HasDerivAt (fun t => thetaOnIdeles F f.val (γ (Multiplicative.ofAdd t) * g))
      (thetaOnIdeles F (algebraicBruhatDeriv F γ hγ f).val (γ (Multiplicative.ofAdd r) * g)) r := by
  let D := algebraicBruhatDeriv F γ hγ f
  let P (t : ℝ) : Idele F × Adeles F := (γ (Multiplicative.ofAdd t) * g, 0)
  have hc : Continuous P := (((hγ.comp continuous_ofAdd).mul continuous_const).prodMk continuous_const)
  let K := P '' Icc (r - 1) (r + 1)
  have hK : IsCompact K := isCompact_Icc.image hc
  obtain ⟨m, hm, hbound⟩ := bruhat_shiftedTheta_majorant D.property hK
  have hmem : r ∈ Ioo (r - 1) (r + 1) := ⟨by linarith, by linarith⟩
  have hs : Summable (fun ξ => thetaSummand F f.val (γ (Multiplicative.ofAdd r) * g) ξ) :=
    bruhat_theta_summable f.property _
  change HasDerivAt (fun t => ∑' ξ, thetaSummand F f.val (γ (Multiplicative.ofAdd t) * g) ξ)
    (∑' ξ, thetaSummand F D.val (γ (Multiplicative.ofAdd r) * g) ξ) r
  apply hasDerivAt_tsum_of_isPreconnected hm isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun ξ t _ => thetaSummand_hasDerivAt F γ hγ f g ξ t) ?_ hmem hs hmem
  intro ξ t ht
  have h := hbound ξ (P t) ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  simpa only [P, shiftedThetaSummand_zero] using h

/-- Lemma 2.2.4.3. The differentiated theta sum on the idele class group is
the continuous theta sum of the adelic directional derivative. -/
theorem adelicTheta_orbit_derivative (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) :
    Continuous (adelicTheta F (algebraicBruhatDeriv F γ hγ f).val) ∧
    ∀ q : IdeleClass F,
      HasDerivAt (fun t : ℝ => adelicTheta F f.val
        (ideleClassMap F (γ (Multiplicative.ofAdd (Real.log t))) * q))
        (adelicTheta F (algebraicBruhatDeriv F γ hγ f).val q) 1 := by
  refine ⟨adelicTheta_continuous F (bruhat_theta_continuous_and_invariant
    (algebraicBruhatDeriv F γ hγ f).property).1, ?_⟩
  intro q
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
  have h := thetaOnIdeles_log_orbit_hasDerivAt F γ hγ f g (Real.log 1)
  have hlog : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log (one_ne_zero (α := ℝ))
  have hh := h.scomp 1 hlog
  simpa only [Function.comp_def, Real.log_one, show Multiplicative.ofAdd (0 : ℝ) = 1 from rfl,
    map_one, one_mul, one_smul, ← map_mul, adelicTheta_mk] using hh

end

end Masullo
