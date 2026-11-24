import SchwartzBanachCoordinates
import HigherWeakDifferentiability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.HahnBanach

open Function Set Topology
open scoped SchwartzMap ContDiff

namespace Masullo
noncomputable section

variable {I Y X : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {p : SeminormFamily ℂ Y I}

/-- A continuous scalar functional factors through finitely many Banach coordinates. -/
theorem exists_localBanach_scalar_factorization (hp : WithSeminorms p) (l : Y →L[ℂ] ℂ) :
    ∃ s : Finset I, ∃ T : (∀ i : s, LocalBanach (p i.val)) →L[ℂ] ℂ,
      ∀ y, T (fun i => localBanachDenseMap (p i.val) y) = l y := by
  classical
  let q := (normSeminorm ℂ ℂ).comp l.toLinearMap
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hp q l.continuous.norm
  let P := ∀ i : s, LocalBanach (p i.val)
  let j : Y →ₗ[ℂ] P := LinearMap.pi (fun i => localBanachDenseMap (p i.val))
  have hbound (y : Y) : ‖l y‖ ≤ (C : ℝ) * ‖j y‖ := by
    refine (hC y).trans ?_
    change (C : ℝ) * s.sup p y ≤ (C : ℝ) * ‖j y‖
    refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) ?_) C.coe_nonneg
    intro i hi
    rw [← norm_localBanachDenseMap (p i) y]
    exact norm_le_pi_norm (j y) (⟨i, hi⟩ : s)
  have hk : j.ker ≤ l.toLinearMap.ker := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    exact norm_eq_zero.mp (le_antisymm (by simpa [hy] using hbound y) (norm_nonneg _))
  let L : j.range →ₗ[ℂ] ℂ :=
    (j.ker.liftQ l.toLinearMap hk).comp j.quotKerEquivRange.symm.toLinearMap
  have hL (y : Y) : L (j.rangeRestrict y) = l y := by
    have he : j.quotKerEquivRange (Submodule.Quotient.mk y) = j.rangeRestrict y := rfl
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, ← he,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply, ContinuousLinearMap.coe_coe]
  let Lc := L.mkContinuous C (fun z => by
    obtain ⟨y, rfl⟩ := j.surjective_rangeRestrict z
    rw [hL]
    exact hbound y)
  obtain ⟨T, hT, -⟩ := exists_extension_norm_eq j.range Lc
  exact ⟨s, T, fun y => (hT (j.rangeRestrict y)).trans (hL y)⟩

/-- Coordinatewise smoothness implies smoothness after applying any continuous scalar functional. -/
theorem localBanach_contDiff_scalar (hp : WithSeminorms p) (u : X → Y)
    (h : ∀ i, ContDiff ℝ ∞ (fun x => localBanachDenseMap (p i) (u x))) (l : Y →L[ℂ] ℂ) :
    ContDiff ℝ ∞ (fun x => l (u x)) := by
  obtain ⟨s, T, hT⟩ := exists_localBanach_scalar_factorization hp l
  have hc := (T.restrictScalars ℝ).contDiff.comp (contDiff_pi.mpr fun i : s => h i.val)
  exact (funext fun x => hT (u x)) ▸ hc

/-- The scalar tests of each such Schwartz map are ordinary scalar Schwartz maps. -/
theorem localBanach_schwartz_scalar (hp : WithSeminorms p) (u : X → Y)
    (h : ∀ i, ∃ f : 𝓢(X, LocalBanach (p i)), ∀ x, f x = localBanachDenseMap (p i) (u x))
    (l : Y →L[ℂ] ℂ) : ∃ f : 𝓢(X, ℂ), ∀ x, f x = l (u x) := by
  classical
  obtain ⟨s, T, hT⟩ := exists_localBanach_scalar_factorization hp l
  choose F hF using h
  let S (i : s) := ContinuousLinearMap.single ℂ (fun i : s => LocalBanach (p i.val)) i
  refine ⟨∑ i : s, (F i.val).postcompCLM (T.comp (S i)), fun x => ?_⟩
  simp only [sum_apply, SchwartzMap.postcompCLM_apply,
    ContinuousLinearMap.comp_apply, hF, ← map_sum]
  rw [← hT (u x)]
  congr 1
  ext i
  change (∑ j : s, Pi.single j (localBanachDenseMap (p j.val) (u x))) i = _
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    exact Pi.single_eq_of_ne hj.symm _
  · simp

/-- Smoothness in the local Banach coordinates implies the corrected
vector-valued smoothness of C.5.1.25 in real coordinates. -/
theorem localBanach_localVectorSmooth {I Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [Module ℝ Y] [IsScalarTower ℝ ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [T2Space Y] [ContinuousSMul ℂ Y] [PolynormableSpace ℂ Y] [QuasiCompleteSpace ℂ Y]
    {p : SeminormFamily ℂ Y I} (hp : WithSeminorms p) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin d) → Y)
    (h : ∀ i, ContDiff ℝ ∞ (fun x => localBanachDenseMap (p i) (u x))) :
    ∀ m : ℕ, LocalVectorContDiff m
      (fun x : Fin d → ℝ => u ((EuclideanSpace.equiv (Fin d) ℝ).symm x)) univ := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  apply (localVectorSmooth_iff_weak (𝕜 := ℝ) isOpen_univ (fun x => u (e x))).mpr
  intro l
  exact ((localBanach_contDiff_scalar hp u h l).comp e.contDiff).contDiffOn

end
end Masullo
