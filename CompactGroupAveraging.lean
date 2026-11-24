import PettisBounds
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Complex.Circle

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Masullo

noncomputable section

section CompactPettis

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] [IsUniformAddGroup E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E] in
private theorem dual_ext {u v : E} (h : ∀ ℓ : StrongDual ℂ E, ℓ u = ℓ v) : u = v := by
  apply (weakBidualEval_isEmbedding E).injective
  change (weakBidualEval E u : Module.Dual ℂ (StrongDual ℂ E)) =
    (weakBidualEval E v : Module.Dual ℂ (StrongDual ℂ E))
  exact DFunLike.ext (F := Module.Dual ℂ (StrongDual ℂ E)) _ _ h

omit [TopologicalSpace X] [BorelSpace X] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [IsUniformAddGroup E] [LocallyConvexSpace ℝ E] [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E] in
theorem positivePettis_integral_unique {ν : Measure X} {f : X → E} {u v : E}
    (hu : HasPositivePettisIntegral ν f u) (hv : HasPositivePettisIntegral ν f v) : u = v :=
  dual_ext fun ℓ => (hu ℓ).2.trans (hv ℓ).2.symm

variable (ν : Measure X) [IsFiniteMeasure ν]

private def positiveComplexMeasure : VectorMeasure X ℂ :=
  ν.withDensityᵥ (fun _ => (1 : ℂ))

omit [TopologicalSpace X] [BorelSpace X] in
private theorem positiveComplexMeasure_variation : (positiveComplexMeasure ν).variation = ν := by
  rw [positiveComplexMeasure, Measure.variation_withDensityᵥ (integrable_const _)]
  simp

private instance : IsFiniteMeasure (positiveComplexMeasure ν).variation := by
  rw [positiveComplexMeasure_variation]
  infer_instance

omit [PolynormableSpace ℂ E] in
/-- A continuous compactly supported map into a quasi-complete locally convex space
has a Pettis integral for every measure finite on compact sets. -/
theorem exists_positivePettisIntegral_of_hasCompactSupport
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → E}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ u, HasPositivePettisIntegral μ f u := by
  let K := tsupport f
  have hK : MeasurableSet K := isClosed_tsupport f |>.measurableSet
  let ν := μ.restrict K
  letI : IsFiniteMeasure ν := ⟨by
    change μ.restrict K univ < ∞
    simpa [Measure.restrict_apply MeasurableSet.univ] using hc.measure_lt_top (μ := μ)⟩
  obtain ⟨u, _, hu⟩ := pettis_exists_of_hasCompactSupport (positiveComplexMeasure ν) hf hc
  refine ⟨u, fun ℓ ↦ ⟨?_, ?_⟩⟩
  · exact (ℓ.continuous.comp hf).integrable_of_hasCompactSupport (hc.comp_left ℓ.map_zero)
  · have hcont : Continuous (ℓ ∘ f) := ℓ.continuous.comp hf
    have hi : Integrable (ℓ ∘ f) ν :=
      hcont.integrable_of_hasCompactSupport (hc.comp_left ℓ.map_zero)
    have h := (hu ℓ).2
    rw [positiveComplexMeasure, complexMeasureIntegral_withDensity ν (integrable_const _)
      (fun _ ↦ by simp) hcont.measurable hi] at h
    simp only [mul_one] at h
    change ℓ u = ∫ x in K, (ℓ ∘ f) x ∂μ at h
    rw [← integral_indicator hK] at h
    have hind : K.indicator (ℓ ∘ f) = ℓ ∘ f := by
      funext x
      by_cases hx : x ∈ K
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx, Function.comp_apply, image_eq_zero_of_notMem_tsupport hx, map_zero]
    rwa [hind] at h

variable [CompactSpace X]

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] [IsUniformAddGroup E] [T2Space E]
  [LocallyConvexSpace ℝ E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
private theorem positiveComplexMeasure_pettis_iff {f : X → E} (hf : Continuous f) (u : E) :
    HasPettisIntegral (positiveComplexMeasure ν) f u ↔ HasPositivePettisIntegral ν f u := by
  unfold HasPettisIntegral HasPositivePettisIntegral
  apply forall_congr'
  intro ℓ
  have hc : Continuous (ℓ ∘ f) := ℓ.continuous.comp hf
  have hI : Integrable (ℓ ∘ f) ν := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [show (positiveComplexMeasure ν).Integrable (ℓ ∘ f) ↔ Integrable (ℓ ∘ f) ν by
      change Integrable _ (positiveComplexMeasure ν).variation ↔ _
      rw [positiveComplexMeasure_variation]]
  rw [positiveComplexMeasure, complexMeasureIntegral_withDensity ν (integrable_const _)
    (fun _ => by simp) hc.measurable hI]
  simp only [mul_one, Function.comp_apply]

omit [PolynormableSpace ℂ E] in
private theorem compactPettis_exists (f : X → E) (hf : Continuous f) :
    ∃ u ∈ (positiveComplexMeasure ν).variation.real (tsupport f) •
      closure (complexAbsConvexHull (range f)), HasPositivePettisIntegral ν f u := by
  obtain ⟨u, hu, h⟩ := pettis_exists_of_hasCompactSupport (positiveComplexMeasure ν)
    hf (HasCompactSupport.of_compactSpace _)
  exact ⟨u, hu, (positiveComplexMeasure_pettis_iff ν hf u).mp h⟩

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] [T2Space E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E] in
private theorem compactPettis_continuous (f : X × E → E) (hf : Continuous f) (F : E → E)
    (hF : ∀ u, HasPositivePettisIntegral ν (fun x => f (x, u)) (F u)) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro u
  have hC (v : E) : Continuous (fun x : X => f (x, v)) :=
    hf.comp (continuous_id.prodMk continuous_const)
  apply pettis_tendsto_of_uniform (positiveComplexMeasure ν)
    (fun v => (positiveComplexMeasure_pettis_iff ν (hC v) _).mpr (hF v))
    ((positiveComplexMeasure_pettis_iff ν (hC u) _).mpr (hF u))
  intro p hp δ hδ
  let W : Set (X × E) := {z | p (f z - f (z.1, u)) < δ}
  have hW : IsOpen W := isOpen_lt
    (hp.comp (hf.sub (hf.comp (continuous_fst.prodMk continuous_const)))) continuous_const
  have he : (univ : Set X) ×ˢ ({u} : Set E) ⊆ W := by
    intro z hz
    have hz' : z.2 = u := hz.2
    change p (f z - f (z.1, u)) < δ
    rw [← hz', Prod.mk.eta, sub_self, map_zero]
    exact hδ
  obtain ⟨U, V, hU, hV, hX, hu, hW'⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hW he
  filter_upwards [hV.mem_nhds (hu (mem_singleton u))] with v hv
  intro x
  exact hW' ⟨hX (mem_univ x), hv⟩

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E] in
/-- Represented integrals of individual orbits assemble into a continuous
linear average when the family is jointly continuous on the compact parameter space. -/
theorem compactPettis_clm_of_exists (ρ : X → E →L[ℂ] E)
    (hρ : Continuous (fun z : X × E => ρ z.1 z.2))
    (hInt : ∀ u, ∃ v, HasPositivePettisIntegral ν (fun x => ρ x u) v) :
    ∃ F : E →L[ℂ] E, ∀ u, HasPositivePettisIntegral ν (fun x => ρ x u) (F u) := by
  choose F hInt using hInt
  refine ⟨⟨{ toFun := F, map_add' := ?_, map_smul' := ?_ },
    compactPettis_continuous ν _ hρ F hInt⟩, hInt⟩
  · intro u v
    apply dual_ext
    intro ℓ
    rw [(hInt (u + v) ℓ).2, map_add, (hInt u ℓ).2, (hInt v ℓ).2]
    have hi := integral_add (hInt u ℓ).1 (hInt v ℓ).1
    simp only [Function.comp_apply] at hi
    rw [← hi]
    congr 1
    ext x
    simp
  · intro c u
    apply dual_ext
    intro ℓ
    rw [(hInt (c • u) ℓ).2, map_smul, (hInt u ℓ).2, ← integral_smul]
    congr 1
    ext x
    simp

/-- A jointly continuous family of linear maps on a compact space admits a continuous Pettis average. -/
theorem compactPettis_clm_exists (ρ : X → E →L[ℂ] E)
    (hρ : Continuous (fun z : X × E => ρ z.1 z.2)) :
    ∃ F : E →L[ℂ] E, ∀ u, HasPositivePettisIntegral ν (fun x => ρ x u) (F u) :=
  compactPettis_clm_of_exists ν ρ hρ fun u ↦ by
    obtain ⟨v, _, hv⟩ := compactPettis_exists ν (fun x ↦ ρ x u)
      (hρ.comp (continuous_id.prodMk continuous_const))
    exact ⟨v, hv⟩

private theorem compactPettis_mem_closedSubmodule {f : X → E} (hf : Continuous f)
    (M : Submodule ℂ E) (hM : IsClosed (M : Set E)) (hm : MapsTo f univ M)
    {u : E} (hu : HasPositivePettisIntegral ν f u) : u ∈ M := by
  obtain ⟨v, hv, hν⟩ := compactPettis_exists ν f hf
  have hEq : v = u := dual_ext fun ℓ => (hν ℓ).2.trans (hu ℓ).2.symm
  subst v
  have hbal : Balanced ℂ (M : Set E) := by
    rintro c _ _ ⟨y, hy, rfl⟩
    exact M.smul_mem c hy
  have hsub : complexAbsConvexHull (range f) ⊆ M :=
    complexAbsConvexHull_min (range_subset_iff.mpr (fun x => hm (mem_univ x)))
      M.zero_mem hbal (M.restrictScalars ℝ).convex
  have hcl : closure (complexAbsConvexHull (range f)) ⊆ M := closure_minimal hsub hM
  obtain ⟨v, hv, rfl⟩ := hv
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact (M.restrictScalars ℝ).smul_mem _ (hcl hv)

end CompactPettis

section GroupAverage

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]

/-- The vectors fixed by a continuous linear action. -/
def fixedSubmodule (ρ : G →* (E →L[ℂ] E)) : Submodule ℂ E where
  carrier := {u | ∀ g, ρ g u = u}
  zero_mem' g := map_zero (ρ g)
  add_mem' {u v} hu hv g := by rw [map_add, hu g, hv g]
  smul_mem' c u hu g := by rw [map_smul, hu g]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] [Module ℝ E] [IsScalarTower ℝ ℂ E] [LocallyConvexSpace ℝ E] [ContinuousSMul ℂ E]
  [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
theorem fixedSubmodule_isClosed (ρ : G →* (E →L[ℂ] E)) :
    IsClosed (fixedSubmodule ρ : Set E) := by
  change IsClosed {u | ∀ g, ρ g u = u}
  rw [ofPred_forall]
  exact isClosed_iInter fun g => isClosed_eq (ρ g).continuous continuous_id

/-- The span of the differences defining the coinvariants of an action. -/
def actionDifferenceSpan (ρ : G →* (E →L[ℂ] E)) : Submodule ℂ E :=
  Submodule.span ℂ (range fun p : G × E => p.2 - ρ p.1 p.2)

omit [T2Space G] in
private theorem compactGroupAverage_clauses (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun z : G × E => ρ z.1 z.2))
    (ν : Measure G) [ν.IsHaarMeasure] :
    ∃ Φ : E →L[ℂ] E,
      (∀ u, HasPositivePettisIntegral ν (fun g => ρ g u) (Φ u)) ∧
      (∀ u, Φ u ∈ fixedSubmodule ρ) ∧
      (∀ u ∈ fixedSubmodule ρ, Φ u = (ν.real univ : ℂ) • u) ∧
      (∀ u g, Φ (ρ g u) = Φ u) ∧
      Φ.ker = (actionDifferenceSpan ρ).topologicalClosure := by
  obtain ⟨Φ, hΦ⟩ := compactPettis_clm_exists ν ρ hρ
  have hρmul (g h : G) (u : E) : ρ (g * h) u = ρ g (ρ h u) := by rw [map_mul]; rfl
  have hFix (u : E) : Φ u ∈ fixedSubmodule ρ := by
    intro g
    apply dual_ext
    intro ℓ
    have hL := (hΦ u (ℓ.comp (ρ g))).2
    change ℓ (ρ g (Φ u)) = ∫ h, ℓ (ρ g (ρ h u)) ∂ν at hL
    rw [hL, (hΦ u ℓ).2]
    simp_rw [← hρmul]
    exact integral_mul_left_eq_self (μ := ν) (fun h => ℓ (ρ h u)) g
  have hSc (u : E) (hu : u ∈ fixedSubmodule ρ) : Φ u = (ν.real univ : ℂ) • u := by
    apply dual_ext
    intro ℓ
    rw [(hΦ u ℓ).2, map_smul]
    have hpoint (g : G) : ρ g u = u := hu g
    simp only [hpoint, integral_const, Complex.real_smul, smul_eq_mul]
  have hInv (u : E) (g : G) : Φ (ρ g u) = Φ u := by
    apply dual_ext
    intro ℓ
    rw [(hΦ (ρ g u) ℓ).2, (hΦ u ℓ).2]
    simp_rw [← hρmul, mul_comm _ g]
    exact integral_mul_left_eq_self (μ := ν) (fun h => ℓ (ρ h u)) g
  refine ⟨Φ, hΦ, hFix, hSc, hInv, le_antisymm ?_ ?_⟩
  · intro u hu
    let M := (actionDifferenceSpan ρ).topologicalClosure
    let f := fun g : G => u - ρ g u
    have hf : Continuous f := continuous_const.sub (hρ.comp (continuous_id.prodMk continuous_const))
    have hm : MapsTo f univ M := fun g _ => Submodule.le_topologicalClosure _ <|
      Submodule.subset_span (mem_range_self (g, u))
    have hI : HasPositivePettisIntegral ν f ((ν.real univ : ℂ) • u) := by
      intro ℓ
      have hi : Integrable (fun _ : G => ℓ u) ν := integrable_const _
      have hj := (hΦ u ℓ).1
      have hcomp : ℓ ∘ f = (fun _ : G => ℓ u) - (ℓ ∘ (fun g : G => ρ g u)) := by
        funext g
        exact map_sub ℓ _ _
      refine ⟨hcomp.symm ▸ hi.sub hj, ?_⟩
      have hν : Φ u = 0 := hu
      have he := (hΦ u ℓ).2
      rw [hν, map_zero] at he
      change ℓ ((ν.real univ : ℂ) • u) = ∫ g, (ℓ ∘ f) g ∂ν
      rw [hcomp]
      change ℓ ((ν.real univ : ℂ) • u) = ∫ g, ℓ u - ℓ (ρ g u) ∂ν
      have hEq := integral_sub hi hj
      simp only [Function.comp_apply] at hEq
      rw [hEq, ← he, sub_zero, integral_const, map_smul, Complex.real_smul, smul_eq_mul]
    have huM := compactPettis_mem_closedSubmodule ν hf M
      (Submodule.isClosed_topologicalClosure _) hm hI
    have hmass : (ν.real univ : ℂ) ≠ 0 := by
      have hp := MeasureTheory.Measure.measure_pos_of_nonempty_interior (s := (univ : Set G)) ν
        (by simp)
      exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)).ne'
    have hh := M.smul_mem ((ν.real univ : ℂ)⁻¹) huM
    rwa [smul_smul, inv_mul_cancel₀ hmass, one_smul] at hh
  · refine Submodule.topologicalClosure_minimal (actionDifferenceSpan ρ) ?_ Φ.isClosed_ker
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,u⟩, rfl⟩
    change Φ (u - ρ g u) = 0
    rw [map_sub, hInv, sub_self]

omit [IsTopologicalGroup G] [T2Space G] [BorelSpace G] in
private theorem haarMass_ne_zero (ν : Measure G) [ν.IsHaarMeasure] :
    (ν.real univ : ℂ) ≠ 0 := by
  have hp := MeasureTheory.Measure.measure_pos_of_nonempty_interior (s := (univ : Set G)) ν
    (by simp)
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)).ne'

private def normAverageEquiv (ρ : G →* (E →L[ℂ] E)) (Φ : E →L[ℂ] E) (c : ℂ)
    (hc : c ≠ 0) (hFix : ∀ u, Φ u ∈ fixedSubmodule ρ)
    (hSc : ∀ u ∈ fixedSubmodule ρ, Φ u = c • u) :
    (E ⧸ Φ.ker) ≃L[ℂ] fixedSubmodule ρ := by
  let U := fixedSubmodule ρ
  let F := Φ.ker.liftQL (Φ.codRestrict U hFix) (fun x hx => Subtype.ext hx)
  let R : U →L[ℂ] (E ⧸ Φ.ker) := c⁻¹ • (Φ.ker.mkQL.comp U.subtypeL)
  have hcalc (u : E) : F (Φ.ker.mkQ u) = ⟨Φ u, hFix u⟩ := rfl
  have hCL (q : E ⧸ Φ.ker) : R (F q) = q := by
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective Φ.ker q
    change R (F (Φ.ker.mkQ u)) = Φ.ker.mkQ u
    rw [hcalc]
    change c⁻¹ • Φ.ker.mkQ (Φ u) = Φ.ker.mkQ u
    rw [← map_smul]
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero Φ.ker).mpr (by
      change Φ (c⁻¹ • Φ u - u) = 0
      rw [map_sub, map_smul, hSc (Φ u) (hFix u), smul_smul, inv_mul_cancel₀ hc, one_smul, sub_self])
  have hRC (v : U) : F (R v) = v := by
    apply Subtype.ext
    change (F (c⁻¹ • Φ.ker.mkQ v.val)).val = v.val
    rw [map_smul, hcalc]
    change c⁻¹ • Φ v.val = v.val
    rw [hSc v.val v.property, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact { toLinearEquiv := { F.toLinearMap with
                           invFun := R
                           left_inv := hCL
                           right_inv := hRC }
          continuous_toFun := F.continuous
          continuous_invFun := R.continuous }

omit [T2Space G] in
/-- Lemma 4.3.3.1. Compact Haar averaging of a jointly continuous linear
action gives the norm isomorphism from coinvariants to fixed vectors. -/
theorem compactGroupAverage (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun z : G × E => ρ z.1 z.2))
    (ν : Measure G) [ν.IsHaarMeasure] :
    ∃ Φ : E →L[ℂ] E,
      (∀ u, HasPositivePettisIntegral ν (fun g => ρ g u) (Φ u)) ∧
      range Φ = fixedSubmodule ρ ∧ IsClosed (fixedSubmodule ρ : Set E) ∧
      (∀ u, let P := (ν.real univ : ℂ)⁻¹ • Φ; P (P u) = P u) ∧
      (∃ e : (E ⧸ Φ.ker) ≃L[ℂ] fixedSubmodule ρ, ∀ u, (e (Φ.ker.mkQ u) : E) = Φ u) ∧
      Φ.ker = (actionDifferenceSpan ρ).topologicalClosure := by
  obtain ⟨Φ, hΦ, hFix, hSc, _, hKer⟩ := compactGroupAverage_clauses ρ hρ ν
  let c : ℂ := ν.real univ
  have hc : c ≠ 0 := haarMass_ne_zero ν
  refine ⟨Φ, hΦ, ?_, fixedSubmodule_isClosed ρ, ?_,
    ⟨normAverageEquiv ρ Φ c hc hFix hSc, fun _ => rfl⟩, hKer⟩
  · ext u
    constructor
    · rintro ⟨v, rfl⟩
      exact hFix v
    · intro hu
      exact ⟨c⁻¹ • u, by rw [map_smul, hSc u hu, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  · intro u
    change c⁻¹ • Φ (c⁻¹ • Φ u) = c⁻¹ • Φ u
    rw [map_smul, hSc (Φ u) (hFix u), smul_smul c⁻¹ c, inv_mul_cancel₀ hc, one_smul]

/-- Twisting a linear action by the inverse of a circle character. -/
def twistedCircleAction (ω : G →* Circle) (ρ : G →* (E →L[ℂ] E)) :
    G →* (E →L[ℂ] E) where
  toFun g := ((ω g)⁻¹ : Circle) • ρ g
  map_one' := by simp
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    intro u
    change (((ω (g * h))⁻¹ : Circle) : ℂ) • ρ (g * h) u =
      (((ω g)⁻¹ : Circle) : ℂ) • (ρ g ((((ω h)⁻¹ : Circle) : ℂ) • ρ h u))
    rw [map_mul ω, mul_inv_rev, Circle.coe_mul, map_mul ρ]
    change ((((ω h)⁻¹ : Circle) : ℂ) * (((ω g)⁻¹ : Circle) : ℂ)) • ρ g (ρ h u) =
      (((ω g)⁻¹ : Circle) : ℂ) • (ρ g ((((ω h)⁻¹ : Circle) : ℂ) • ρ h u))
    rw [map_smul, smul_smul, mul_comm]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] [Module ℝ E] [IsScalarTower ℝ ℂ E] [T2Space E] [LocallyConvexSpace ℝ E]
  [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
theorem mem_circleIsotype_iff (ω : G →* Circle) (ρ : G →* (E →L[ℂ] E)) (u : E) :
    u ∈ fixedSubmodule (twistedCircleAction ω ρ) ↔ ∀ g, ρ g u = (ω g : ℂ) • u := by
  constructor
  · intro hu g
    have h : (((ω g)⁻¹ : Circle) : ℂ) • ρ g u = u := hu g
    have h' := congrArg ((ω g : ℂ) • ·) h
    rw [smul_smul, Circle.coe_inv, mul_inv_cancel₀ (ω g).coe_ne_zero, one_smul] at h'
    exact h'
  · intro hu g
    change (((ω g)⁻¹ : Circle) : ℂ) • ρ g u = u
    rw [hu, smul_smul, Circle.coe_inv, inv_mul_cancel₀ (ω g).coe_ne_zero, one_smul]

omit [T2Space G] in
/-- Corollary 4.3.3.3. Haar averaging with the inverse character identifies
the quotient with the isotypic subspace and gives its normalized projection. -/
theorem compactGroupIsotypicAverage (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous (fun z : G × E => ρ z.1 z.2))
    (ω : G →* Circle) (hω : Continuous ω) (ν : Measure G) [ν.IsHaarMeasure] :
    let U := fixedSubmodule (twistedCircleAction ω ρ)
    (∀ u, u ∈ U ↔ ∀ g, ρ g u = (ω g : ℂ) • u) ∧
    ∃ Φ : E →L[ℂ] E,
      (∀ u, HasPositivePettisIntegral ν
        (fun g => (((ω g)⁻¹ : Circle) : ℂ) • ρ g u) (Φ u)) ∧
      range Φ = U ∧ IsClosed (U : Set E) ∧
      (∀ u, let P := (ν.real univ : ℂ)⁻¹ • Φ; P (P u) = P u) ∧
      (∃ e : (E ⧸ Φ.ker) ≃L[ℂ] U, ∀ u, (e (Φ.ker.mkQ u) : E) = Φ u) ∧
      Φ.ker = (actionDifferenceSpan (twistedCircleAction ω ρ)).topologicalClosure := by
  have hω' : Continuous (fun g : G => (((ω g)⁻¹ : Circle) : ℂ)) :=
    continuous_subtype_val.comp hω.inv
  have hA : Continuous (fun z : G × E => twistedCircleAction ω ρ z.1 z.2) :=
    (hω'.comp continuous_fst).smul hρ
  exact ⟨mem_circleIsotype_iff ω ρ, compactGroupAverage (twistedCircleAction ω ρ) hA ν⟩

end GroupAverage

end

end Masullo
