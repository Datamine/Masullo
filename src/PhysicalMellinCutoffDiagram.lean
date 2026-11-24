import ModulatedSobolevGroupProfiles
import ModulatedSobolevSequence

open Filter Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal TensorProduct

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
  (ν : Measure m.toMonoidHom.ker) [IsFiniteMeasure ν]

local notation "K" => m.toMonoidHom.ker

omit [MeasurableSpace G] [BorelSpace G] in
private theorem logSplit_log (p : ℝ × K) :
    modulatedLog m (modulatedLogSplit m τ hτ p) = p.1 := by
  change (m (τ (Multiplicative.ofAdd p.1) * p.2.val)).toAdd = p.1
  rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one]
  rfl

set_option maxHeartbeats 1500000 in
/-- Transport the exact diagram to the source spaces on physical weighted
Haar measure. The right-hand arrow is the closed-ray multiplier. -/
theorem modulatedPhysicalMellinCutoffDiagram (b : ℝ) (N : ℕ) (c : ℝ) (hc : c ≤ 0) :
    let s : ℝ := 2 * (N : ℝ)
    let W := modulatedSobolevMeasure m τ hτ ν b s
    let L := modulatedGroupCutoff m τ hτ ν b s (Ioo c 0)
    let M := modulatedGroupCutoff m τ hτ ν b s (Ioi c)
    let R := modulatedGroupCutoff m τ hτ ν b s (Ioi 0)
    let L' := Completion (Lp ℂ 2 ν ⊗[ℂ] supportedMellinLineCompletion b N (Ioo c 0))
    let M' := Completion (Lp ℂ 2 ν ⊗[ℂ] supportedMellinLineCompletion b N (Ioi c))
    let R' := Completion (Lp ℂ 2 ν ⊗[ℂ] supportedMellinLineCompletion b N (Ioi 0))
    ∃ (i : L →L[ℂ] M) (p : M →L[ℂ] R) (i' : L' →L[ℂ] M') (p' : M' →L[ℂ] R'),
      (∀ f, (i f).val = f.val) ∧
      (∀ f, ((p f).val : G → ℂ) =ᵐ[W]
        (modulatedLog m ⁻¹' Ici 0).indicator (f.val : G → ℂ)) ∧
      (∀ f, modulatedGroupMellinEquiv m τ hτ ν b N isOpen_Ioi (i f) =
        i' (modulatedGroupMellinEquiv m τ hτ ν b N isOpen_Ioo f)) ∧
      (∀ f, modulatedGroupMellinEquiv m τ hτ ν b N isOpen_Ioi (p f) =
        p' (modulatedGroupMellinEquiv m τ hτ ν b N isOpen_Ioi f)) ∧
      (Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p) ∧
      (Injective i' ∧ IsClosed (range i') ∧ Exact i' p' ∧ Surjective p' ∧ IsOpenMap p') := by
  intro s W L M R L' M' R'
  obtain ⟨j, q, i', p', hj, hq, hcommL, hcommR, hleft, hrest⟩ :=
    modulatedSobolev_mellinCutoffDiagram ν b N c hc
  have hR : Injective i' ∧ IsClosed (range i') ∧ Exact i' p' ∧ Surjective p' ∧ IsOpenMap p' :=
    hrest.1
  obtain ⟨hinj, hclosed, hex, hsurj, hopen⟩ := hleft
  let eL := (modulatedGroupCutoffEquiv m τ hτ ν b s (Ioo c 0)).toContinuousLinearEquiv
  let eM := (modulatedGroupCutoffEquiv m τ hτ ν b s (Ioi c)).toContinuousLinearEquiv
  let eR := (modulatedGroupCutoffEquiv m τ hτ ν b s (Ioi 0)).toContinuousLinearEquiv
  let i : L →L[ℂ] M := eM.symm.toContinuousLinearMap.comp (j.comp eL.toContinuousLinearMap)
  let p : M →L[ℂ] R := eR.symm.toContinuousLinearMap.comp (q.comp eM.toContinuousLinearMap)
  have hi (f : L) : eM (i f) = j (eL f) := eM.apply_symm_apply _
  have hp (f : M) : eR (p f) = q (eM f) := eR.apply_symm_apply _
  let J := modulatedSobolevGroupEquiv m τ hτ ν b s
  refine ⟨i, p, i', p', ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, hR⟩
  · intro f
    apply J.injective
    exact (congrArg Subtype.val (hi f)).trans (hj _)
  · intro f
    let e := modulatedLogSplit m τ hτ
    let er := stripMeasure b b s
    have hMP : MeasurePreserving e (er.prod ν) W := ⟨e.continuous.measurable, rfl⟩
    have hAE : ∀ᵐ t ∂ν.prod er, (p f).val (e (t.2, t.1)) =
        (modulatedLog m ⁻¹' Ici 0).indicator (f.val : G → ℂ) (e (t.2, t.1)) := by
      filter_upwards [modulatedSobolevGroupEquiv_ae m τ hτ ν b s (p f).val,
        modulatedSobolevGroupEquiv_ae m τ hτ ν b s f.val, hq (eM f)] with t ht hf hq'
      have hh : J (p f).val t = (q (eM f)).val t :=
        congrArg (fun u ↦ u.val t) (hp f)
      change J (p f).val t = (p f).val (e (t.2, t.1)) at ht
      change J f.val t = f.val (e (t.2, t.1)) at hf
      rw [← ht, hh, hq']
      have hcoord : modulatedLog m (e (t.2, t.1)) = t.2 := logSplit_log m τ hτ (t.2, t.1)
      have hmem : e (t.2, t.1) ∈ modulatedLog m ⁻¹' Ici 0 ↔ t.2 ∈ Ici (0 : ℝ) := by
        change modulatedLog m (e (t.2, t.1)) ∈ Ici 0 ↔ _
        rw [hcoord]
      by_cases h : t.2 ∈ Ici (0 : ℝ)
      · rw [indicator_of_mem (show t ∈ Prod.snd ⁻¹' Ici (0 : ℝ) from h),
          indicator_of_mem (hmem.mpr h)]
        exact hf
      · rw [indicator_of_notMem (show t ∉ Prod.snd ⁻¹' Ici (0 : ℝ) from h),
          indicator_of_notMem (fun ht' ↦ h (hmem.mp ht'))]
    have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hAE
    filter_upwards [(hMP.symm e.toMeasurableEquiv).quasiMeasurePreserving.ae hswap] with g hg
    change (p f).val (e (e.symm g)) =
      (modulatedLog m ⁻¹' Ici 0).indicator (f.val : G → ℂ) (e (e.symm g)) at hg
    simpa only [e.apply_symm_apply] using hg
  · intro f
    change modulatedSupportedMellinEquiv ν b N isOpen_Ioi (eM (i f)) =
      i' (modulatedSupportedMellinEquiv ν b N isOpen_Ioo (eL f))
    rw [hi]
    exact hcommL _
  · intro f
    change modulatedSupportedMellinEquiv ν b N isOpen_Ioi (eR (p f)) =
      p' (modulatedSupportedMellinEquiv ν b N isOpen_Ioi (eM f))
    rw [hp]
    exact hcommR _
  · exact eM.symm.injective.comp (hinj.comp eL.injective)
  · have he : range i = eM.symm '' range j := by
      rw [show (i : L → M) = eM.symm ∘ j ∘ eL from rfl, range_comp,
        range_comp, eL.surjective.range_eq, image_univ]
    rw [he]
    exact eM.symm.toHomeomorph.isClosedMap _ hclosed
  · intro f
    constructor
    · intro hf
      have hzero : q (eM f) = 0 := (hp f).symm.trans (by rw [hf, map_zero])
      obtain ⟨v, hv⟩ := (hex (eM f)).mp hzero
      refine ⟨eL.symm v, eM.injective ?_⟩
      rw [hi, eL.apply_symm_apply, hv]
    · rintro ⟨v, rfl⟩
      apply eR.injective
      rw [hp, hi, map_zero]
      exact (hex _).mpr ⟨_, rfl⟩
  · exact eR.symm.surjective.comp (hsurj.comp eM.surjective)
  · exact eR.symm.toHomeomorph.isOpenMap.comp (hopen.comp eM.toHomeomorph.isOpenMap)


/-- The endpoints have weighted Haar measure zero, so the closed
multiplicative window and its interior determine the same cutoff space. -/
theorem modulatedGroupCutoff_Icc_eq_Ioo (b s c d : ℝ) :
    modulatedGroupCutoff m τ hτ ν b s (Icc c d) =
      modulatedGroupCutoff m τ hτ ν b s (Ioo c d) := by
  ext u
  rw [modulatedGroupCutoff_mem_iff, modulatedGroupCutoff_mem_iff]
  constructor
  · intro hu
    filter_upwards [hu, modulatedGroupLog_ae_ne m τ hτ ν b s c,
      modulatedGroupLog_ae_ne m τ hτ ν b s d] with g hg hc hd hu'
    exact hg (fun hh ↦ hu' ⟨lt_of_le_of_ne hh.1 hc.symm, lt_of_le_of_ne hh.2 hd⟩)
  · intro hu
    exact hu.mono fun _ h hg ↦ h (fun hh ↦ hg (Ioo_subset_Icc_self hh))

/-- The supported weighted Haar space is the range of the specified
indicator multiplier, with a closed range and the usual idempotence. -/
theorem modulatedGroupCutoff_indicatorRange (b s : ℝ) {U : Set ℝ} (hU : MeasurableSet U) :
    let W := modulatedSobolevMeasure m τ hτ ν b s
    ∃ P : Lp ℂ 2 W →L[ℂ] Lp ℂ 2 W,
      IsClosed (range P) ∧ (∀ u, P (P u) = P u) ∧
      (∀ u, (P u : G → ℂ) =ᵐ[W] (modulatedLog m ⁻¹' U).indicator (u : G → ℂ)) ∧
      range P = (modulatedGroupCutoff m τ hτ ν b s U : Set (Lp ℂ 2 W)) := by
  intro W
  let A := modulatedLog m ⁻¹' U
  have hA : MeasurableSet A := (continuous_toAdd.comp m.continuous).measurable hU
  obtain ⟨P, hClosed, _, hP⟩ := lpTwo_measurableCutoff (μ := W) hA
  refine ⟨P, hClosed, fun u ↦ (hP u).1, fun u ↦ (hP u).2, ?_⟩
  ext u
  rw [SetLike.mem_coe, modulatedGroupCutoff_mem_iff]
  constructor
  · rintro ⟨v, rfl⟩
    filter_upwards [(hP v).2] with g h hg
    exact h.trans (indicator_of_notMem (show g ∉ A from hg) _)
  · intro h
    refine ⟨u, Lp.ext ?_⟩
    filter_upwards [h, (hP u).2] with g hg hp
    by_cases hmem : g ∈ A
    · exact hp.trans (indicator_of_mem hmem _)
    · exact hp.trans ((indicator_of_notMem hmem _).trans (hg hmem).symm)

end
end Masullo
