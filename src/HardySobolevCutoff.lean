import HardySobolevEvaluation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

open Filter Function MeasureTheory Set Topology
open scoped InnerProductSpace ENNReal

namespace Masullo

noncomputable section

local notation "realMeasure" => (volume : Measure ℝ)

private theorem stripMeasure_volume_equiv (a b s : ℝ) :
    realMeasure ≪ stripMeasure a b s ∧ stripMeasure a b s ≪ realMeasure :=
  ⟨absolutelyContinuous_amplitudeMeasure realMeasure _
      (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s),
    amplitudeMeasure_absolutelyContinuous realMeasure _⟩

/-- The closed span of supported smooth Mellin tests consists precisely of
classes vanishing outside their open logarithmic support. -/
theorem mem_supportedSobolevCompletion_iff (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U)
    (u : StripSobolev a b s) :
    u ∈ supportedSobolevCompletion a b s U ↔ ∀ᵐ x ∂realMeasure, x ∉ U → u x = 0 := by
  let S := supportedSobolevCompletion a b s U
  let μ := stripMeasure a b s
  obtain ⟨P, hPcl, _, hP⟩ := lpTwo_measurableCutoff (μ := μ) hU.measurableSet
  have hac := stripMeasure_volume_equiv a b s
  have hmem (v : StripSobolev a b s) :
      v ∈ range P ↔ ∀ᵐ x ∂realMeasure, x ∉ U → v x = 0 := by
    constructor
    · rintro ⟨w, rfl⟩
      filter_upwards [hac.1.ae_le (hP w).2] with x hx hxU
      rw [hx, indicator_of_notMem hxU]
    · intro hv
      refine ⟨v, Lp.ext ?_⟩
      filter_upwards [(hP v).2, hac.2.ae_le hv] with x hx hz
      rw [hx]
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem hxU]
      · rw [indicator_of_notMem hxU, hz hxU]
  constructor
  · intro hu
    apply (hmem u).mp
    apply closure_minimal _ hPcl hu
    rintro _ ⟨f, hf, rfl⟩
    refine (hmem _).mpr ?_
    filter_upwards [hac.1.ae_le (stripSobolevTest_ae univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ s f)]
      with x hx hxU
    exact hx.trans (hf x hxU)
  · intro hu
    change u ∈ S
    rw [← S.orthogonal_orthogonal]
    apply (Submodule.mem_orthogonal Sᗮ u).mpr
    intro v hv
    let L := InnerProductSpace.toDual ℂ (StripSobolev a b s) v
    let g := (stripSobolevDuality a b s).symm L
    have hzero : ∀ᵐ x ∂realMeasure, x ∈ U → g x = 0 := by
      apply stripDual_rep_eq_on_support_of_testPairing a b s (K := fun _ => (0 : ℂ))
        continuous_const hU L
      intro f hf
      simp only [mul_zero, integral_zero]
      exact Submodule.inner_left_of_mem_orthogonal (supportedSobolevTest a b s U f hf).property hv
    have hL : L u = 0 := by
      rw [← (stripSobolevDuality a b s).apply_symm_apply L, stripSobolevDuality_apply]
      have hprod : (fun x : ℝ => u x * g x) =ᵐ[realMeasure] 0 := by
        filter_upwards [hu, hzero] with x hx hg
        by_cases hxU : x ∈ U
        · simp [hg hxU]
        · simp [hx hxU]
      exact (integral_congr_ae hprod).trans (by simp)
    exact hL

/-- The cutoff projection has range equal to the supported Hardy–Sobolev
completion and is represented by the actual indicator multiplier. -/
theorem supportedSobolevCompletion_eq_cutoff (a b s : ℝ) {U : Set ℝ} (hU : IsOpen U) :
    ∃ P : StripSobolev a b s →L[ℂ] StripSobolev a b s,
      IsStarProjection P ∧ P.IsPositive ∧ ‖P‖ ≤ 1 ∧
      range P = (supportedSobolevCompletion a b s U : Set (StripSobolev a b s)) ∧
      ∀ u, (P u : ℝ → ℂ) =ᵐ[realMeasure] U.indicator (u : ℝ → ℂ) := by
  obtain ⟨P, hproj, hpos, _, hnorm, hP, _, _⟩ :=
    lpTwo_cutoff_isStarProjection (μ := stripMeasure a b s) hU.measurableSet
  have hac := stripMeasure_volume_equiv a b s
  refine ⟨P, hproj, hpos, hnorm, ?_, fun u => hac.1.ae_le (hP u)⟩
  ext u
  rw [SetLike.mem_coe, mem_supportedSobolevCompletion_iff a b s hU]
  constructor
  · rintro ⟨w, rfl⟩
    filter_upwards [hac.1.ae_le (hP w)] with x hx hxU
    rw [hx, indicator_of_notMem hxU]
  · intro hu
    refine ⟨u, Lp.ext ?_⟩
    filter_upwards [hP u, hac.2.ae_le hu] with x hx hz
    rw [hx]
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
    · rw [indicator_of_notMem hxU, hz hxU]


private theorem ae_ne_real (c : ℝ) : ∀ᵐ x ∂realMeasure, x ≠ c := by
  simp [ae_iff, measure_singleton]

private theorem real_indicator_Ioi_ae_eq_Ici (c : ℝ) (f : ℝ → ℂ) :
    (Ioi c).indicator f =ᵐ[realMeasure] (Ici c).indicator f := by
  filter_upwards [ae_ne_real c] with x hx
  by_cases h : c ≤ x
  · exact (indicator_of_mem (lt_of_le_of_ne h hx.symm : x ∈ Ioi c) f).trans
      (indicator_of_mem (show x ∈ Ici c from h) f).symm
  · exact (indicator_of_notMem (fun h' : x ∈ Ioi c => h h'.le) f).trans
      (indicator_of_notMem (show x ∉ Ici c from h) f).symm

/-- Open and inclusive lower cutoffs give the same projection on the
weighted Hilbert space, since a logarithmic endpoint is null. -/
theorem supportedSobolev_lowerCutoff_eq_projection (a b s c : ℝ) :
    ∃ P : StripSobolev a b s →L[ℂ] StripSobolev a b s,
      IsStarProjection P ∧ P.IsPositive ∧
      range P = (supportedSobolevCompletion a b s (Ioi c) : Set (StripSobolev a b s)) ∧
      ∀ u, (P u : ℝ → ℂ) =ᵐ[realMeasure] (Ici c).indicator (u : ℝ → ℂ) := by
  obtain ⟨P, hP, hpos, _, hrange, hae⟩ := supportedSobolevCompletion_eq_cutoff a b s
    (isOpen_Ioi : IsOpen (Ioi c))
  exact ⟨P, hP, hpos, hrange, fun u => (hae u).trans (real_indicator_Ioi_ae_eq_Ici c u)⟩

private theorem real_indicator_Ioo_ae_eq_Icc (c d : ℝ) (f : ℝ → ℂ) :
    (Ioo c d).indicator f =ᵐ[realMeasure] (Icc c d).indicator f := by
  filter_upwards [ae_ne_real c, ae_ne_real d] with x hc hd
  by_cases h : x ∈ Icc c d
  · exact (indicator_of_mem
      (show x ∈ Ioo c d from ⟨lt_of_le_of_ne h.1 hc.symm, lt_of_le_of_ne h.2 hd⟩) f).trans
      (indicator_of_mem h f).symm
  · exact (indicator_of_notMem (fun h' : x ∈ Ioo c d => h (Ioo_subset_Icc_self h')) f).trans
      (indicator_of_notMem h f).symm

private theorem mem_supportedSobolevCompletion_iff_indicator (a b s : ℝ) {U : Set ℝ}
    (hU : IsOpen U) (u : StripSobolev a b s) :
    u ∈ supportedSobolevCompletion a b s U ↔
      (u : ℝ → ℂ) =ᵐ[stripMeasure a b s] U.indicator (u : ℝ → ℂ) := by
  rw [mem_supportedSobolevCompletion_iff a b s hU]
  have hac := stripMeasure_volume_equiv a b s
  constructor
  · intro h
    filter_upwards [hac.2.ae_le h] with x hx
    by_cases hxU : x ∈ U
    · rw [indicator_of_mem hxU]
    · rw [indicator_of_notMem hxU, hx hxU]
  · intro h
    filter_upwards [hac.1.ae_le h] with x hx hxU
    rw [hx, indicator_of_notMem hxU]

/-- The scalar source row of the cutoff sequence on an arbitrary compact-base
weight. The middle term has the lower cutoff and the kernel consists of the
bounded logarithmic interval. -/
theorem stripSobolev_cutoff_exact (a b s c : ℝ) (hc : c ≤ 0) :
    let L := supportedSobolevCompletion a b s (Ioo c 0)
    let M := supportedSobolevCompletion a b s (Ioi c)
    let R := supportedSobolevCompletion a b s (Ioi 0)
    ∃ (i : L →L[ℂ] M) (p : M →L[ℂ] R),
      (∀ f : L, (i f).val = f.val) ∧
      (∀ f : M, ((p f).val : ℝ → ℂ) =ᵐ[realMeasure] (Ioi 0).indicator (f.val : ℝ → ℂ)) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by
  let μ := stripMeasure a b s
  have hac := stripMeasure_volume_equiv a b s
  have hz : μ (id ⁻¹' {0}) = 0 := hac.2 (by simpa only [preimage_id] using
    (measure_singleton (μ := realMeasure) (0 : ℝ)))
  obtain ⟨L, M, R, i, p, hL, hM, hR, hi, hp, hrest⟩ :=
    lpTwo_cutoff_exact μ id measurable_id c hc hz
  have hLeq : L = supportedSobolevCompletion a b s (Ioo c 0) := by
    apply SetLike.coe_injective
    rw [hL]
    ext u
    simp only [mem_ofPred_eq, SetLike.mem_coe, preimage_id,
      mem_supportedSobolevCompletion_iff_indicator a b s isOpen_Ioo]
    exact ⟨fun h => h.trans (hac.2.ae_le ((real_indicator_Ioo_ae_eq_Icc c 0 u).symm)),
      fun h => h.trans (hac.2.ae_le (real_indicator_Ioo_ae_eq_Icc c 0 u))⟩
  have hMeq : M = supportedSobolevCompletion a b s (Ioi c) := by
    apply SetLike.coe_injective
    rw [hM]
    ext u
    simp only [mem_ofPred_eq, SetLike.mem_coe, preimage_id,
      mem_supportedSobolevCompletion_iff_indicator a b s isOpen_Ioi]
    exact ⟨fun h => h.trans (hac.2.ae_le ((real_indicator_Ioi_ae_eq_Ici c u).symm)),
      fun h => h.trans (hac.2.ae_le (real_indicator_Ioi_ae_eq_Ici c u))⟩
  have hReq : R = supportedSobolevCompletion a b s (Ioi 0) := by
    apply SetLike.coe_injective
    rw [hR]
    ext u
    simp only [mem_ofPred_eq, SetLike.mem_coe, preimage_id,
      mem_supportedSobolevCompletion_iff_indicator a b s isOpen_Ioi]
    exact ⟨fun h => h.trans (hac.2.ae_le ((real_indicator_Ioi_ae_eq_Ici 0 u).symm)),
      fun h => h.trans (hac.2.ae_le (real_indicator_Ioi_ae_eq_Ici 0 u))⟩
  subst L M R
  refine ⟨i, p, hi, fun f => ?_, hrest⟩
  have h : ((p f).val : ℝ → ℂ) =ᵐ[μ] (Ici 0).indicator (f.val : ℝ → ℂ) := by
    simpa only [preimage_id] using hp f
  have hvol : ((p f).val : ℝ → ℂ) =ᵐ[realMeasure] (Ici 0).indicator (f.val : ℝ → ℂ) :=
    hac.1.ae_le h
  exact hvol.trans (real_indicator_Ioi_ae_eq_Ici 0 f.val).symm


private def stripShiftLeftWeight (a d b s : ℝ) :
    StripSobolev a b s ≃ₗᵢ[ℂ] StripSobolev d b s :=
  (amplitudeL2Iso realMeasure (stripSobolevAmplitude a b s)
    (stripSobolevAmplitude_continuous a b s).measurable
    (stripSobolevAmplitude_pos a b s)).trans
  (amplitudeL2Iso realMeasure (stripSobolevAmplitude d b s)
    (stripSobolevAmplitude_continuous d b s).measurable
    (stripSobolevAmplitude_pos d b s)).symm

private theorem stripShiftLeftWeight_ae (a d b s : ℝ)
    (u : supportedSobolevCompletion a b s (Ioi 0)) :
    (stripShiftLeftWeight a d b s u.val : ℝ → ℂ) =ᵐ[realMeasure] (u.val : ℝ → ℂ) := by
  let V := amplitudeL2Iso realMeasure (stripSobolevAmplitude a b s)
    (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s)
  have hV := amplitudeL2Iso_ae realMeasure (stripSobolevAmplitude a b s)
    (stripSobolevAmplitude_continuous a b s).measurable (stripSobolevAmplitude_pos a b s) u.val
  have hW := (stripMeasure_volume_equiv d b s).1.ae_le
    (amplitudeL2Iso_symm_ae realMeasure (stripSobolevAmplitude d b s)
      (stripSobolevAmplitude_continuous d b s).measurable (stripSobolevAmplitude_pos d b s) (V u.val))
  have hu := (mem_supportedSobolevCompletion_iff a b s isOpen_Ioi u.val).mp u.property
  filter_upwards [hV, hW, hu] with x hx hy hz
  change V u.val x = _ at hx
  change (stripShiftLeftWeight a d b s u.val) x = _ at hy
  rw [hy, hx, smul_smul]
  by_cases h : 0 < x
  · have he : stripSobolevAmplitude d b s x = stripSobolevAmplitude a b s x := by
      simp only [stripSobolevAmplitude, ite_eq_right h.not_ge]
    rw [he, inv_mul_cancel₀ (stripSobolevAmplitude_pos a b s x).ne', one_smul]
  · rw [hz (show x ∉ Ioi (0 : ℝ) from h), smul_zero]

/-- On the positive logarithmic ray the original compact-base norm is
isometric to the finite upper endpoint norm, with identical representatives. -/
def supportedSobolev_upperEndpointEquiv (a b s : ℝ) :
    supportedSobolevCompletion a b s (Ioi 0) ≃ₗᵢ[ℂ]
      supportedSobolevCompletion b b s (Ioi 0) := by
  let T := stripShiftLeftWeight a b b s
  let S := supportedSobolevCompletion a b s (Ioi 0)
  let R := supportedSobolevCompletion b b s (Ioi 0)
  have hmem (c d : ℝ) (u : supportedSobolevCompletion c b s (Ioi 0)) :
      stripShiftLeftWeight c d b s u.val ∈ supportedSobolevCompletion d b s (Ioi 0) := by
    apply (mem_supportedSobolevCompletion_iff d b s isOpen_Ioi _).mpr
    filter_upwards [stripShiftLeftWeight_ae c d b s u,
      (mem_supportedSobolevCompletion_iff c b s isOpen_Ioi _).mp u.property] with x hx hy hz
    exact hx.trans (hy hz)
  have hsymm : T.symm = stripShiftLeftWeight b a b s := rfl
  exact
    { toFun := fun u => ⟨T u.val, hmem a b u⟩
      invFun := fun v => ⟨T.symm v.val, hsymm ▸ hmem b a v⟩
      left_inv := fun u => Subtype.ext (T.symm_apply_apply u.val)
      right_inv := fun v => Subtype.ext (T.apply_symm_apply v.val)
      map_add' := fun u v => Subtype.ext (T.map_add u.val v.val)
      map_smul' := fun z u => Subtype.ext (T.map_smul z u.val)
      norm_map' := fun u => T.norm_map u.val }

theorem supportedSobolev_upperEndpointEquiv_ae (a b s : ℝ)
    (f : supportedSobolevCompletion a b s (Ioi 0)) :
    ((supportedSobolev_upperEndpointEquiv a b s f).val : ℝ → ℂ) =ᵐ[realMeasure] f.val :=
  stripShiftLeftWeight_ae a b b s f

end
end Masullo
