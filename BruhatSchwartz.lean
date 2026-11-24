import BruhatSchwartzStages
import TopologicalLinearLimits
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Function Set Topology
open scoped ContDiff NNReal

set_option maxHeartbeats 1500000

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Structural pairs together with a choice of elementary coordinates. -/
abbrev BruhatSchwartzStage (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  Σ P : LCAStructuralPair G, ElementaryLCAPresentation P.StageQuotient

abbrev BruhatSchwartzStage.Space (p : BruhatSchwartzStage G) :=
  ElementarySchwartz p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor

abbrev BruhatSchwartzStage.realize (p : BruhatSchwartzStage G) :
    p.Space →ₗ[ℂ] (G → ℂ) := p.1.realizeSchwartz p.2

/-- Two realized Schwartz–Bruhat functions can be represented on a common stage. -/
theorem bruhatSchwartzStages_common {p q : BruhatSchwartzStage G}
    (f : p.Space) (g : q.Space) :
    ∃ (r : BruhatSchwartzStage G) (u v : r.Space),
      r.realize u = p.realize f ∧ r.realize v = q.realize g := by
  letI := (lcaStructuralPairs_filtered (G := G)).2
  obtain ⟨R, hp, hq⟩ := exists_ge_ge p.1 q.1
  obtain ⟨r⟩ := R.quotient_elementary
  have hpu : p.1.upper.val ≤ R.upper.val := hp.1
  have hpk : R.kernel ≤ p.1.kernel := hp.2
  have hqu : q.1.upper.val ≤ R.upper.val := hq.1
  have hqk : R.kernel ≤ q.1.kernel := hq.2
  obtain ⟨L, _, hL⟩ := p.1.schwartz_refinement_closedEmbedding R hpu hpk p.2 r
  obtain ⟨M, _, hM⟩ := q.1.schwartz_refinement_closedEmbedding R hqu hqk q.2 r
  let Rr : BruhatSchwartzStage G := ⟨R, r⟩
  refine ⟨Rr, L f, M g, ?_, ?_⟩
  · exact hL f
  · exact hM g

/-- The actual Schwartz–Bruhat functions form the directed union of the
realized elementary stages. -/
def bruhatSchwartzSubmodule : Submodule ℂ (G → ℂ) where
  carrier := {f | ∃ (p : BruhatSchwartzStage G) (g : p.Space), p.realize g = f}
  zero_mem' := by
    obtain ⟨P⟩ := (lcaStructuralPairs_filtered (G := G)).1
    obtain ⟨p⟩ := P.quotient_elementary
    exact ⟨⟨P, p⟩, 0, map_zero (P.realizeSchwartz p)⟩
  add_mem' := by
    rintro f g ⟨p, u, rfl⟩ ⟨q, v, rfl⟩
    obtain ⟨r, f₀, g₀, hf, hg⟩ := bruhatSchwartzStages_common u v
    exact ⟨r, f₀ + g₀, by rw [map_add, hf, hg]⟩
  smul_mem' := by
    rintro c f ⟨p, u, rfl⟩
    exact ⟨p, c • u, map_smul _ _ _⟩

abbrev BruhatSchwartz (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] := bruhatSchwartzSubmodule (G := G)

def BruhatSchwartzStage.inclusion (p : BruhatSchwartzStage G) :
    p.Space →ₗ[ℂ] BruhatSchwartz G :=
  p.realize.codRestrict _ fun f ↦ ⟨p, f, rfl⟩

instance : TopologicalSpace (BruhatSchwartz G) :=
  locallyConvexFinalTopology (fun p : BruhatSchwartzStage G ↦ p.inclusion)

instance : PolynormableSpace ℂ (BruhatSchwartz G) :=
  (locallyConvexFinal_withSeminorms (fun p : BruhatSchwartzStage G ↦ p.inclusion)).toPolynormableSpace

/-- A stage realization is Bruhat-smooth, by restricting a common refinement
to each quotient for the same good kernel. -/
theorem BruhatSchwartzStage.realize_smooth (p : BruhatSchwartzStage G) (f : p.Space) :
    p.realize f ∈ bruhatSmoothSubmodule (G := G) := by
  let P := p.1
  intro s
  refine ⟨P, fun k x ↦ ?_, fun Q hk q ↦ ?_⟩
  · have hkx : k.val ∈ P.upper.val := P.kernel_le k.property
    by_cases hx : x ∈ P.upper.val
    · let y : P.upper.val := ⟨x, hx⟩
      let z : P.upper.val := ⟨k.val, hkx⟩
      change P.realizeSchwartz p.2 f (z * y).val = P.realizeSchwartz p.2 f y.val
      rw [P.realizeSchwartz_apply_of_mem, P.realizeSchwartz_apply_of_mem, map_mul]
      have hz : P.stageCoordinates p.2 z = 1 := by
        change p.2.equiv (QuotientGroup.mk z) = 1
        rw [(QuotientGroup.eq_one_iff z).mpr k.property, map_one]
      rw [hz, one_mul]
    · have hnot : k.val * x ∉ P.upper.val := by
        intro h
        have H := P.upper.val.mul_mem (P.upper.val.inv_mem hkx) h
        exact hx (by simpa only [inv_mul_cancel_left] using H)
      exact (P.realizeSchwartz_apply_of_not_mem p.2 f _ hnot).trans
        (P.realizeSchwartz_apply_of_not_mem p.2 f _ hx).symm
  · letI := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
    obtain ⟨J, hQJ, hPJ⟩ := exists_ge_ge Q.upper P.upper
    let R : LCAStructuralPair G :=
      ⟨J, P.kernel, P.kernel_closed, P.annihilator_open, P.annihilator_compactlyGenerated,
        P.kernel_le.trans hPJ⟩
    obtain ⟨r⟩ := R.quotient_elementary
    obtain ⟨L, _, hL⟩ := P.schwartz_refinement_closedEmbedding R hPJ le_rfl p.2 r
    let a := Q.stageCoordinateMap R hQJ (hk.symm ▸ le_rfl) q r
    have hS (d b) := ((L f).property.1 d b).of_le (show (s : WithTop ℕ∞) ≤ ∞ from by
      exact_mod_cast (le_top : (s : ℕ∞) ≤ ⊤))
    refine ⟨(L f).val ∘ a.toMonoidHom.toAdditive, fun x ↦ ?_,
      elementaryContDiff_hom a.toMonoidHom.toAdditive a.continuous _ hS⟩
    change (L f) (a (Q.stageCoordinates q x)).toAdd = p.realize f x.val
    dsimp only [a]
    rw [Q.stageCoordinateMap_stageCoordinates]
    exact (R.realizeSchwartz_apply_of_mem r (L f) (Subgroup.inclusion hQJ x)).symm.trans
      (congrFun (hL f) x.val)

theorem bruhatSchwartz_le_smooth :
    bruhatSchwartzSubmodule (G := G) ≤ bruhatSmoothSubmodule (G := G) := by
  rintro f ⟨p, u, rfl⟩
  exact p.realize_smooth u

/-- Schwartz–Bruhat functions are continuous on the ambient group. -/
theorem bruhatSchwartz_continuous (f : BruhatSchwartz G) : Continuous f.val :=
  (bruhatSchwartz_le_smooth f.property 0).continuous

private theorem bruhatSchwartz_derivative_mem (c : Multiplicative ℝ →ₜ* G)
    (f : BruhatSchwartz G) : bruhatOrbitDeriv c f.val ∈ bruhatSchwartzSubmodule (G := G) := by
  obtain ⟨p, u, hu⟩ := f.property
  exact ⟨p, elementarySchwartz_derivative
    ((p.1.stageCoordinates p.2).comp (p.1.restrictOneParameter c)) u,
      (p.1.bruhatOrbitDeriv_realizeSchwartz p.2 c u).symm.trans
        (congrArg (bruhatOrbitDeriv c) hu)⟩

/-- The first-order operator on the actual Schwartz–Bruhat inductive limit
restricts from the smooth function space and is continuous. -/
def bruhatSchwartz_derivative (c : Multiplicative ℝ →ₜ* G) :
    BruhatSchwartz G →L[ℂ] BruhatSchwartz G := by
  let j := (bruhatSmoothSubmodule (G := G)).subtype.comp
    ((bruhatFirstOrder c).comp (Submodule.inclusion bruhatSchwartz_le_smooth))
  let L := j.codRestrict _ (bruhatSchwartz_derivative_mem c)
  refine ⟨L, ?_⟩
  apply (locallyConvexFinal_continuous_iff
    (fun p : BruhatSchwartzStage G ↦ p.inclusion) L).mpr
  intro p
  let D := elementarySchwartz_derivative
    ((p.1.stageCoordinates p.2).comp (p.1.restrictOneParameter c))
  have hEq : (L.comp p.inclusion : p.Space → BruhatSchwartz G) = p.inclusion ∘ D := by
    funext u
    apply Subtype.ext
    exact p.1.bruhatOrbitDeriv_realizeSchwartz p.2 c u
  rw [hEq]
  exact (locallyConvexFinal_stage_continuous
    (fun p : BruhatSchwartzStage G ↦ p.inclusion) p).comp D.continuous

theorem bruhatSchwartz_derivative_eq_firstOrder (c : Multiplicative ℝ →ₜ* G)
    (f : BruhatSchwartz G) :
    Submodule.inclusion bruhatSchwartz_le_smooth (bruhatSchwartz_derivative c f) =
      bruhatFirstOrder c (Submodule.inclusion bruhatSchwartz_le_smooth f) :=
  Subtype.ext rfl

/-- Evaluation is continuous in the final locally convex Schwartz topology. -/
theorem bruhatSchwartz_continuous_eval (x : G) :
    Continuous (fun f : BruhatSchwartz G ↦ f.val x) := by
  let e : BruhatSchwartz G →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ f.val x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  change Continuous e
  apply (locallyConvexFinal_continuous_iff
    (fun p : BruhatSchwartzStage G ↦ p.inclusion) e).mpr
  intro p
  change Continuous (fun f : p.Space ↦ p.realize f x)
  by_cases hx : x ∈ p.1.upper.val
  · let y : p.1.upper.val := ⟨x, hx⟩
    let z := (p.1.stageCoordinates p.2 y).toAdd
    let e₀ : p.Space →ₗ[ℂ] ℂ :=
      { toFun := fun f ↦ f z
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    have he₀ : (fun f : p.Space ↦ p.realize f x) = e₀ :=
      funext fun f ↦ p.1.realizeSchwartz_apply_of_mem p.2 f y
    rw [he₀]
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp
    intro i
    refine Seminorm.continuous_of_le
      (elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)) fun f ↦ ?_
    change ‖f z‖ ≤ (elementarySchwartzSeminorm (0, 0, 0, 0)) f
    have hb : (‖f z‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) := by
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun w ↦ (‖f w‖₊ : ENNReal)) z
    exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb
  · have hzero : (fun f : p.Space ↦ p.realize f x) = fun _ ↦ 0 :=
      funext fun f ↦ p.1.realizeSchwartz_apply_of_not_mem p.2 f x hx
    rw [hzero]
    exact continuous_const

/-- The full Schwartz–Bruhat topology is Hausdorff. -/
theorem bruhatSchwartz_t2 : T2Space (BruhatSchwartz G) :=
  T2Space.of_injective_continuous (f := fun f : BruhatSchwartz G ↦ f.val)
    Subtype.val_injective (continuous_pi bruhatSchwartz_continuous_eval)

/-- The compact character average in Definition 4.4.2.1 exists for each
translate of a Schwartz–Bruhat function. Adapted from the Apache-2.0
RiemannMasullo proof at a735545. -/
theorem bruhatSchwartz_isotypicPeriodization_integrable
    (μ : G →ₜ* Multiplicative ℝ) (hproper : IsProperMap μ)
    [MeasurableSpace μ.toMonoidHom.ker] [BorelSpace μ.toMonoidHom.ker]
    (ν : MeasureTheory.Measure μ.toMonoidHom.ker) [MeasureTheory.IsFiniteMeasureOnCompacts ν]
    (χ : G →ₜ* Circle) (f : BruhatSchwartz G) (g x : G) :
    MeasureTheory.Integrable
      (fun k : μ.toMonoidHom.ker ↦ (χ k.val : ℂ) * f.val (g * (k.val * x))) ν := by
  have hf : Continuous f.val := (bruhatSchwartz_le_smooth f.property 0).continuous
  letI : CompactSpace μ.toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (hproper.isCompact_preimage (isCompact_singleton (x := 1)))
  have hc : Continuous (fun k : μ.toMonoidHom.ker ↦
      (χ k.val : ℂ) * f.val (g * (k.val * x))) :=
    (continuous_subtype_val.comp (χ.continuous.comp continuous_subtype_val)).mul
      (hf.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const)))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)


end

end Masullo
