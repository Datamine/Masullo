import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

open Filter Function Set Topology
open scoped NNReal TensorProduct

namespace Masullo

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- A continuous seminorm on a normed space is bounded by a multiple of its norm. -/
theorem continuousSeminorm_le_norm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (p : Seminorm ℂ X) (hp : Continuous p) : ∃ C : ℝ≥0, ∀ x, p x ≤ (C : ℝ) * ‖x‖ := by
  obtain ⟨s, C, _, h⟩ := Seminorm.bound_of_continuous (norm_withSeminorms ℂ X) p hp
  refine ⟨C, fun x => (h x).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (show (s.sup (fun _ => normSeminorm ℂ X)) x ≤ ‖x‖ from
      (Finset.sup_le (fun _ _ => le_rfl : ∀ a ∈ s, normSeminorm ℂ X ≤ normSeminorm ℂ X)) x)
    C.coe_nonneg

/-- The seminorm tests for the projective tensor topology are exactly the
seminorms bounded on elementary tensors by products of continuous seminorms. -/
structure ProjectiveTensorTest (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] where
  tensor : Seminorm ℂ (E ⊗[ℂ] F)
  first : Seminorm ℂ E
  second : Seminorm ℂ F
  first_continuous : Continuous first
  second_continuous : Continuous second
  bound (x : E) (y : F) : tensor (x ⊗ₜ[ℂ] y) ≤ first x * second y

abbrev projectiveTensorTopology (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] : TopologicalSpace (E ⊗[ℂ] F) :=
  (SeminormFamily.moduleFilterBasis (ProjectiveTensorTest.tensor (E := E) (F := F))).topology

theorem projectiveTensor_withSeminorms :
    letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
    WithSeminorms (ProjectiveTensorTest.tensor (E := E) (F := F)) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  exact ⟨rfl⟩

theorem bilinear_bound_of_nhds [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (f : E →ₗ[ℂ] F →ₗ[ℂ] G) (q : Seminorm ℂ G)
    (hsub : {p : E × F | q (f p.1 p.2) ≤ 1} ∈ 𝓝 (0, 0)) :
    ∃ p : Seminorm ℂ E, ∃ r : Seminorm ℂ F, Continuous p ∧ Continuous r ∧
      ∀ x y, q (f x y) ≤ p x * r y := by
  rw [nhds_prod_eq] at hsub
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hsub
  let hE := PolynormableSpace.withSeminorms ℂ E
  let hF := PolynormableSpace.withSeminorms ℂ F
  letI : IsTopologicalAddGroup E := hE.topologicalAddGroup
  letI : IsTopologicalAddGroup F := hF.topologicalAddGroup
  obtain ⟨⟨I, a⟩, ha, hIU⟩ := hE.hasBasis_zero_ball.mem_iff.mp hU
  obtain ⟨⟨J, b⟩, hb, hJV⟩ := hF.hasBasis_zero_ball.mem_iff.mp hV
  let p₀ := I.sup (fun p : {s : Seminorm ℂ E // Continuous s} => p.val)
  let r₀ := J.sup (fun p : {s : Seminorm ℂ F // Continuous s} => p.val)
  let a' : ℝ≥0 := ⟨a⁻¹, inv_nonneg.mpr ha.le⟩
  let b' : ℝ≥0 := ⟨b⁻¹, inv_nonneg.mpr hb.le⟩
  let p : Seminorm ℂ E := a' • p₀
  let r : Seminorm ℂ F := b' • r₀
  have hp₀ : Continuous p₀ := Seminorm.continuous_finsetSup fun i _ => i.property
  have hr₀ : Continuous r₀ := Seminorm.continuous_finsetSup fun i _ => i.property
  have hp : Continuous p := continuous_const.mul hp₀
  have hr : Continuous r := continuous_const.mul hr₀
  have hpU : p.ball 0 1 ⊆ U := by
    intro x hx
    apply hIU
    apply p₀.mem_ball_zero.mpr
    have he : a⁻¹ * p₀ x < 1 := p.mem_ball_zero.mp hx
    exact (inv_mul_lt_iff₀ ha).mp he |>.trans_eq (mul_one _)
  have hrV : r.ball 0 1 ⊆ V := by
    intro y hy
    apply hJV
    apply r₀.mem_ball_zero.mpr
    have he : b⁻¹ * r₀ y < 1 := r.mem_ball_zero.mp hy
    exact (inv_mul_lt_iff₀ hb).mp he |>.trans_eq (mul_one _)
  refine ⟨p, r, hp, hr, fun x y => ?_⟩
  have hh (ε : ℝ) (hε : 0 < ε) : q (f x y) ≤ (p x + ε) * (r y + ε) := by
    let d : ℝ := p x + ε
    let e : ℝ := r y + ε
    have hd : 0 < d := add_pos_of_nonneg_of_pos (apply_nonneg p x) hε
    have he : 0 < e := add_pos_of_nonneg_of_pos (apply_nonneg r y) hε
    have hx' : ((d : ℂ)⁻¹) • x ∈ p.ball 0 1 := by
      apply p.mem_ball_zero.mpr
      rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      exact (inv_mul_lt_iff₀ hd).mpr (by simpa [d] using lt_add_of_pos_right (p x) hε)
    have hy' : ((e : ℂ)⁻¹) • y ∈ r.ball 0 1 := by
      apply r.mem_ball_zero.mpr
      rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
      exact (inv_mul_lt_iff₀ he).mpr (by simpa [e] using lt_add_of_pos_right (r y) hε)
    have h : q (f (((d : ℂ)⁻¹) • x) (((e : ℂ)⁻¹) • y)) ≤ 1 :=
      hUV (show (((d : ℂ)⁻¹) • x, ((e : ℂ)⁻¹) • y) ∈ U ×ˢ V from ⟨hpU hx', hrV hy'⟩)
    have hfx : f (((d : ℂ)⁻¹) • x) y = ((d : ℂ)⁻¹) • f x y :=
      congrArg (fun g : F →ₗ[ℂ] G => g y) (f.map_smul _ x)
    rw [(f _).map_smul, hfx, map_smul_eq_mul, map_smul_eq_mul,
      norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg he.le,
      Real.norm_of_nonneg hd.le] at h
    have hd' := (inv_mul_le_iff₀ hd).mp ((inv_mul_le_iff₀ he).mp h)
    simpa [d, e] using hd'
  have hc : Continuous (fun ε : ℝ => (p x + ε) * (r y + ε)) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => (p x + ε) * (r y + ε)) (𝓝[>] 0) (𝓝 (p x * r y)) := by
    have h := hc.continuousWithinAt (s := Ioi (0 : ℝ)) (x := 0)
    rw [ContinuousWithinAt, add_zero, add_zero] at h
    exact h
  haveI : (𝓝[>] (0 : ℝ)).NeBot := inferInstance
  have hz : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Ioi 0 := self_mem_nhdsWithin
  exact isClosed_Ici.mem_of_tendsto ht (hz.mono fun ε hε => hh ε hε)

theorem continuous_bilinear_bound [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    (f : E →ₗ[ℂ] F →ₗ[ℂ] G) (hf : Continuous (fun p : E × F => f p.1 p.2))
    (q : Seminorm ℂ G) (hq : Continuous q) :
    ∃ p : Seminorm ℂ E, ∃ r : Seminorm ℂ F, Continuous p ∧ Continuous r ∧
      ∀ x y, q (f x y) ≤ p x * r y :=
  bilinear_bound_of_nhds f q
    (((hq.comp hf).tendsto' (0, 0) 0 (by simp)) (Iic_mem_nhds zero_lt_one))

/-- Jointly continuous bilinear maps linearize continuously for the
projective tensor topology. -/
theorem continuous_projectiveTensor_lift [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G]
    (f : E →ₗ[ℂ] F →ₗ[ℂ] G) (hf : Continuous (fun p : E × F => f p.1 p.2)) :
    Continuous[projectiveTensorTopology E F, inferInstance] (TensorProduct.lift f) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  let hG := PolynormableSpace.withSeminorms ℂ G
  apply (hG.continuous_iff_continuous_comp (TensorProduct.lift f)).2
  rintro ⟨q, hq⟩
  obtain ⟨p, r, hp, hr, hb⟩ := continuous_bilinear_bound f hf q hq
  let I : ProjectiveTensorTest E F :=
    ⟨q.comp (TensorProduct.lift f), p, r, hp, hr, fun x y => by simpa using hb x y⟩
  exact projectiveTensor_withSeminorms.continuous_seminorm I

/-- The elementary tensor map is jointly continuous for the projective topology. -/
theorem continuous_projectiveTensor_tmul [IsTopologicalAddGroup E] [IsTopologicalAddGroup F] :
    Continuous[inferInstance, projectiveTensorTopology E F]
      (fun z : E × F => z.1 ⊗ₜ[ℂ] z.2) := by
  letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
  have hW := projectiveTensor_withSeminorms (E := E) (F := F)
  haveI : IsTopologicalAddGroup (E ⊗[ℂ] F) := hW.topologicalAddGroup
  apply continuous_iff_continuousAt.mpr
  rintro ⟨x, y⟩
  apply (hW.tendsto_nhds _ _).mpr
  intro P ε hε
  let C (z : E × F) := P.first (z.1 - x) * P.second z.2 +
    P.first x * P.second (z.2 - y)
  have hC0 : C (x, y) = 0 := by simp [C]
  have hbound (z : E × F) : P.tensor (z.1 ⊗ₜ[ℂ] z.2 - x ⊗ₜ[ℂ] y) ≤ C z := by
    have he : z.1 ⊗ₜ[ℂ] z.2 - x ⊗ₜ[ℂ] y =
        (z.1 - x) ⊗ₜ[ℂ] z.2 + x ⊗ₜ[ℂ] (z.2 - y) := by
      rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel
    rw [he]
    exact (map_add_le_add P.tensor _ _).trans
      (add_le_add (P.bound _ _) (P.bound _ _))
  have hc : Continuous C := by
    exact ((P.first_continuous.comp (continuous_fst.sub continuous_const)).mul
      (P.second_continuous.comp continuous_snd)).add
      (continuous_const.mul (P.second_continuous.comp (continuous_snd.sub continuous_const)))
  exact ((hc.tendsto' (x, y) 0 hC0).eventually (Iio_mem_nhds hε)).mono
    fun z hz => (hbound z).trans_lt hz

/-- The projective topology has the continuous bilinear mapping property. -/
theorem continuous_projectiveTensor_lift_iff [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    {G : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G]
    (f : E →ₗ[ℂ] F →ₗ[ℂ] G) :
    Continuous[projectiveTensorTopology E F, inferInstance] (TensorProduct.lift f) ↔
      Continuous (fun z : E × F => f z.1 z.2) := by
  constructor
  · intro h
    letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
    letI : IsTopologicalAddGroup F := (PolynormableSpace.withSeminorms ℂ F).topologicalAddGroup
    letI : TopologicalSpace (E ⊗[ℂ] F) := projectiveTensorTopology E F
    have he : ((TensorProduct.lift f : (E ⊗[ℂ] F) → G) ∘
        (fun z : E × F => z.1 ⊗ₜ[ℂ] z.2)) = (fun z => f z.1 z.2) :=
      funext fun z => TensorProduct.lift.tmul (f' := f) z.1 z.2
    rw [← he]
    exact h.comp (continuous_projectiveTensor_tmul (E := E) (F := F))
  · exact continuous_projectiveTensor_lift f

/-- The tensor of continuous linear maps is continuous for the projective topologies. -/
theorem projectiveTensor_map_continuous [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    {G H : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G] [PolynormableSpace ℂ G]
    [AddCommGroup H] [Module ℂ H] [TopologicalSpace H] [PolynormableSpace ℂ H]
    (i : E →L[ℂ] G) (j : F →L[ℂ] H) :
    Continuous[projectiveTensorTopology E F, projectiveTensorTopology G H]
      (TensorProduct.map i.toLinearMap j.toLinearMap) := by
  letI : TopologicalSpace (G ⊗[ℂ] H) := projectiveTensorTopology G H
  letI : PolynormableSpace ℂ (G ⊗[ℂ] H) :=
    projectiveTensor_withSeminorms.toPolynormableSpace
  letI : IsTopologicalAddGroup G := (PolynormableSpace.withSeminorms ℂ G).topologicalAddGroup
  letI : IsTopologicalAddGroup H := (PolynormableSpace.withSeminorms ℂ H).topologicalAddGroup
  let L := TensorProduct.map i.toLinearMap j.toLinearMap
  let B := TensorProduct.curry L
  have hL : TensorProduct.lift B = L := by
    apply TensorProduct.ext'
    intro x y
    rfl
  have hB : Continuous (fun z : E × F => B z.1 z.2) := by
    have he : (fun z : E × F => B z.1 z.2) = (fun z => i z.1 ⊗ₜ[ℂ] j z.2) :=
      funext fun z => TensorProduct.map_tmul _ _ _ _
    rw [he]
    exact continuous_projectiveTensor_tmul.comp
      ((i.continuous.comp continuous_fst).prodMk (j.continuous.comp continuous_snd))
  rw [← show TensorProduct.lift B = TensorProduct.map i.toLinearMap j.toLinearMap from hL]
  exact continuous_projectiveTensor_lift B hB

omit [TopologicalSpace E] [TopologicalSpace F] in
/-- The tensor of two dense maps has dense range for the projective topology. -/
theorem projectiveTensor_map_denseRange
    {G H : Type*} [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [AddCommGroup H] [Module ℂ H] [TopologicalSpace H]
    [IsTopologicalAddGroup H] (f : E →ₗ[ℂ] G) (g : F →ₗ[ℂ] H)
    (hf : DenseRange f) (hg : DenseRange g) :
    @DenseRange _ (projectiveTensorTopology G H) _ (TensorProduct.map f g) := by
  letI : TopologicalSpace (G ⊗[ℂ] H) := projectiveTensorTopology G H
  letI : IsTopologicalAddGroup (G ⊗[ℂ] H) := projectiveTensor_withSeminorms.topologicalAddGroup
  letI : ContinuousSMul ℂ (G ⊗[ℂ] H) := projectiveTensor_withSeminorms.continuousSMul
  let L := TensorProduct.map f g
  let C := L.range.topologicalClosure
  intro z
  change z ∈ C
  induction z using TensorProduct.induction_on with
  | zero => exact C.zero_mem
  | tmul x y =>
    refine (hf.prodMap hg).induction_on (p := fun p => p.1 ⊗ₜ[ℂ] p.2 ∈ C) (x, y)
      (L.range.isClosed_topologicalClosure.preimage continuous_projectiveTensor_tmul) ?_
    rintro ⟨a, b⟩
    exact L.range.le_topologicalClosure ⟨a ⊗ₜ[ℂ] b, TensorProduct.map_tmul _ _ _ _⟩
  | add x y hx hy => exact C.add_mem hx hy

end

end Masullo
