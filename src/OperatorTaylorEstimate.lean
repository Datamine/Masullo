import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms

open Asymptotics Filter Set
open scoped BigOperators NNReal Topology

namespace Masullo

section

variable {E F G : Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]

/-- A first-order operator Taylor estimate, with a quadratic remainder
controlled in each continuous output seminorm by a continuous input seminorm. -/
def HasOperatorTaylorEstimate (A : ℂ → E →L[ℂ] F) (c : ℂ) (D : E →L[ℂ] F) : Prop :=
  ∀ q : Seminorm ℂ F, Continuous q →
    ∃ p : Seminorm ℂ E, Continuous p ∧
      ∀ᶠ h : ℂ in 𝓝 0, ∀ x, q (A (c + h) x - A c x - h • D x) ≤ ‖h‖ ^ 2 * p x

namespace HasOperatorTaylorEstimate

variable {A B : ℂ → E →L[ℂ] F} {D D' : E →L[ℂ] F} {c : ℂ}

theorem const (T : E →L[ℂ] F) (c : ℂ) :
    HasOperatorTaylorEstimate (fun _ => T) c 0 := by
  intro q hq
  exact ⟨0, continuous_const, .of_forall fun h x => by simp⟩

theorem parameter [ContinuousConstSMul ℂ F] (T : E →L[ℂ] F) (c : ℂ) :
    HasOperatorTaylorEstimate (fun z => z • T) c T := by
  intro q hq
  refine ⟨0, continuous_const, .of_forall fun h x => ?_⟩
  simp [add_smul, add_sub_cancel_left]

theorem congr (h : HasOperatorTaylorEstimate A c D) (he : A =ᶠ[𝓝 c] B) :
    HasOperatorTaylorEstimate B c D := by
  intro q hq
  obtain ⟨p, hp, hbound⟩ := h q hq
  have hs : Tendsto (fun h : ℂ => c + h) (𝓝 0) (𝓝 c) := by
    have hc : Continuous (fun h : ℂ => c + h) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℂ)
  refine ⟨p, hp, ?_⟩
  filter_upwards [hbound, hs.eventually he] with z hz hez x
  simpa only [← hez, ← he.eq_of_nhds] using hz x

theorem add [IsTopologicalAddGroup F] (ha : HasOperatorTaylorEstimate A c D) (hb : HasOperatorTaylorEstimate B c D') :
    HasOperatorTaylorEstimate (fun z => A z + B z) c (D + D') := by
  intro q hq
  obtain ⟨p, hp, ha⟩ := ha q hq
  obtain ⟨r, hr, hb⟩ := hb q hq
  refine ⟨p + r, hp.add hr, ?_⟩
  filter_upwards [ha, hb] with h ha hb x
  simp only [add_apply, mul_add]
  have he : A (c + h) x + B (c + h) x - (A c x + B c x) - h • (D x + D' x) =
      (A (c + h) x - A c x - h • D x) + (B (c + h) x - B c x - h • D' x) := by module
  rw [he]
  exact (map_add_le_add _ _ _).trans (add_le_add (ha x) (hb x))

/-- A Taylor estimate gives locally uniform control of both the operator
and its difference from the value at the center. -/
theorem local_bounds (ha : HasOperatorTaylorEstimate A c D) (q : Seminorm ℂ F)
    (hq : Continuous q) :
    ∃ p : Seminorm ℂ E, Continuous p ∧ ∀ᶠ h : ℂ in 𝓝 0, ∀ x,
      q (A (c + h) x) ≤ p x ∧ q (A (c + h) x - A c x) ≤ ‖h‖ * p x := by
  obtain ⟨r, hr, ha⟩ := ha q hq
  let p := r + q.comp D.toLinearMap + q.comp (A c).toLinearMap
  refine ⟨p, (hr.add (hq.comp D.continuous)).add (hq.comp (A c).continuous), ?_⟩
  have hsmall : ∀ᶠ h : ℂ in 𝓝 0, ‖h‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with h hh
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  filter_upwards [ha, hsmall] with h hh hsmall x
  have hn := norm_nonneg h
  have hsq : ‖h‖ ^ 2 ≤ ‖h‖ := by nlinarith [mul_nonneg hn (sub_nonneg.mpr hsmall.le)]
  have hdiff : q (A (c + h) x - A c x) ≤ ‖h‖ * (r x + q (D x)) := by
    calc
      _ = q (((A (c + h) x - A c x) - h • D x) + h • D x) := by rw [sub_add_cancel]
      _ ≤ _ := map_add_le_add _ _ _
      _ ≤ ‖h‖ ^ 2 * r x + ‖h‖ * q (D x) := by rw [map_smul_eq_mul]; gcongr; exact hh x
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right hsq (apply_nonneg r x)) le_rfl
  have hsum : r x + q (D x) ≤ p x := by
    exact le_add_of_nonneg_right (apply_nonneg q (A c x))
  refine ⟨?_, hdiff.trans (mul_le_mul_of_nonneg_left hsum hn)⟩
  calc
    _ = q ((A (c + h) x - A c x) + A c x) := by rw [sub_add_cancel]
    _ ≤ _ := map_add_le_add _ _ _
    _ ≤ (r x + q (D x)) + q (A c x) := by
      exact add_le_add (hdiff.trans (mul_le_of_le_one_left (by positivity) hsmall.le)) le_rfl
    _ = p x := rfl

/-- Locally controlled operator families satisfy the product rule under composition. -/
theorem comp [IsTopologicalAddGroup G] {A : ℂ → F →L[ℂ] G} {C : F →L[ℂ] G}
    (ha : HasOperatorTaylorEstimate A c C) (hb : HasOperatorTaylorEstimate B c D') :
    HasOperatorTaylorEstimate (fun z => (A z).comp (B z)) c
      (C.comp (B c) + (A c).comp D') := by
  intro q hq
  obtain ⟨p, hp, hA⟩ := ha q hq
  obtain ⟨r, hr, hR⟩ := ha.local_bounds q hq
  obtain ⟨s, hs, hB⟩ := hb r hr
  let t := p.comp (B c).toLinearMap + r.comp D'.toLinearMap + s
  refine ⟨t, ((hp.comp (B c).continuous).add (hr.comp D'.continuous)).add hs, ?_⟩
  filter_upwards [hA, hR, hB] with h hA hR hB x
  let u := A (c + h) (B c x) - A c (B c x) - h • C (B c x)
  let v := A (c + h) (D' x) - A c (D' x)
  let w := B (c + h) x - B c x - h • D' x
  have he : A (c + h) (B (c + h) x) - A c (B c x) -
      h • (C (B c x) + A c (D' x)) = u + h • v + A (c + h) w := by
    simp only [u, v, w, map_sub, map_smul]
    module
  simp only [ContinuousLinearMap.comp_apply, add_apply]
  rw [he]
  calc
    _ ≤ (q u + q (h • v)) + q (A (c + h) w) :=
      (map_add_le_add _ _ _).trans (add_le_add (map_add_le_add _ _ _) le_rfl)
    _ ≤ (‖h‖ ^ 2 * p (B c x) + ‖h‖ * (‖h‖ * r (D' x))) + ‖h‖ ^ 2 * s x := by
      rw [map_smul_eq_mul]
      exact add_le_add (add_le_add (hA _) (mul_le_mul_of_nonneg_left (hR _).2 (norm_nonneg _)))
        ((hR w).1.trans (hB x))
    _ = _ := by
      change _ = ‖h‖ ^ 2 * (p (B c x) + r (D' x) + s x)
      ring

theorem smul_const [ContinuousConstSMul ℂ F] [IsTopologicalAddGroup F]
    (h : HasOperatorTaylorEstimate A c D) (a : ℂ) :
    HasOperatorTaylorEstimate (fun z => a • A z) c (a • D) := by
  have ht := (const (a • ContinuousLinearMap.id ℂ F) c).comp h
  convert ht using 1 <;> ext <;> simp

/-- An analytic scalar times a fixed operator has a quadratic Taylor remainder
controlled by the pullback of each output seminorm. -/
theorem analytic_smul_fixed [ContinuousConstSMul ℂ F] {a : ℂ → ℂ} (ha : AnalyticAt ℂ a c) (T : E →L[ℂ] F) :
    ∃ P, HasOperatorTaylorEstimate (fun z => a z • T) c P := by
  obtain ⟨p, hp⟩ := ha
  let d := p 1 (fun _ => 1)
  have hmap : Tendsto (fun h : ℂ => (c + h, c)) (𝓝 0) (𝓝 (c, c)) := by
    have hc : Continuous (fun h : ℂ => (c + h, c)) :=
      (continuous_const.add continuous_id).prodMk continuous_const
    simpa only [add_zero] using hc.tendsto (0 : ℂ)
  obtain ⟨C, hC⟩ := (hp.isBigO_image_sub_norm_mul_norm_sub.comp_tendsto hmap).exists_nonneg
  obtain ⟨hC₀, hC⟩ := hC
  refine ⟨d • T, fun q hq => ?_⟩
  let b : ℝ≥0 := ⟨C, hC₀⟩
  refine ⟨b • q.comp T.toLinearMap, (hq.comp T.continuous).const_smul b, ?_⟩
  filter_upwards [hC.bound] with h hh x
  have hlinear : p 1 (fun _ => h) = h * d := by
    simp [d, FormalMultilinearSeries.apply_eq_prod_smul_coeff, smul_eq_mul]
  have hb : ‖a (c + h) - a c - h * d‖ ≤ C * ‖h‖ ^ 2 := by
    simpa only [Function.comp_apply, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
      add_sub_cancel_left, sub_self, hlinear, norm_zero, max_eq_left (norm_nonneg h),
      ← pow_two, Real.norm_of_nonneg (sq_nonneg ‖h‖)] using hh
  simp only [smul_apply, smul_smul, ← sub_smul, map_smul_eq_mul,
    Seminorm.comp_apply, NNReal.smul_def, smul_eq_mul]
  rw [mul_left_comm]
  change _ ≤ C * (‖h‖ ^ 2 * q (T x))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hb (apply_nonneg q (T x))

theorem finset_sum {ι : Type*} [IsTopologicalAddGroup F] (S : Finset ι)
    (A : ι → ℂ → E →L[ℂ] F)
    (h : ∀ i ∈ S, ∃ D, HasOperatorTaylorEstimate (A i) c D) :
    ∃ D, HasOperatorTaylorEstimate (fun z => ∑ i ∈ S, A i z) c D := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simpa using const (0 : E →L[ℂ] F) c⟩
  | @insert i S hi ih =>
    obtain ⟨D, hD⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨Q, hQ⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact ⟨D + Q, by simpa only [Finset.sum_insert hi] using hD.add hQ⟩

theorem smul_linear_factors {ι : Type*} [ContinuousConstSMul ℂ F] [IsTopologicalAddGroup F]
    (h : HasOperatorTaylorEstimate A c D) (S : Finset ι) (b : ι → ℂ) :
    ∃ D', HasOperatorTaylorEstimate (fun z => (∏ i ∈ S, (z + b i)) • A z) c D' := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨D, by simpa only [Finset.prod_empty, one_smul] using h⟩
  | @insert i S hi ih =>
    obtain ⟨Q, hQ⟩ := ih
    let I := ContinuousLinearMap.id ℂ F
    have hI : HasOperatorTaylorEstimate (fun z => (z + b i) • I) c I := by
      simpa only [add_smul, add_zero] using ((parameter I c).add (const (b i • I) c))
    refine ⟨_, (hI.comp hQ).congr (.of_forall fun z => ?_)⟩
    ext x
    simp only [ContinuousLinearMap.comp_apply, smul_apply, I, ContinuousLinearMap.id_apply,
      Finset.prod_insert hi, mul_smul]

theorem reparametrize [ContinuousConstSMul ℂ F] (a b : ℂ)
    (h : HasOperatorTaylorEstimate A (a * c + b) D) :
    HasOperatorTaylorEstimate (fun z => A (a * z + b)) c (a • D) := by
  intro q hq
  obtain ⟨p, hp, h⟩ := h q hq
  let C : ℝ≥0 := ‖a‖₊ ^ 2
  refine ⟨C • p, hp.const_smul C, ?_⟩
  have hcont : Tendsto (fun z : ℂ => a * z) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => a * z) := continuous_const.mul continuous_id
    simpa only [mul_zero] using hc.tendsto 0
  filter_upwards [hcont.eventually h] with z hz x
  have he : a * (c + z) + b = a * c + b + a * z := by ring
  simp only [he, smul_apply, smul_smul, mul_comm z a]
  exact (hz x).trans_eq (by
    rw [norm_mul]
    change (‖a‖ * ‖z‖) ^ 2 * p x = ‖z‖ ^ 2 * (‖a‖ ^ 2 * p x)
    ring)

theorem hasDerivAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {A : ℂ → E →L[ℂ] H} {D : E →L[ℂ] H} (ha : HasOperatorTaylorEstimate A c D) (x : E) :
    HasDerivAt (fun z => A z x) (D x) c := by
  obtain ⟨p, hp, h⟩ := ha (normSeminorm ℂ H) continuous_norm
  apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
  have hbig : (fun h : ℂ => A (c + h) x - A c x - h • D x) =O[𝓝 0] (fun h => ‖h‖ ^ 2) := by
    apply IsBigO.of_bound (p x)
    filter_upwards [h] with h hh
    simpa only [coe_normSeminorm, Real.norm_of_nonneg (sq_nonneg ‖h‖), mul_comm (p x)] using hh x
  exact hbig.trans_isLittleO (isLittleO_norm_pow_id (E' := ℂ) (by norm_num : 1 < 2))

/-- On a compact family of regular parameters a single continuous seminorm
bounds the whole operator family. -/
theorem compact_bound {K : Set ℂ} (hK : IsCompact K)
    (hA : ∀ z ∈ K, ∃ D, HasOperatorTaylorEstimate A z D)
    (q : Seminorm ℂ F) (hq : Continuous q) :
    ∃ p : Seminorm ℂ E, Continuous p ∧ ∀ z ∈ K, ∀ x, q (A z x) ≤ p x := by
  classical
  have hloc (z : K) : ∃ (p : Seminorm ℂ E) (U : Set ℂ),
      Continuous p ∧ IsOpen U ∧ z.val ∈ U ∧ ∀ w ∈ U, ∀ x, q (A w x) ≤ p x := by
    obtain ⟨D, hD⟩ := hA z z.property
    obtain ⟨p, hp, hb⟩ := hD.local_bounds q hq
    have hc : Continuous (fun w : ℂ => w - z.val) := continuous_id.sub continuous_const
    have ht : Tendsto (fun w : ℂ => w - z.val) (𝓝 z.val) (𝓝 0) := by
      simpa only [sub_self] using hc.tendsto z.val
    have hw := ht.eventually hb
    obtain ⟨U, hU, hUo, hz⟩ := mem_nhds_iff.mp hw
    refine ⟨p, U, hp, hUo, hz, fun w hw x => ?_⟩
    simpa only [add_sub_cancel, add_comm (z : ℂ) w] using ((hU hw) x).1
  choose p U hp hUo hz hU using hloc
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hUo (fun z hz' =>
    mem_iUnion.mpr ⟨⟨z, hz'⟩, hz ⟨z, hz'⟩⟩)
  use ∑ i ∈ s, p i
  refine ⟨?_, fun z hz x => ?_⟩
  · exact Seminorm.continuous_finsetSum (fun i _ => hp i)
  · obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hs hz)
    refine (hU i z hzi x).trans ?_
    change p i x ≤ FunLike.coeAddMonoidHom _ _ _ (∑ j ∈ s, p j) x
    simp_rw [map_sum, Finset.sum_apply]
    exact Finset.single_le_sum (fun j _ => apply_nonneg (p j) x) hi

theorem of_seminormFamily [IsTopologicalAddGroup E] {ι : Type*} {p : ι → Seminorm ℂ F} (hp : WithSeminorms p)
    (h : ∀ i, ∃ r : Seminorm ℂ E, Continuous r ∧ ∀ᶠ h : ℂ in 𝓝 0, ∀ x,
      p i (A (c + h) x - A c x - h • D x) ≤ ‖h‖ ^ 2 * r x) :
    HasOperatorTaylorEstimate A c D := by
  classical
  intro q hq
  obtain ⟨S, C, _, hC⟩ := Seminorm.bound_of_continuous hp q hq
  choose r hr hbound using h
  refine ⟨C • S.sup r, (Seminorm.continuous_finsetSup fun i _ => hr i).const_smul C, ?_⟩
  filter_upwards [S.eventually_all.mpr (fun i _ => hbound i)] with z hz x
  refine (hC _).trans ?_
  simp only [smul_apply, NNReal.smul_def, smul_eq_mul]
  rw [mul_left_comm (‖z‖ ^ 2) (C : ℝ)]
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  exact Seminorm.finset_sup_apply_le (by positivity) fun i hi =>
    (hz i hi x).trans (mul_le_mul_of_nonneg_left (Seminorm.le_finset_sup_apply hi) (sq_nonneg _))

end HasOperatorTaylorEstimate

end

end Masullo
