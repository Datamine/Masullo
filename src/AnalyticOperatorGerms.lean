import MeromorphicOperators
import Mathlib.Analysis.Meromorphic.Order

open Filter Set
open scoped Topology

namespace Masullo

section

variable {E F G : Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]

/-- The operator family on punctured neighborhoods is given by a family with
continuous-seminorm Taylor estimates throughout a neighborhood of the center. -/
def AnalyticOperatorGerm (A : ℂ → E →L[ℂ] F) (c : ℂ) : Prop :=
  ∃ N : ℂ → E →L[ℂ] F, A =ᶠ[𝓝[≠] c] N ∧
    ∀ᶠ z in 𝓝 c, ∃ D, HasOperatorTaylorEstimate N z D

namespace AnalyticOperatorGerm

variable {c : ℂ}

theorem of_taylor {A : ℂ → E →L[ℂ] F}
    (h : ∀ᶠ z in 𝓝 c, ∃ D, HasOperatorTaylorEstimate A z D) :
    AnalyticOperatorGerm A c :=
  ⟨A, EventuallyEq.rfl, h⟩

theorem congr {A B : ℂ → E →L[ℂ] F} (h : AnalyticOperatorGerm A c)
    (he : B =ᶠ[𝓝[≠] c] A) : AnalyticOperatorGerm B c := by
  obtain ⟨N, hN, hd⟩ := h
  exact ⟨N, he.trans hN, hd⟩

theorem const (T : E →L[ℂ] F) : AnalyticOperatorGerm (fun _ => T) c :=
  of_taylor (.of_forall fun z => ⟨0, HasOperatorTaylorEstimate.const T z⟩)

theorem add [IsTopologicalAddGroup F] {A B : ℂ → E →L[ℂ] F}
    (hA : AnalyticOperatorGerm A c) (hB : AnalyticOperatorGerm B c) :
    AnalyticOperatorGerm (fun z => A z + B z) c := by
  obtain ⟨N, hN, hd⟩ := hA
  obtain ⟨M, hM, he⟩ := hB
  refine ⟨fun z => N z + M z, ?_, ?_⟩
  · filter_upwards [hN, hM] with z hz hw
    rw [hz, hw]
  · filter_upwards [hd, he] with z hz hw
    obtain ⟨_, h⟩ := hz
    obtain ⟨_, h'⟩ := hw
    exact ⟨_, h.add h'⟩

theorem comp [IsTopologicalAddGroup G] {A : ℂ → F →L[ℂ] G} {B : ℂ → E →L[ℂ] F}
    (hA : AnalyticOperatorGerm A c) (hB : AnalyticOperatorGerm B c) :
    AnalyticOperatorGerm (fun z => (A z).comp (B z)) c := by
  obtain ⟨N, hN, hd⟩ := hA
  obtain ⟨M, hM, he⟩ := hB
  refine ⟨fun z => (N z).comp (M z), ?_, ?_⟩
  · filter_upwards [hN, hM] with z hz hw
    rw [hz, hw]
  · filter_upwards [hd, he] with z hz hw
    obtain ⟨_, h⟩ := hz
    obtain ⟨_, h'⟩ := hw
    exact ⟨_, h.comp h'⟩

theorem smul [IsTopologicalAddGroup F] [ContinuousConstSMul ℂ F]
    {A : ℂ → E →L[ℂ] F} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g c) (h : AnalyticOperatorGerm A c) :
    AnalyticOperatorGerm (fun z => g z • A z) c := by
  have hS : AnalyticOperatorGerm (fun z => g z • ContinuousLinearMap.id ℂ F) c :=
    of_taylor (hg.eventually_analyticAt.mono fun _ h => HasOperatorTaylorEstimate.analytic_smul_fixed h _)
  apply (hS.comp h).congr (.of_forall fun z => ?_)
  ext x
  rfl

theorem finset_sum [IsTopologicalAddGroup F] {ι : Type*} (s : Finset ι)
    {A : ι → ℂ → E →L[ℂ] F} (h : ∀ i ∈ s, AnalyticOperatorGerm (A i) c) :
    AnalyticOperatorGerm (fun z => ∑ i ∈ s, A i z) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using const (c := c) (0 : E →L[ℂ] F)
  | @insert i s hi ih =>
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
      |>.congr (.of_forall fun z => Finset.sum_insert hi)

theorem affine [ContinuousConstSMul ℂ F] {A : ℂ → E →L[ℂ] F} (a b : ℂ)
    (ha : a ≠ 0) (h : AnalyticOperatorGerm A (a * c + b)) :
    AnalyticOperatorGerm (fun z => A (a * z + b)) c := by
  obtain ⟨N, hN, hd⟩ := h
  let e (z : ℂ) := a * z + b
  have hc : Continuous e := continuous_const.mul continuous_id |>.add continuous_const
  have hT : Tendsto e (𝓝 c) (𝓝 (e c)) := hc.tendsto c
  have hP : Tendsto e (𝓝[≠] c) (𝓝[≠] (e c)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hT.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin (s := ({c} : Set ℂ)ᶜ)] with z hz
    simpa only [e, mem_compl_iff, mem_singleton_iff, add_left_inj,
      mul_right_inj' ha] using hz
  refine ⟨fun z => N (e z), hP.eventually hN, ?_⟩
  filter_upwards [hT.eventually hd] with z hz
  obtain ⟨_, hD⟩ := hz
  exact ⟨_, hD.reparametrize a b⟩

theorem translate [ContinuousConstSMul ℂ F] {A : ℂ → E →L[ℂ] F} (b : ℂ)
    (h : AnalyticOperatorGerm A (c + b)) :
    AnalyticOperatorGerm (fun z => A (z + b)) c := by
  have he : AnalyticOperatorGerm A (1 * c + b) := by simpa only [one_mul] using h
  apply (he.affine 1 b one_ne_zero).congr (.of_forall fun z => ?_)
  change A (z + b) = A (1 * z + b)
  rw [one_mul]

theorem smul_comp_const [IsTopologicalAddGroup G] [ContinuousConstSMul ℂ G]
    {A : ℂ → F →L[ℂ] G} {d : ℂ → ℂ} (h : AnalyticOperatorGerm (fun z => d z • A z) c)
    (T : E →L[ℂ] F) :
    AnalyticOperatorGerm (fun z => d z • (A z).comp T) c :=
  (h.comp (.const T)).congr (.of_forall fun _ => by ext; rfl)

theorem comp_mul_smul [IsTopologicalAddGroup G] [ContinuousConstSMul ℂ F]
    [ContinuousConstSMul ℂ G] {A : ℂ → F →L[ℂ] G} {B : ℂ → E →L[ℂ] F}
    {d e : ℂ → ℂ} (hA : AnalyticOperatorGerm (fun z => d z • A z) c)
    (hB : AnalyticOperatorGerm (fun z => e z • B z) c) :
    AnalyticOperatorGerm (fun z => (d z * e z) • (A z).comp (B z)) c := by
  apply (hA.comp hB).congr (.of_forall fun z => ?_)
  ext x
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul, mul_smul]
  rw [smul_comm]

theorem apply_exists_analytic {A : ℂ → E →L[ℂ] ℂ} (h : AnalyticOperatorGerm A c) (x : E) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧ (fun z => A z x) =ᶠ[𝓝[≠] c] g := by
  obtain ⟨N, hN, hd⟩ := h
  refine ⟨fun z => N z x, ?_, hN.mono fun _ hz => congrArg (fun D : E →L[ℂ] ℂ => D x) hz⟩
  have hDiff : DifferentiableOn ℂ (fun z => N z x)
      {z | ∃ D, HasOperatorTaylorEstimate N z D} := by
    rintro z ⟨D, hD⟩
    exact (hD.hasDerivAt x).differentiableAt.differentiableWithinAt
  exact hDiff.analyticAt hd

end AnalyticOperatorGerm
end
end Masullo
