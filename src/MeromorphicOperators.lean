import OperatorTaylorEstimate
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic

open Filter Set
open scoped Topology

namespace Masullo

section

variable {E F G : Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]

/-- An operator family has a nonzero local analytic denominator and a
numerator differentiable with quadratic control in continuous seminorms. -/
def MeromorphicOperator [ContinuousConstSMul ℂ F] (A : ℂ → E →L[ℂ] F) : Prop :=
  ∀ c : ℂ, ∃ (p : ℂ → ℂ) (N : ℂ → E →L[ℂ] F),
    AnalyticAt ℂ p c ∧ (∀ᶠ z in 𝓝[≠] c, p z ≠ 0) ∧
      (∀ᶠ z in 𝓝[≠] c, N z = p z • A z) ∧
      ∀ᶠ z in 𝓝 c, ∃ D, HasOperatorTaylorEstimate N z D

namespace MeromorphicOperator

theorem const [ContinuousConstSMul ℂ F] (T : E →L[ℂ] F) :
    MeromorphicOperator (fun _ => T) := by
  intro c
  exact ⟨fun _ => 1, fun _ => T, analyticAt_const,
    .of_forall fun _ => one_ne_zero, .of_forall fun _ => (one_smul ℂ T).symm,
    .of_forall fun z => ⟨0, HasOperatorTaylorEstimate.const T z⟩⟩

theorem comp [IsTopologicalAddGroup G] [ContinuousConstSMul ℂ G] [ContinuousConstSMul ℂ F]
    {A : ℂ → F →L[ℂ] G} {B : ℂ → E →L[ℂ] F}
    (hA : MeromorphicOperator A) (hB : MeromorphicOperator B) :
    MeromorphicOperator (fun z => (A z).comp (B z)) := by
  intro c
  obtain ⟨p, N, hp, hp₀, hN, hDN⟩ := hA c
  obtain ⟨q, M, hq, hq₀, hM, hDM⟩ := hB c
  refine ⟨fun z => p z * q z, fun z => (N z).comp (M z), hp.mul hq,
    (hp₀.and hq₀).mono fun _ h => mul_ne_zero h.1 h.2, ?_, ?_⟩
  · filter_upwards [hN, hM] with z hN hM
    rw [hN, hM]
    ext x
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul, mul_smul]
    rw [smul_comm (p z) (q z)]
  · filter_upwards [hDN, hDM] with z hN hM
    obtain ⟨_, hN⟩ := hN
    obtain ⟨_, hM⟩ := hM
    exact ⟨_, hN.comp hM⟩

theorem translate [ContinuousConstSMul ℂ F] {A : ℂ → E →L[ℂ] F}
    (hA : MeromorphicOperator A) (b : ℂ) :
    MeromorphicOperator (fun z => A (z + b)) := by
  intro c
  obtain ⟨p, N, hp, hp₀, hN, hDN⟩ := hA (c + b)
  have hT : Tendsto (fun z : ℂ => z + b) (𝓝 c) (𝓝 (c + b)) :=
    (continuous_id.add continuous_const).tendsto c
  have hP : Tendsto (fun z : ℂ => z + b) (𝓝[≠] c) (𝓝[≠] (c + b)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hT.mono_left nhdsWithin_le_nhds, ?_⟩
    have hmem : ∀ᶠ z : ℂ in 𝓝[≠] c, z ∈ ({c} : Set ℂ)ᶜ :=
      self_mem_nhdsWithin (s := ({c} : Set ℂ)ᶜ)
    exact hmem.mono (fun z hz => by
      simpa only [mem_compl_iff, mem_singleton_iff, add_left_inj] using hz)
  have hShift : AnalyticAt ℂ (fun z : ℂ => z + b) c := analyticAt_id.add analyticAt_const
  refine ⟨fun z => p (z + b), fun z => N (z + b),
    hp.comp (f := fun z : ℂ => z + b) (x := c) hShift, hP.eventually hp₀, hP.eventually hN, ?_⟩
  filter_upwards [hT.eventually hDN] with z hz
  obtain ⟨D, hD⟩ := hz
  have hD' : HasOperatorTaylorEstimate N (1 * z + b) D := by simpa only [one_mul] using hD
  exact ⟨D, by simpa only [one_mul, one_smul] using hD'.reparametrize (c := z) 1 b⟩

theorem apply_meromorphic {A : ℂ → E →L[ℂ] ℂ}
    (hA : MeromorphicOperator A) (x : E) : Meromorphic (fun z => A z x) := by
  intro c
  obtain ⟨p, N, hp, hp₀, hN, hDN⟩ := hA c
  have hDiff : DifferentiableOn ℂ (fun z => N z x)
      {z | ∃ D, HasOperatorTaylorEstimate N z D} := by
    rintro z ⟨D, hD⟩
    exact (hD.hasDerivAt x).differentiableAt.differentiableWithinAt
  have hAna := hDiff.analyticAt hDN
  apply (hAna.meromorphicAt.div hp.meromorphicAt).congr
  filter_upwards [hp₀, hN] with z hz hw
  simp only [Pi.div_apply, hw, smul_apply, smul_eq_mul]
  exact (mul_div_cancel_left₀ _ hz)

end MeromorphicOperator

end

end Masullo
