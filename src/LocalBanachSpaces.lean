import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.LocallyConvex.WithSeminorms

open Filter Function Set Topology UniformSpace

namespace Masullo

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The underlying vector space equipped with the topology of one seminorm. -/
def SeminormCarrier (_p : Seminorm ℂ E) := E

instance (p : Seminorm ℂ E) : SeminormedAddCommGroup (SeminormCarrier p) :=
  p.toAddGroupSeminorm.toSeminormedAddCommGroup

instance (p : Seminorm ℂ E) : Module ℂ (SeminormCarrier p) := inferInstanceAs (Module ℂ E)

instance (p : Seminorm ℂ E) : NormedSpace ℂ (SeminormCarrier p) where
  norm_smul_le a x := le_of_eq (map_smul_eq_mul p a x)

/-- The separated completion for the seminorm of a local Banach space. -/
abbrev LocalBanach (p : Seminorm ℂ E) := Completion (SeminormCarrier p)

def localBanachDenseMap (p : Seminorm ℂ E) : E →ₗ[ℂ] LocalBanach p :=
  (Completion.toComplL : SeminormCarrier p →L[ℂ] LocalBanach p).toLinearMap

theorem localBanachDenseMap_dense (p : Seminorm ℂ E) : DenseRange (localBanachDenseMap p) :=
  @Completion.denseRange_coe (SeminormCarrier p) _

@[simp] theorem norm_localBanachDenseMap (p : Seminorm ℂ E) (x : E) :
    ‖localBanachDenseMap p x‖ = p x :=
  @Completion.norm_coe (SeminormCarrier p) _ x

def localBanachMap [TopologicalSpace E] [IsTopologicalAddGroup E]
    (p : Seminorm ℂ E) (hp : Continuous p) : E →L[ℂ] LocalBanach p := by
  let L := localBanachDenseMap p
  refine ⟨L, continuous_of_tendsto_nhds_zero (G := E) (M := LocalBanach p) L.toAddMonoidHom ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(hp.tendsto' 0 0 (map_zero p)).eventually (Iio_mem_nhds hε)] with x hx
  change dist (localBanachDenseMap p x) 0 < ε
  rwa [dist_zero_right, norm_localBanachDenseMap]

private def seminormCarrierMap (p q : Seminorm ℂ E) (h : p ≤ q) :
    SeminormCarrier q →L[ℂ] SeminormCarrier p := by
  let L : SeminormCarrier q →ₗ[ℂ] SeminormCarrier p := LinearMap.id
  exact L.mkContinuous 1 (fun x => by
    change p x ≤ 1 * q x
    rw [one_mul]
    exact h x)

/-- The contraction between local Banach spaces induced by seminorm domination. -/
def localBanachTransition (p q : Seminorm ℂ E) (h : p ≤ q) :
    LocalBanach q →L[ℂ] LocalBanach p :=
  (Completion.toComplL.comp (seminormCarrierMap p q h)).extend Completion.toComplL

@[simp] theorem localBanachTransition_denseMap (p q : Seminorm ℂ E) (h : p ≤ q) (x : E) :
    localBanachTransition p q h (localBanachDenseMap q x) = localBanachDenseMap p x := by
  exact ((Completion.toComplL : SeminormCarrier p →L[ℂ] LocalBanach p).comp
    (seminormCarrierMap p q h)).extend_eq (e := Completion.toComplL)
      (@Completion.denseRange_coe (SeminormCarrier q) _)
      (Completion.isUniformInducing_coe (SeminormCarrier q)) x

theorem norm_localBanachTransition_le (p q : Seminorm ℂ E) (h : p ≤ q) (x : LocalBanach q) :
    ‖localBanachTransition p q h x‖ ≤ ‖x‖ := by
  have hc : IsClosed {z : LocalBanach q | ‖localBanachTransition p q h z‖ ≤ ‖z‖} :=
    isClosed_le (localBanachTransition p q h).continuous.norm continuous_norm
  refine hc.closure_subset_iff.mpr ?_ (localBanachDenseMap_dense q x)
  rintro _ ⟨y, rfl⟩
  change ‖localBanachTransition p q h (localBanachDenseMap q y)‖ ≤ ‖localBanachDenseMap q y‖
  rw [localBanachTransition_denseMap, norm_localBanachDenseMap, norm_localBanachDenseMap]
  exact h y

end

end Masullo
