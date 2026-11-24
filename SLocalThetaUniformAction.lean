import ThetaTranslationContinuity
import SLocalThetaSmallNorm
import Mathlib.Topology.UniformSpace.UniformConvergence

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField Uniformity

namespace Masullo

noncomputable section

/-- A jointly continuous family of continuous linear maps with compact
parameter space takes convergent nets to uniformly convergent orbit maps. -/
theorem tendstoUniformly_of_continuousLinearFamily_compact
    {G E ι : Type*} [TopologicalSpace G] [CompactSpace G]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    (A : G → E →L[ℂ] E) (hA : Continuous (fun z : G × E => A z.1 z.2))
    {l : Filter ι} {f : ι → E} {x : E} (hf : Tendsto f l (𝓝 x)) :
    TendstoUniformly (fun i g => A g (f i)) (fun g => A g x) l := by
  intro W hW
  rw [uniformity_eq_comap_nhds_zero E] at hW
  obtain ⟨U, hU, hUW⟩ := Filter.mem_comap.mp hW
  have hzero : ∀ᶠ v in 𝓝 (0 : E), ∀ g : G, A g v ∈ U := by
    have hlocal (g : G) : ∀ᶠ z : E × G in 𝓝 ((0 : E), g), A z.2 z.1 ∈ U := by
      have hc : Continuous (fun z : E × G => A z.2 z.1) :=
        hA.comp (continuous_snd.prodMk continuous_fst)
      exact (hc.tendsto' (0, g) 0 (map_zero _)).eventually hU
    simpa only [mem_univ, true_implies] using
      (isCompact_univ : IsCompact (univ : Set G)).eventually_forall_of_forall_eventually
        (fun g _ => hlocal g)
  have hd : Tendsto (fun i => f i - x) l (𝓝 0) := by
    have hx : Tendsto (fun _ : ι => x) l (𝓝 x) := tendsto_const_nhds
    simpa only [sub_self] using hf.sub hx
  filter_upwards [hd.eventually hzero] with i hi g
  apply hUW
  change A g (f i) - A g x ∈ U
  rw [← map_sub]
  exact hi g

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Theta := SLocalThetaQuotient F S
private abbrev NormOne := SLocalThetaNormOne F S

local instance : UniformSpace (Theta F S) := IsTopologicalAddGroup.rightUniformSpace _
local instance : IsUniformAddGroup (Theta F S) := isUniformAddGroup_of_addCommGroup

/-- Lemma 6.2.1.3(1). Convergence in the actual S-local theta quotient
implies uniform convergence of its translates over the norm-one group. -/
theorem sLocalThetaTranslate_tendstoUniformly {ι : Type*} {l : Filter ι}
    {f : ι → Theta F S} {x : Theta F S} (hf : Tendsto f l (𝓝 x)) :
    TendstoUniformly (fun i (g : NormOne F S) => sLocalThetaTranslate F S g.val (f i))
      (fun g : NormOne F S => sLocalThetaTranslate F S g.val x) l := by
  letI : CompactSpace (NormOne F S) := sLocalThetaNormOne_compact F S
  exact tendstoUniformly_of_continuousLinearFamily_compact
    (fun g : NormOne F S => sLocalThetaTranslate F S g.val)
    ((continuous_sLocalThetaTranslate F S).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) hf

/-- Lemma 6.2.1.3(2). Character twists preserve uniform convergence of
the translated net on the compact norm-one group. -/
theorem sLocalThetaTranslate_twist_tendstoUniformly {ι : Type*} {l : Filter ι}
    (χ : PontryaginDual (NormOne F S))
    {f : ι → Theta F S} {x : Theta F S} (hf : Tendsto f l (𝓝 x)) :
    TendstoUniformly (fun i g => (χ g : ℂ) • sLocalThetaTranslate F S g.val (f i))
      (fun g => (χ g : ℂ) • sLocalThetaTranslate F S g.val x) l := by
  letI : CompactSpace (NormOne F S) := sLocalThetaNormOne_compact F S
  have hχ : Continuous (fun z : NormOne F S × Theta F S => (χ z.1 : ℂ)) :=
    continuous_subtype_val.comp (χ.continuous.comp continuous_fst)
  have hA : Continuous (fun z : NormOne F S × Theta F S => sLocalThetaTranslate F S z.1.val z.2) :=
    (continuous_sLocalThetaTranslate F S).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  exact tendstoUniformly_of_continuousLinearFamily_compact
    (fun g => (χ g : ℂ) • sLocalThetaTranslate F S g.val) (hχ.smul hA) hf

end
end Masullo
