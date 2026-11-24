import BruhatPettisConvolution
import ModulatedDecayComplete
import HardySobolevTranslations
import WeightedL2Coordinates

open Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (m : G →ₜ* Multiplicative ℝ)

local instance (I : Set ℝ) : IsTopologicalAddGroup (ModulatedExponentialInductive m I) :=
  (PolynormableSpace.withSeminorms ℂ (ModulatedExponentialInductive m I)).topologicalAddGroup

local instance (I : Set ℝ) : ContinuousSMul ℂ (ModulatedExponentialInductive m I) :=
  (PolynormableSpace.withSeminorms ℂ (ModulatedExponentialInductive m I)).continuousSMul

set_option maxHeartbeats 1800000 in
private theorem exists_decayPettisOrbit (I : Set ℝ) (hI : I.Nonempty)
    (hm : IsProperMap m) (hms : Surjective m)
    (φ : BruhatCompactTest G) (f : ModulatedExponentialInductive m I) :
    ∃ v, HasPositivePettisIntegral μ
      (fun g ↦ φ.val.val g • ModulatedExponentialInductive.translate m I g f) v := by
  obtain ⟨p, hp⟩ := exists_wholeBruhatStage_decay m I hm hms hI (ModulatedExponentialInductive.algebraicEquiv f)
  let u : WholeBruhatDecayStage m I p :=
    WholeBruhatDecayStage.algebraicEquiv.symm ⟨f.val, (Submodule.mem_iInf _).mpr hp⟩
  let E := WholeBruhatDecayStage m I p
  let j : E →L[ℂ] ModulatedExponentialInductive m I :=
    ⟨ModulatedExponentialInductive.stageMap p, ModulatedExponentialInductive.stageMap_continuous p⟩
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace E := WholeBruhatDecayStage.complete m I hI p
  letI : T2Space E := by
    letI : T2Space p.val.Space := (@elementarySchwartz_isFrechet
      p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank p.val.2.finiteFactor
      p.val.2.finiteGroup p.val.2.finiteTopology p.val.2.finiteDiscrete (Finite.of_fintype _)).1
    exact (WholeBruhatDecayStage.twistTuple_isClosedEmbedding m I hI p).isEmbedding.t2Space
  letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  letI : Module ℝ E := Module.compHom E Complex.ofRealHom
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let F (g : G) : E := φ.val.val g • WholeBruhatDecayStage.translate m I p g u
  have hF : Continuous F := (bruhatSchwartz_continuous φ.val).smul
    ((WholeBruhatDecayStage.continuous_translate m I p).comp (continuous_id.prodMk continuous_const))
  have hc : HasCompactSupport F := φ.property.mono (fun g hg ↦ by
    by_contra he
    exact hg (by change φ.val.val g • _ = 0; rw [show φ.val.val g = 0 from not_not.mp he, zero_smul]))
  obtain ⟨v, hv⟩ := exists_positivePettisIntegral_of_hasCompactSupport μ hF hc
  refine ⟨j v, fun ℓ ↦ ?_⟩
  have he (g : G) : j (F g) = φ.val.val g • ModulatedExponentialInductive.translate m I g f := by
    rw [show F g = φ.val.val g • WholeBruhatDecayStage.translate m I p g u from rfl, map_smul]
    congr 1
  simpa only [ContinuousLinearMap.comp_apply, Function.comp_def, he] using hv (ℓ.comp j)

set_option maxHeartbeats 2000000 in
/-- The decay-space clause of Lemma 9.3.1.3 on the inductive topology
of the actual weighted Schwartz–Bruhat stages. -/
theorem exists_modulatedDecayPettisConvolution (I : Set ℝ) (hI : I.Nonempty)
    (hm : IsProperMap m) (hms : Surjective m) :
    let E := ModulatedExponentialInductive m I
    ∃ A : BruhatCompactTest G →L[ℂ] (E →L[ℂ] E),
      ∀ φ f, HasPositivePettisIntegral μ
        (fun g ↦ φ.val.val g • ModulatedExponentialInductive.translate m I g f) (A φ f) := by
  let E := ModulatedExponentialInductive m I
  letI : T2Space E := ModulatedExponentialInductive.t2 m I hI
  letI : Module ℝ E := Module.compHom E Complex.ofRealHom
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact exists_bruhatPettisConvolution μ (ModulatedExponentialInductive.translate m I)
    (ModulatedExponentialInductive.continuous_translate m I hm hms hI)
    (exists_decayPettisOrbit μ m I hI hm hms)

private theorem exists_hilbertPettisConvolution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : G → E →L[ℂ] E) (hT : Continuous fun z : G × E ↦ T z.1 z.2) :
    ∃ A : BruhatCompactTest G →L[ℂ] (E →L[ℂ] E),
      ∀ φ f, HasPositivePettisIntegral μ (fun g ↦ φ.val.val g • T g f) (A φ f) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine exists_bruhatPettisConvolution (E := E) μ (fun g ↦ (T g).toLinearMap) hT ?_
  intro φ f
  let F (g : G) : E := φ.val.val g • T g f
  have hF : Continuous F := (bruhatSchwartz_continuous φ.val).smul
    (hT.comp (continuous_id.prodMk continuous_const))
  have hc : HasCompactSupport F := φ.property.mono (fun g hg ↦ by
    by_contra he
    exact hg (by change φ.val.val g • _ = 0; rw [show φ.val.val g = 0 from not_not.mp he, zero_smul]))
  exact exists_positivePettisIntegral_of_hasCompactSupport μ hF hc

omit [IsFiniteMeasureOnCompacts μ] in
set_option maxHeartbeats 1600000 in
private theorem amplitude_conjugate_leftShift
    [μ.IsHaarMeasure] (a b s : ℝ) (hs : 0 ≤ s)
    (r : G → ℝ) (hr : Measurable r) (hpos : ∀ g, 0 < r g)
    (he : ∀ g : G, r g = hardySobolevAmplitude a b s (m g).toAdd)
    (g : G) (f : Lp ℂ 2 (amplitudeMeasure μ r)) :
    let U := amplitudeL2Iso μ r hr hpos
    let S := hardySobolevMulTranslation μ m.toMonoidHom m.continuous a b s hs
    (U.symm (S g (U f)) : G → ℂ) =ᵐ[amplitudeMeasure μ r] fun x ↦ f (g⁻¹ * x) := by
  let U := amplitudeL2Iso μ r hr hpos
  let S := hardySobolevMulTranslation μ m.toMonoidHom m.continuous a b s hs
  have hm := amplitudeMeasure_absolutelyContinuous μ r
  filter_upwards [amplitudeL2Iso_symm_ae μ r hr hpos (S g (U f)),
    hm.ae_le (hardySobolevMulTranslation_ae μ m.toMonoidHom m.continuous a b s hs g (U f)),
    hm.ae_le ((measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp
      (amplitudeL2Iso_ae μ r hr hpos f))] with x hx hy hz
  change (U.symm (S g (U f)) : G → ℂ) x = _
  change (U.symm (S g (U f)) : G → ℂ) x = (r x)⁻¹ • (S g (U f) : G → ℂ) x at hx
  change (S g (U f) : G → ℂ) x =
    ((hardySobolevAmplitude a b s (m x).toAdd /
      hardySobolevAmplitude a b s (m (g⁻¹ * x)).toAdd : ℝ) : ℂ) * (U f : G → ℂ) (g⁻¹ * x) at hy
  change (U f : G → ℂ) (g⁻¹ * x) = r (g⁻¹ * x) • f (g⁻¹ * x) at hz
  rw [← he, ← he] at hy
  rw [hx, hy, hz, ← Complex.real_smul, smul_smul (r x / r (g⁻¹ * x : G)),
    div_mul_cancel₀ _ (hpos _).ne', inv_smul_smul₀ (hpos x).ne']

private def weightedPettisActionExists (ν : Measure G) : Prop :=
  let E := Lp ℂ 2 ν
  ∃ T : G → E →L[ℂ] E, (∀ g f, (T g f : G → ℂ) =ᵐ[ν] fun x ↦ f (g⁻¹ * x)) ∧
    ∃ A : BruhatCompactTest G →L[ℂ] (E →L[ℂ] E),
      ∀ φ f, HasPositivePettisIntegral μ (fun g ↦ φ.val.val g • T g f) (A φ f)

private theorem continuous_conjugate_action {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : E ≃L[ℂ] F) (S : G → F →L[ℂ] F)
    (hS : Continuous (fun z : G × F ↦ S z.1 z.2)) :
    Continuous (fun z : G × E ↦ (U.symm.toContinuousLinearMap.comp
      ((S z.1).comp U.toContinuousLinearMap)) z.2) := by
  change Continuous (fun z : G × E ↦ U.symm (S z.1 (U z.2)))
  exact U.symm.continuous.comp (hS.comp (continuous_fst.prodMk (U.continuous.comp continuous_snd)))

omit [IsFiniteMeasureOnCompacts μ] in
set_option maxHeartbeats 1900000 in
private theorem weightedPettisActionExists_amplitude
    [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop] (a b s : ℝ) (hs : 0 ≤ s)
    (r : G → ℝ) (hr : Measurable r) (hpos : ∀ g, 0 < r g)
    (he : ∀ g : G, r g = hardySobolevAmplitude a b s (m g).toAdd) :
    weightedPettisActionExists μ (amplitudeMeasure μ r) := by
  let E : Type _ := Lp ℂ 2 (amplitudeMeasure μ r)
  let U : E ≃ₗᵢ[ℂ] Lp ℂ 2 μ := amplitudeL2Iso μ r hr hpos
  let S := hardySobolevMulTranslation μ m.toMonoidHom m.continuous a b s hs
  let T (g : G) : E →L[ℂ] E :=
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((S g).comp U.toContinuousLinearEquiv.toContinuousLinearMap)
  have hS := continuous_hardySobolevMulTranslation μ m.toMonoidHom m.continuous a b s hs
  have hT : Continuous (fun z : G × E ↦ T z.1 z.2) :=
    continuous_conjugate_action U.toContinuousLinearEquiv S hS
  have hshift (g : G) (f : E) : (T g f : G → ℂ) =ᵐ[amplitudeMeasure μ r] fun x ↦ f (g⁻¹ * x) :=
    amplitude_conjugate_leftShift μ m a b s hs r hr hpos he g f
  have hA := exists_hilbertPettisConvolution (E := E) μ T hT
  exact ⟨T, hshift, hA⟩

omit [IsFiniteMeasureOnCompacts μ] in
set_option maxHeartbeats 1400000 in
/-- The compact-interval convolution acts on the actual weighted Haar
space. The associated translations have the usual left-shift representatives. -/
theorem exists_weightedHardySobolevPettisConvolution
    [μ.IsHaarMeasure] [μ.InnerRegularCompactLTTop] (a b s : ℝ) (hs : 0 ≤ s) :
    let l (g : G) := (m g).toAdd
    let E := Lp ℂ 2 (hardySobolevMeasure μ l a b s)
    ∃ T : G → E →L[ℂ] E, (∀ g f, (T g f : G → ℂ) =ᵐ[hardySobolevMeasure μ l a b s]
      fun x ↦ f (g⁻¹ * x)) ∧
      ∃ A : BruhatCompactTest G →L[ℂ] (E →L[ℂ] E),
        ∀ φ f, HasPositivePettisIntegral μ (fun g ↦ φ.val.val g • T g f) (A φ f) := by
  let l (g : G) := (m g).toAdd
  let r (g : G) := hardySobolevAmplitude a b s (l g)
  have hpos (g : G) : 0 < r g := by
    apply Real.sqrt_pos.2
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _))
      (Real.rpow_pos_of_pos (by positivity) _)
  have hr : Measurable r :=
    (Real.continuous_sqrt.comp ((continuous_hardySobolevWeight a b s).comp m.continuous)).measurable
  have hmeasure : hardySobolevMeasure μ l a b s = amplitudeMeasure μ r := by
    unfold hardySobolevMeasure amplitudeMeasure
    congr 1
    funext x
    exact congrArg ENNReal.ofReal (Real.sq_sqrt (hardySobolevWeight_nonneg ..)).symm
  change weightedPettisActionExists μ (hardySobolevMeasure μ l a b s)
  rw [hmeasure]
  exact weightedPettisActionExists_amplitude μ m a b s hs r hr hpos (fun _ ↦ rfl)

end
end Masullo
