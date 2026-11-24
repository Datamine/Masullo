import SLocalThetaDualGeneration
import CompactGroupAveraging
import CompactCharacterCompleteness
import LCAFourierIntegral
import FiniteLocalZeta

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField

namespace Masullo

noncomputable section

set_option maxHeartbeats 950000

universe u

variable (F : Type u) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F
private abbrev U := ↥(principalIntegralUnits F v)
private abbrev E := ↥(locallyConstantTests (K F v))

local instance : MeasurableSpace (K F v)ˣ := borel _
local instance : BorelSpace (K F v)ˣ := ⟨rfl⟩
local instance : MeasurableSpace (U F v) := borel _
local instance : BorelSpace (U F v) := ⟨rfl⟩
local instance : CompactSpace (U F v) := principalIntegralUnits_compactSpace F v
local instance : TopologicalSpace (E F v) := finestLocallyConvexTopology _
local instance : IsTopologicalAddGroup (E F v) := (finest_withSeminorms _).topologicalAddGroup
local instance : ContinuousSMul ℂ (E F v) := (finest_withSeminorms (E F v)).continuousSMul
local instance : PolynormableSpace ℂ (E F v) := (finest_withSeminorms _).toPolynormableSpace

variable (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]

/-- Evaluate the pole-cleared finite zeta distribution at real Mellin weight one. -/
def finiteLocalMellinEval (μ : Measure (K F v)ˣ) [μ.IsHaarMeasure]
    (χ : PontryaginDual (K F v)ˣ) : StrongDual ℂ (E F v) :=
  finiteZetaClearedDistribution F v μ χ 1

private theorem finiteLocalMellinEval_separates (f : E F v)
    (h : ∀ χ, finiteLocalMellinEval F v μ χ f = 0) : f = 0 := by
  let φ (a : (K F v)ˣ) : ℂ := f.val a.val * finiteZetaWeight F v 1 a
  letI : LocallyCompactSpace (K F v) := finitePlace_locallyCompact F v
  letI : LocallyCompactSpace (K F v)ˣ := inferInstance
  letI : SecondCountableTopology (K F v) := finitePlace_secondCountable F v
  letI : SecondCountableTopology (K F v)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hφ : Integrable φ μ := by
    have h := (finiteZetaContinuation_eq_integral F v μ
      (1 : PontryaginDual (K F v)ˣ) f 1 (by norm_num)).1
    apply h.congr
    exact .of_forall fun a ↦ by
      change f.val a.val * (1 : ℂ) * finiteZetaWeight F v 1 a = φ a
      rw [mul_one]
  have hφcont : Continuous φ := by
    have hf := f.property.1.continuous.comp (Units.continuous_val (M := K F v))
    have hn : Continuous (fun a : (K F v)ˣ ↦ ‖a.val‖) :=
      continuous_norm.comp Units.continuous_val
    apply hf.mul
    unfold finiteZetaWeight
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (hn.log fun a ↦ norm_ne_zero_iff.mpr a.ne_zero)))
  have hz : φ =ᵐ[μ] 0 := by
    apply ae_eq_zero_of_lcaFourier_eq_zero μ hφ
    intro χ
    have heq := finiteZetaClearedDistribution_eq_mul_integral F v μ χ⁻¹ f 1 (by norm_num)
    have he := heq.symm.trans (h χ⁻¹)
    have hi := (mul_eq_zero.mp he).resolve_right (finiteZetaDenominator_ne_zero_of_pos F v χ⁻¹ 1
      (by norm_num))
    refine (integral_congr_ae (.of_forall fun a ↦ ?_)).trans hi
    change φ a * star (χ a : ℂ) = f.val a.val * ((χ⁻¹ a : Circle) : ℂ) *
      finiteZetaWeight F v 1 a
    rw [show χ⁻¹ a = (χ a)⁻¹ from rfl, Circle.coe_inv_eq_conj]
    dsimp [φ]
    ring
  have he := Measure.eq_of_ae_eq hz hφcont continuous_const
  have hnonzero (x : K F v) (hx : x ≠ 0) : f.val x = 0 := by
    have hzero := congrFun he (Units.mk0 x hx)
    change f.val x * finiteZetaWeight F v 1 (Units.mk0 x hx) = 0 at hzero
    exact (mul_eq_zero.mp hzero).resolve_right (Complex.exp_ne_zero _)
  apply Subtype.ext
  funext x
  have hf : Continuous f.val := f.property.1.continuous
  have hclosed := isClosed_eq hf (continuous_const (y := (0 : ℂ)))
  let π := chosenFiniteUniformizer F v
  have hπ := norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  letI : NontriviallyNormedField (K F v) :=
    ⟨⟨((π : K F v)⁻¹), by rw [norm_inv, hπ, inv_inv]; exact hq⟩⟩
  have hd := dense_compl_singleton (0 : K F v)
  exact hclosed.closure_subset_iff.mpr
    (show ({0} : Set (K F v))ᶜ ⊆ {x | f.val x = 0} from fun x hx ↦ hnonzero x (by simpa using hx))
    (by rw [hd.closure_eq]; trivial)

/-- The pole-cleared finite Mellin functional is an eigendistribution for every local unit. -/
theorem finiteLocalMellinEval_translate (χ : PontryaginDual (K F v)ˣ)
    (g : (K F v)ˣ) (f : E F v) :
    finiteLocalMellinEval F v μ χ (locallyConstantTestTranslate (K F v) g f) =
      ((χ g : ℂ) * finiteZetaWeight F v 1 g) * finiteLocalMellinEval F v μ χ f := by
  simp only [finiteLocalMellinEval, finiteZetaClearedDistribution_eq_mul_integral F v μ χ _ 1
    (by norm_num)]
  rw [finiteZetaIntegral_translate F v μ χ 1 g f, mul_assoc]
  rfl

/-- The fixed positive Mellin line, parametrized by all unitary characters,
strongly generates the finite-place distribution space. -/
theorem finiteLocalMellin_strongSpan :
    closure (Submodule.span ℂ (range (finiteLocalMellinEval F v μ)) :
      Set (StrongDual ℂ (E F v))) = univ := by
  let b := Module.Free.chooseBasis ℂ (E F v)
  rw [strongDual_closure_span_eq_annihilator (finest_strongBidual b)
    (finest_strongBidual_apply b) _ ⊥]
  · ext T
    simp
  · intro f
    simp only [Submodule.mem_bot]
    exact ⟨fun h χ ↦ by rw [h, map_zero], finiteLocalMellinEval_separates F v μ f⟩

/-- The integral-unit action on the finest locally convex test space. -/
def finiteLocalUnitAction : U F v →* (E F v →L[ℂ] E F v) where
  toFun u := ⟨principalUnitAction F v u, finest_linear_continuous (principalUnitAction F v u)⟩
  map_one' := by
    apply ContinuousLinearMap.ext
    intro f
    change principalUnitAction F v 1 f = f
    rw [map_one]
    rfl
  map_mul' a b := by
    apply ContinuousLinearMap.ext
    intro f
    change principalUnitAction F v (a * b) f = principalUnitAction F v a (principalUnitAction F v b f)
    rw [map_mul]
    rfl

private theorem finiteLocalMellinEval_unit (χ : PontryaginDual (K F v)ˣ) (a : U F v) (f : E F v) :
    finiteLocalMellinEval F v μ χ (finiteLocalUnitAction F v a f) =
      (χ a.val : ℂ) * finiteLocalMellinEval F v μ χ f := by
  have H : ‖a.val.val‖ = 1 := a.property
  exact (finiteLocalMellinEval_translate F v μ χ a.val f).trans (by simp [finiteZetaWeight, H])

/-- Restriction of a unitary local character to the integral units. -/
def finiteLocalRestrict (χ : PontryaginDual (K F v)ˣ) : PontryaginDual (U F v) :=
  χ.comp ⟨(principalIntegralUnits F v).subtype, continuous_subtype_val⟩

variable (ω : PontryaginDual (U F v))

private theorem finiteLocalMellin_component_kernel :
    ∃ P : E F v →L[ℂ] E F v,
      (∀ f, P f = 0 ↔ ∀ χ, finiteLocalRestrict F v χ = ω → finiteLocalMellinEval F v μ χ f = 0) ∧
      {T : StrongDual ℂ (E F v) | ∀ f ∈ P.ker, T f = 0} =
        {T : StrongDual ℂ (E F v) | ∀ (a : U F v) f,
          T (finiteLocalUnitAction F v a f) = (ω a : ℂ) * T f} := by
  classical
  let W := finest_withSeminorms (E F v)
  letI : Module ℝ (E F v) := Module.restrictScalars ℝ ℂ (E F v)
  letI : IsScalarTower ℝ ℂ (E F v) := IsScalarTower.restrictScalars ℝ ℂ (E F v)
  letI : LocallyConvexSpace ℝ (E F v) := W.toLocallyConvexSpace
  letI : UniformSpace (E F v) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (E F v) := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace (E F v) := finest_complete _
  letI : T2Space (E F v) := finest_t2 _
  letI : BarrelledSpace ℂ (E F v) := finest_barrelled
  let ν := principalUnitHaar F v
  have hρ : Continuous (fun z : U F v × E F v ↦ finiteLocalUnitAction F v z.1 z.2) :=
    continuous_joint_of_barrelled (finiteLocalUnitAction F v)
      (fun f ↦ (principalUnitAction_orbit F v f).continuous)
  obtain ⟨_, P, hP, _, _, _, _, hker⟩ :=
    compactGroupIsotypicAverage (finiteLocalUnitAction F v) hρ ω.toMonoidHom ω.continuous ν
  have hcoeff (χ : PontryaginDual (K F v)ˣ) (f : E F v) :
      finiteLocalMellinEval F v μ χ (P f) =
        if finiteLocalRestrict F v χ = ω then finiteLocalMellinEval F v μ χ f else 0 := by
    let l := finiteLocalMellinEval F v μ χ
    have h := (hP f l).2
    change l (P f) = ∫ a, l ((((ω a)⁻¹ : Circle) : ℂ) • finiteLocalUnitAction F v a f) ∂ν at h
    simp only [map_smul, smul_eq_mul] at h
    have he (a : U F v) : (((ω a)⁻¹ : Circle) : ℂ) * l (finiteLocalUnitAction F v a f) =
        (star (ω a : ℂ) * (finiteLocalRestrict F v χ a : ℂ)) * l f := by
      dsimp only [l]
      rw [finiteLocalMellinEval_unit F v μ χ a f, ← mul_assoc, Circle.coe_inv_eq_conj]
      rfl
    rw [integral_congr_ae (.of_forall he), integral_mul_const,
      integral_character_pair ν ω (finiteLocalRestrict F v χ)] at h
    rw [h]
    have hm : ν.real univ = 1 := by simp [ν, Measure.real, principalUnitHaar_univ]
    by_cases hc : finiteLocalRestrict F v χ = ω
    · simp [hc, hm, l]
    · have hc' : ω ≠ finiteLocalRestrict F v χ := Ne.symm hc
      simp [hc, hc']
  refine ⟨P, fun f ↦ ?_, ?_⟩
  · constructor
    · intro h χ hχ
      have he := hcoeff χ f
      rwa [h, map_zero, ite_eq_left hχ, eq_comm] at he
    · intro h
      apply finiteLocalMellinEval_separates F v μ
      intro χ
      rw [hcoeff]
      split_ifs with he
      · exact h χ he
      · rfl
  · ext T
    change (∀ f ∈ P.ker, T f = 0) ↔
      ∀ (a : U F v) f, T (finiteLocalUnitAction F v a f) = (ω a : ℂ) * T f
    rw [hker]
    change (actionDifferenceSpan (twistedCircleAction ω.toMonoidHom
      (finiteLocalUnitAction F v))).topologicalClosure ≤ T.ker ↔ _
    let S := actionDifferenceSpan (twistedCircleAction ω.toMonoidHom (finiteLocalUnitAction F v))
    rw [show S.topologicalClosure ≤ T.ker ↔ S ≤ T.ker from
      ⟨S.le_topologicalClosure.trans, fun h ↦ S.topologicalClosure_minimal h T.isClosed_ker⟩]
    change Submodule.span ℂ _ ≤ T.ker ↔ _
    rw [Submodule.span_le]
    constructor
    · intro h a f
      have hh := h (mem_range_self (a, f))
      change T (f - (((ω a)⁻¹ : Circle) : ℂ) • finiteLocalUnitAction F v a f) = 0 at hh
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero, Circle.coe_inv] at hh
      have he := congrArg ((ω a : ℂ) * ·) hh
      simpa [← mul_assoc, (ω a).coe_ne_zero] using he.symm
    · intro h _ hf
      obtain ⟨⟨a, f⟩, rfl⟩ := hf
      change T (f - (((ω a)⁻¹ : Circle) : ℂ) • finiteLocalUnitAction F v a f) = 0
      rw [map_sub, map_smul, smul_eq_mul, h, Circle.coe_inv, ← mul_assoc,
        inv_mul_cancel₀ (ω a).coe_ne_zero, one_mul, sub_self]

/-- The finite-place strong span with a prescribed character of the integral units. -/
theorem finiteLocalMellin_homogeneous_strongSpan :
    closure (Submodule.span ℂ
      (range fun χ : {χ : PontryaginDual (K F v)ˣ // finiteLocalRestrict F v χ = ω} ↦
        finiteLocalMellinEval F v μ χ.val) : Set (StrongDual ℂ (E F v))) =
      {T : StrongDual ℂ (E F v) | ∀ (a : U F v) f,
        T (finiteLocalUnitAction F v a f) = (ω a : ℂ) * T f} := by
  obtain ⟨P, hP, hT⟩ := finiteLocalMellin_component_kernel F v μ ω
  let b := Module.Free.chooseBasis ℂ (E F v)
  rw [← hT, strongDual_closure_span_eq_annihilator (finest_strongBidual b)
    (finest_strongBidual_apply b) _ P.ker]
  intro f
  change P f = 0 ↔ _
  rw [hP]
  exact ⟨fun h χ ↦ h χ.val χ.property, fun h χ hc ↦ h ⟨χ, hc⟩⟩

end
end Masullo
