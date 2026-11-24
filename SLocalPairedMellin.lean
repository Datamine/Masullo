import SLocalUnramifiedThetaRange
import SLocalZetaVerticalSchwartz
import SLocalFourierTail
import MellinBergman
import BergmanVerticalTranslation
import FrechetFactorization

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace WithSeminorms
open scoped Classical NumberField SchwartzMap NNReal ENNReal

namespace Masullo

noncomputable section

set_option maxHeartbeats 2400000

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev E := sLocalBruhatImage F S
private abbrev K := SLocalThetaNormOne F S
private abbrev R := Ioi (0 : ℝ)
private abbrev L := Iio (1 : ℝ)

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (ω : PontryaginDual (K F S))

private abbrev Q := SLocalHomogeneousThetaQuotient F S ν ω
private abbrev M := sLocalHomogeneousThetaKernel F S ν ω

private theorem sLocalMellinEval_ker (f : E F S) (hf : f ∈ M F S ν ω) (z : ℂ) (hz : 0 < z.re) :
    sLocalThetaZetaCLM F S ν ω z hz f = 0 := by
  have hline : ∀ y : ℝ, sLocalThetaZetaIntegral F S ν ω f (1 + (y : ℂ) * Complex.I) = 0 := by
    simp only [sLocalHomogeneousThetaKernel, Submodule.mem_iInf, LinearMap.mem_ker] at hf
    intro y
    exact hf y
  have hθ := (sLocalHomogeneousTheta_zero_iff_verticalZeta F S ν ω f 1 zero_lt_one).mpr hline
  rw [sLocalThetaZetaCLM_apply, (sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).2,
    sLocalRadialMellin]
  simp only [hθ, mul_zero, integral_zero]

private def rightEval (z : ℂ) (hz : 0 < z.re) : Q F S ν ω →L[ℂ] ℂ :=
  (M F S ν ω).liftQL (sLocalThetaZetaCLM F S ν ω z hz)
    (fun f hf ↦ LinearMap.mem_ker.mpr (sLocalMellinEval_ker F S ν ω f hf z hz))

private def canonicalRadialProfile (f : E F S) : PositiveRealExponentialDecay R := by
  let θ (t : ℝ) := sLocalHomogeneousTheta F S ν ω f.val
    (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t)))
  refine ⟨θ, (Submodule.mem_iInf _).2 fun a ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_sLocalRadialSchwartz F S ν ω f a.val a.property
  refine ⟨g, funext fun t ↦ ?_⟩
  change g t = (Real.exp (a.val * t) : ℂ) * θ t
  rw [hg]
  change Complex.exp ((a.val : ℂ) * (t : ℂ)) * θ t = (Real.exp (a.val * t) : ℂ) * θ t
  rw [Complex.ofReal_exp, Complex.ofReal_mul]

private theorem canonicalRadialProfile_mellin (f : E F S) (z : ℂ) (hz : 0 < z.re) :
    (positiveRealFourierMellin R isOpen_Ioi ordConnected_Ioi nonempty_Ioi
      (canonicalRadialProfile F S ν ω f)).val z =
        rightEval F S ν ω z hz (Submodule.Quotient.mk f) := by
  rw [positiveRealFourierMellin_apply R isOpen_Ioi ordConnected_Ioi nonempty_Ioi _ z hz,
    mellin_eq_log_integral]
  change (∫ t : ℝ, Complex.exp (z * (t : ℂ)) *
    (canonicalRadialProfile F S ν ω f).val (Real.log (Real.exp t))) =
    sLocalThetaZetaCLM F S ν ω z hz f
  rw [sLocalThetaZetaCLM_apply, (sLocalThetaZeta_integrable_eq_radial F S ν ω f z hz).2]
  simp only [Real.log_exp, sLocalRadialMellin, canonicalRadialProfile]

private theorem rightEval_exists (q : Q F S ν ω) :
    ∃ g : SchwartzBergman R, ∀ z (hz : 0 < z.re), g.val z = rightEval F S ν ω z hz q := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (M F S ν ω) q
  exact ⟨positiveRealFourierMellin R isOpen_Ioi ordConnected_Ioi nonempty_Ioi
    (canonicalRadialProfile F S ν ω f), fun z hz ↦ canonicalRadialProfile_mellin F S ν ω f z hz⟩

private theorem rightBergman_ext {f g : SchwartzBergman R}
    (h : ∀ z, 0 < z.re → f.val z = g.val z) : f = g := by
  apply Subtype.ext
  funext z
  by_cases hz : 0 < z.re
  · exact h z hz
  · have hf := f.property.1 (show z ∈ (Complex.re ⁻¹' R)ᶜ from hz)
    have hg := g.property.1 (show z ∈ (Complex.re ⁻¹' R)ᶜ from hz)
    exact hf.trans hg.symm

/-- The actual positive-half-plane Mellin transform as a continuous map
from the homogeneous theta quotient to its Schwartz–Bergman space. -/
def sLocalRightBergmanMellin : Q F S ν ω →L[ℂ] SchwartzBergman R := by
  let P (q : Q F S ν ω) := (rightEval_exists F S ν ω q).choose
  have hP (q : Q F S ν ω) := (rightEval_exists F S ν ω q).choose_spec
  let A : Q F S ν ω →ₗ[ℂ] SchwartzBergman R :=
    { toFun := P
      map_add' := fun q r ↦ rightBergman_ext fun z hz ↦ by
        change (P (q+r)).val z = (P q).val z + (P r).val z
        rw [hP (q+r) z hz, hP q z hz, hP r z hz, map_add]
      map_smul' := fun c q ↦ rightBergman_ext fun z hz ↦ by
        change (P (c • q)).val z = c • (P q).val z
        rw [hP (c • q) z hz, hP q z hz, map_smul] }
  have hgraph : IsClosed (A.graph : Set (Q F S ν ω × SchwartzBergman R)) := by
    rw [show (A.graph : Set (Q F S ν ω × SchwartzBergman R)) =
      ⋂ (z : ℂ) (hz : 0 < z.re), {p | rightEval F S ν ω z hz p.1 = p.2.val z} from by
        ext p
        change p ∈ A.graph ↔ _
        rw [A.mem_graph_iff]
        simp only [mem_iInter, mem_ofPred_eq]
        constructor
        · intro hp z hz
          rw [hp]
          exact (hP p.1 z hz).symm
        · intro h
          exact (rightBergman_ext fun z hz ↦ (hP p.1 z hz).trans (h z hz)).symm]
    refine isClosed_iInter fun z ↦ isClosed_iInter fun hz ↦ isClosed_eq
      ((rightEval F S ν ω z hz).continuous.comp continuous_fst) ?_
    obtain ⟨e, he⟩ := exists_schwartzBergman_jetEvaluation isOpen_Ioi ordConnected_Ioi z hz 0
    have h := e.continuous.comp (continuous_snd (X := Q F S ν ω))
    exact h.congr (fun p ↦ (he p.2).trans (congrFun iteratedDeriv_zero z))
  have hcont : Continuous A := by
    obtain ⟨hQadd, hQpoly, hQmetric, hQcomplete⟩ := sLocalHomogeneousTheta_isFrechet F S ν ω
    obtain ⟨hRadd, hRpoly, hRmetric, hRcomplete⟩ :=
      schwartzBergman_frechet R isOpen_Ioi ordConnected_Ioi nonempty_Ioi
    letI : UniformSpace (Q F S ν ω) := IsTopologicalAddGroup.rightUniformSpace _
    letI : UniformSpace (SchwartzBergman R) := IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup (Q F S ν ω) := isUniformAddGroup_of_addCommGroup
    letI : IsUniformAddGroup (SchwartzBergman R) := isUniformAddGroup_of_addCommGroup
    letI : CompleteSpace (Q F S ν ω) := hQcomplete
    letI : CompleteSpace (SchwartzBergman R) := hRcomplete
    letI : MetrizableSpace (Q F S ν ω) := hQmetric
    letI : MetrizableSpace (SchwartzBergman R) := hRmetric
    letI : ContinuousSMul ℂ (Q F S ν ω) := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
    letI : ContinuousSMul ℂ (SchwartzBergman R) := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
    exact frechet_continuous_of_closed_graph A hgraph
  exact ⟨A, hcont⟩

theorem sLocalRightBergmanMellin_apply (f : E F S) (z : ℂ) (hz : 0 < z.re) :
    (sLocalRightBergmanMellin F S ν ω (Submodule.Quotient.mk f)).val z =
      sLocalThetaZetaIntegral F S ν ω f z :=
  (rightEval_exists F S ν ω (Submodule.Quotient.mk f)).choose_spec z hz

theorem sLocalRightBergmanMellin_inverse_apply (f : E F S) (t : ℝ) :
    ((positiveRealFourierMellin R isOpen_Ioi ordConnected_Ioi nonempty_Ioi).symm
      (sLocalRightBergmanMellin F S ν ω (Submodule.Quotient.mk f))).val t =
        sLocalHomogeneousTheta F S ν ω f.val
          (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))) := by
  let M := positiveRealFourierMellin R isOpen_Ioi ordConnected_Ioi nonempty_Ioi
  have he : sLocalRightBergmanMellin F S ν ω (Submodule.Quotient.mk f) =
      M (canonicalRadialProfile F S ν ω f) :=
    rightBergman_ext fun z hz ↦ ((rightEval_exists F S ν ω (Submodule.Quotient.mk f)).choose_spec
      z hz).trans (canonicalRadialProfile_mellin F S ν ω f z hz).symm
  change (M.symm (sLocalRightBergmanMellin F S ν ω (Submodule.Quotient.mk f))).val t = _
  rw [he, M.symm_apply_apply]
  rfl

theorem sLocalRightBergmanMellin_injective : Injective (sLocalRightBergmanMellin F S ν ω) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (M F S ν ω) q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change f ∈ M F S ν ω
  simp only [sLocalHomogeneousThetaKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y
  let z := (1 : ℂ) + (y : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z]
  have he := congrArg (fun g : SchwartzBergman R ↦ g.val z) (LinearMap.mem_ker.mp hq)
  rw [show ((sLocalRightBergmanMellin F S ν ω).toLinearMap (Submodule.Quotient.mk f)).val z =
    sLocalThetaZetaIntegral F S ν ω f z from sLocalRightBergmanMellin_apply F S ν ω f z hz] at he
  exact he

private theorem reflect_re_pos (z : ℂ) : 0 < (1-z).re ↔ z.re < 1 := by
  simp [Complex.sub_re, sub_pos]

private theorem reflectBergman_mem {I J : Set ℝ}
    (hIJ : ∀ x : ℝ, 1-x ∈ I ↔ x ∈ J) (G : SchwartzBergman I) :
    (fun z : ℂ ↦ G.val (1-z)) ∈ schwartzBergmanSubmodule J := by
  have h (z : ℂ) : (1-z).re ∈ I ↔ z.re ∈ J := by
    simpa only [Complex.sub_re, Complex.one_re] using hIJ z.re
  refine ⟨fun z hz ↦ G.property.1 (fun hp ↦ hz ((h z).mp hp)),
    G.property.2.1.comp (by fun_prop) (fun z hz ↦ (h z).mpr hz), ?_⟩
  intro a b hab hI n
  have hJ : Icc (1-b) (1-a) ⊆ I := fun σ hσ ↦ by
    have he : 1-σ ∈ Icc a b := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    simpa only [sub_sub_cancel] using (hIJ (1-σ)).mpr (hI he)
  obtain ⟨M, hM⟩ := G.property.2.2 (1-b) (1-a) (by linarith) hJ n
  obtain ⟨B, hB⟩ := G.property.2.2 (1-b) (1-a) (by linarith) hJ 0
  refine ⟨2^n * max M B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  let w := 1-z
  have hw : w.re ∈ Icc (1-b) (1-a) := by
    change z.re ∈ Icc a b at hz
    simp only [w, Complex.sub_re, Complex.one_re]
    constructor <;> linarith [hz.1, hz.2]
  have hn := norm_sub_le (1 : ℂ) w
  rw [show (1 : ℂ)-w=z by simp [w], norm_one] at hn
  have hle : ‖z‖ ≤ 2 * max 1 ‖w‖ :=
    hn.trans (by linarith [le_max_left (1 : ℝ) ‖w‖, le_max_right (1 : ℝ) ‖w‖])
  change ‖z^n * G.val w‖ ≤ _
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2 * max 1 ‖w‖)^n * ‖G.val w‖ := by gcongr
    _ = 2^n * ((max 1 ‖w‖)^n * ‖G.val w‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total ‖w‖ 1 with h | h
      · rw [max_eq_left h, one_pow, one_mul]
        exact (by simpa only [pow_zero, one_mul] using hB (mem_image_of_mem _ hw) :
          ‖G.val w‖ ≤ B).trans (le_max_right _ _)
      · rw [max_eq_right h]
        exact (by simpa only [norm_mul, norm_pow] using hM (mem_image_of_mem _ hw) :
          ‖w‖^n * ‖G.val w‖ ≤ M).trans (le_max_left _ _)

theorem bergman_continuous_evaluation {I : Set ℝ} (hI : IsOpen I) (hord : OrdConnected I)
    (z : ℂ) (hz : z.re ∈ I) : Continuous (fun G : SchwartzBergman I ↦ G.val z) := by
  obtain ⟨e, he⟩ := exists_schwartzBergman_jetEvaluation hI hord z hz 0
  exact e.continuous.congr (fun G ↦ (he G).trans (congrFun iteratedDeriv_zero z))

private def bergmanReflect {I J : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (hJ : IsOpen J) (hJo : OrdConnected J) (hJn : J.Nonempty)
    (hIJ : ∀ x : ℝ, 1-x ∈ I ↔ x ∈ J) :
    SchwartzBergman I →L[ℂ] SchwartzBergman J := by
  have hre (z : ℂ) : (1-z).re ∈ I ↔ z.re ∈ J := by
    simpa only [Complex.sub_re, Complex.one_re] using hIJ z.re
  let A : SchwartzBergman I →ₗ[ℂ] SchwartzBergman J :=
    { toFun := fun G ↦ ⟨fun z ↦ G.val (1-z), reflectBergman_mem hIJ G⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  have hgraph : IsClosed (A.graph : Set (SchwartzBergman I × SchwartzBergman J)) := by
    rw [show (A.graph : Set (SchwartzBergman I × SchwartzBergman J)) =
      ⋂ (z : ℂ) (hz : z.re ∈ J), {p | p.2.val z = p.1.val (1-z)} from by
        ext p
        change p ∈ A.graph ↔ _
        rw [A.mem_graph_iff]
        simp only [mem_iInter, mem_ofPred_eq]
        constructor
        · intro h z _
          change p.2.val z = (A p.1).val z
          rw [h]
        · intro h
          apply Subtype.ext
          funext z
          by_cases hz : z.re ∈ J
          · exact h z hz
          · exact (p.2.property.1 (show z ∈ (Complex.re ⁻¹' J)ᶜ from hz)).trans
              ((A p.1).property.1 (show z ∈ (Complex.re ⁻¹' J)ᶜ from hz)).symm]
    refine isClosed_iInter fun z ↦ isClosed_iInter fun hz ↦ isClosed_eq ?_ ?_
    · exact (bergman_continuous_evaluation hJ hJo z hz).comp continuous_snd
    · exact (bergman_continuous_evaluation hI hIo (1-z)
        ((hre z).mpr hz)).comp continuous_fst
  have hc : Continuous A := by
    obtain ⟨hRadd, hRpoly, hRmetric, hRcomplete⟩ :=
      schwartzBergman_frechet I hI hIo hIn
    obtain ⟨hLadd, hLpoly, hLmetric, hLcomplete⟩ :=
      schwartzBergman_frechet J hJ hJo hJn
    letI : UniformSpace (SchwartzBergman I) := IsTopologicalAddGroup.rightUniformSpace _
    letI : UniformSpace (SchwartzBergman J) := IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup (SchwartzBergman I) := isUniformAddGroup_of_addCommGroup
    letI : IsUniformAddGroup (SchwartzBergman J) := isUniformAddGroup_of_addCommGroup
    letI : CompleteSpace (SchwartzBergman I) := hRcomplete
    letI : CompleteSpace (SchwartzBergman J) := hLcomplete
    letI : MetrizableSpace (SchwartzBergman I) := hRmetric
    letI : MetrizableSpace (SchwartzBergman J) := hLmetric
    letI : ContinuousSMul ℂ (SchwartzBergman I) := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
    letI : ContinuousSMul ℂ (SchwartzBergman J) := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
    exact frechet_continuous_of_closed_graph A hgraph
  exact ⟨A, hc⟩

/-- Reflect the spectral coordinate and the underlying interval simultaneously. -/
def schwartzBergmanReflectEquiv {I J : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (hJ : IsOpen J) (hJo : OrdConnected J) (hJn : J.Nonempty)
    (hIJ : ∀ x : ℝ, 1-x ∈ I ↔ x ∈ J) :
    SchwartzBergman I ≃L[ℂ] SchwartzBergman J := by
  have hJI (x : ℝ) : 1-x ∈ J ↔ x ∈ I := by
    simpa only [sub_sub_cancel] using (hIJ (1-x)).symm
  refine ContinuousLinearEquiv.equivOfInverse
    (bergmanReflect hI hIo hIn hJ hJo hJn hIJ) (bergmanReflect hJ hJo hJn hI hIo hIn hJI) ?_ ?_
  all_goals
    intro f
    exact Subtype.ext (funext fun z ↦ by
      change f.val (1-(1-z)) = f.val z
      rw [sub_sub_cancel])

theorem schwartzBergmanReflectEquiv_apply {I J : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (hJ : IsOpen J) (hJo : OrdConnected J) (hJn : J.Nonempty)
    (hIJ : ∀ x : ℝ, 1-x ∈ I ↔ x ∈ J) (f : SchwartzBergman I) (z : ℂ) :
    (schwartzBergmanReflectEquiv hI hIo hIn hJ hJo hJn hIJ f).val z = f.val (1-z) := rfl

/-- Reflection in the coordinate $s=1/2$ carries the positive Bergman
space into the left Bergman space continuously. -/
def bergmanReflectOne : SchwartzBergman R →L[ℂ] SchwartzBergman L :=
  bergmanReflect isOpen_Ioi ordConnected_Ioi nonempty_Ioi isOpen_Iio ordConnected_Iio
    nonempty_Iio (fun x ↦ (show 0 < (1 : ℝ)-x ↔ x < 1 from sub_pos))

@[simp] theorem bergmanReflectOne_apply (G : SchwartzBergman R) (z : ℂ) :
    (bergmanReflectOne G).val z = G.val (1-z) := rfl

/-- The pure reflection is a topological linear equivalence of the half-planes. -/
def bergmanReflectOneEquiv : SchwartzBergman R ≃L[ℂ] SchwartzBergman L :=
  schwartzBergmanReflectEquiv isOpen_Ioi ordConnected_Ioi nonempty_Ioi isOpen_Iio
    ordConnected_Iio nonempty_Iio (fun x ↦ (show 0 < (1 : ℝ)-x ↔ x < 1 from sub_pos))

@[simp] theorem bergmanReflectOneEquiv_apply (G : SchwartzBergman R) (z : ℂ) :
    (bergmanReflectOneEquiv G).val z = G.val (1-z) := rfl

private theorem compressedFourier_toGlobal (q : SLocalThetaQuotient F S) :
    globalThetaFourier F (sLocalThetaToGlobal F S q) =
      globalThetaTranslateIdeles F (sLocalCodifferentTailIdele F S)
        (sLocalThetaToGlobal F S (sLocalThetaCompressedFourier F S q)) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [sLocalThetaCompressedFourier_mk]
  change globalThetaFourier F (Submodule.Quotient.mk f.val) =
    globalThetaTranslateIdeles F (sLocalCodifferentTailIdele F S)
      (Submodule.Quotient.mk (sLocalFourierCompression F S f).val)
  rw [globalThetaFourier_mk, globalThetaTranslateIdeles_mk, sLocalFourier_eq_tailTranslate]

theorem compressedFourier_translate_normOne (c : K F S)
    (q : SLocalThetaQuotient F S) :
    sLocalThetaCompressedFourier F S (sLocalNormOneAction F S c q) =
      sLocalNormOneAction F S c⁻¹ (sLocalThetaCompressedFourier F S q) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective c.val
  have hn : sLocalIdeleNorm F S g = 1 := by
    have h := c.property
    change sQuotientNorm F S c.val = 1 at h
    rw [← hg] at h
    exact congrArg (fun a : ℝ≥0ˣ ↦ (a.val : ℝ)) h
  let b := (sLocalEmbed F S g).val
  let j := sLocalThetaToGlobal F S
  let T := sLocalThetaCompressedFourier F S
  let γ := ideleClassMap F (sLocalCodifferentTailIdele F S)
  have hb : ideleNorm F b = 1 := hn
  have hconj := globalThetaFourier_translate_normOne F b hb (j q)
  have hc (r : SLocalThetaQuotient F S) :
      globalThetaFourier F (j r) = globalThetaTranslate F γ (j (T r)) := by
    rw [globalThetaTranslate_class]
    exact compressedFourier_toGlobal F S r
  have h₁ : j (sLocalNormOneAction F S c q) = globalThetaTranslateIdeles F b (j q) := by
    change j (sLocalThetaTranslate F S c.val q) = _
    rw [← hg]
    exact sLocalThetaToGlobal_translate F S g q
  have h₂ (r : SLocalThetaQuotient F S) :
      j (sLocalNormOneAction F S c⁻¹ r) =
        globalThetaTranslate F (ideleClassMap F b⁻¹) (j r) := by
    change j (sLocalThetaTranslate F S c.val⁻¹ r) = _
    rw [← hg]
    change j (sLocalThetaTranslate F S ((QuotientGroup.mk' (sUnitImage F S)) g)⁻¹ r) = _
    rw [← map_inv (QuotientGroup.mk' (sUnitImage F S))]
    have hginv : (sLocalEmbed F S g⁻¹).val = b⁻¹ := by simp [b]
    exact (sLocalThetaToGlobal_translate_class F S g⁻¹ r).trans
      (congrArg (fun a : Idele F ↦ globalThetaTranslate F (ideleClassMap F a) (j r)) hginv)
  rw [← h₁, hc, hc, ← globalThetaTranslate_class] at hconj
  have hswap (w : GlobalThetaQuotient F) :
      globalThetaTranslate F (ideleClassMap F b⁻¹) (globalThetaTranslate F γ w) =
        globalThetaTranslate F γ (globalThetaTranslate F (ideleClassMap F b⁻¹) w) := by
    simp only [← ContinuousLinearMap.comp_apply, ← globalThetaTranslate_mul]
    exact congrArg (fun a : IdeleClass F ↦ globalThetaTranslate F a w)
      (mul_comm (ideleClassMap F b⁻¹) γ)
  rw [hswap, ← h₂] at hconj
  apply sLocalThetaToGlobal_injective F S
  have hcancel (w : GlobalThetaQuotient F) :
      globalThetaTranslate F γ⁻¹ (globalThetaTranslate F γ w) = w := by
    simp only [← ContinuousLinearMap.comp_apply, ← globalThetaTranslate_mul, inv_mul_cancel,
      globalThetaTranslate_one, ContinuousLinearMap.id_apply]
  have he := congrArg (globalThetaTranslate F γ⁻¹) hconj
  simpa only [hcancel] using he

/-- The local Fourier integral descends to the inverse character quotient
at every finite stage. -/
theorem exists_sLocalHomogeneousFourier :
    ∃ U : Q F S ν ω →L[ℂ] Q F S ν ω⁻¹,
      U.comp (sLocalThetaToComponent F S ν ω) =
        (sLocalThetaToComponent F S ν ω⁻¹).comp (sLocalThetaCompressedFourier F S) := by
  letI : T2Space (Q F S ν ω⁻¹) := (sLocalHomogeneousTheta_primalStructure F S ν ω⁻¹).1.1
  let A := (sLocalThetaToComponent F S ν ω⁻¹).comp (sLocalThetaCompressedFourier F S)
  let p := sLocalThetaToComponent F S ν ω
  obtain ⟨j, hj, _, hk⟩ := sLocalThetaComponent_isotypicSection F S ν ω
  obtain ⟨_, _, _, hk'⟩ := sLocalThetaComponent_isotypicSection F S ν ω⁻¹
  have hA : p.ker ≤ A.ker := by
    change (sLocalThetaToComponent F S ν ω).ker ≤ A.ker
    rw [hk]
    apply Submodule.topologicalClosure_minimal _ _ A.isClosed_ker
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, q⟩, rfl⟩
    let w := sLocalThetaCompressedFourier F S q
    have hw : w - ((((ω⁻¹ k⁻¹)⁻¹ : Circle) : ℂ)) • sLocalNormOneAction F S k⁻¹ w ∈
        (sLocalThetaToComponent F S ν ω⁻¹).ker := by
      rw [hk']
      apply Submodule.le_topologicalClosure
      exact Submodule.subset_span ⟨(k⁻¹,w), rfl⟩
    have he : ω⁻¹ k⁻¹ = ω k := by
      change (ω k⁻¹)⁻¹ = ω k
      rw [map_inv, inv_inv]
    rw [he] at hw
    change (sLocalThetaToComponent F S ν ω⁻¹)
      (sLocalThetaCompressedFourier F S (q - ((((ω k)⁻¹ : Circle) : ℂ)) • sLocalNormOneAction F S k q)) = 0
    rw [map_sub, map_smul]
    have hcomm : sLocalThetaCompressedFourier F S (sLocalNormOneAction F S k q) =
        sLocalNormOneAction F S k⁻¹ w :=
      compressedFourier_translate_normOne F S k q
    rw [hcomm]
    exact hw
  refine ⟨A.comp j, ContinuousLinearMap.ext fun q ↦ ?_⟩
  have hq : q - j (p q) ∈ p.ker := by
    change p (q - j (p q)) = 0
    rw [map_sub, hj (p q), sub_self]
  have hz := hA hq
  change A (q - j (p q)) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- Product of the omitted finite additive Tamagawa masses. -/
abbrev sLocalFourierTailVolume : ℝ≥0∞ :=
  ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, differentPrimeMass F v.val

theorem sLocalFourierTailVolume_pos : 0 < (sLocalFourierTailVolume F S).toReal := by
  let m (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) := differentPrimeMass F v.val
  have hn : (∏ᶠ v, m v) ≠ 0 :=
    finprod_ne_zero (f := m) fun v ↦ differentPrimeMass_ne_zero F v.val
  refine ENNReal.toReal_pos hn ?_
  change (∏ᶠ v, m v) ≠ ∞
  by_cases hm : m.HasFiniteMulSupport
  · rw [finprod_eq_prod m hm]
    exact ENNReal.prod_ne_top fun v _ ↦ differentPrimeMass_ne_top F v.val
  · rw [finprod_of_not_hasFiniteMulSupport hm]
    exact ENNReal.one_ne_top

/-- Remove the omitted-place volume from the padded adelic Fourier
integral to give the selected-place Tamagawa normalization. -/
def sLocalSelectedFourier : E F S →L[ℂ] E F S :=
  ((sLocalFourierTailVolume F S).toReal : ℂ)⁻¹ • sLocalFourierCompression F S

section AdditiveHaar

variable [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]

set_option maxHeartbeats 500000 in
theorem sLocalSelectedFourier_restrict (f : E F S) (ξ : SAdeles F S) :
    sLocalBruhatRestriction F S (sLocalSelectedFourier F S f).val ξ =
      ∫ x : SAdeles F S, sLocalBruhatRestriction F S f.val x *
        ((standardAdelicCharacter F (sLocalBruhatPad F S (x * ξ))).toMul : ℂ)
        ∂sLocalAdditiveProduct F S (fun v ↦ additiveHaarDifferent F v.val) := by
  have hm : ((sLocalFourierTailVolume F S).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sLocalFourierTailVolume_pos F S).ne'
  let c : ℂ := ((sLocalFourierTailVolume F S).toReal : ℂ)⁻¹
  let g := sLocalFourierCompression F S f
  change sLocalBruhatRestriction F S (c • g.val) ξ = _
  rw [map_smul]
  change c * sLocalBruhatRestriction F S g.val ξ = _
  have h := sLocalFourierCompression_restrict F S f ξ
  rw [sLocalFourierCompressionMeasure, integral_smul_measure] at h
  change sLocalBruhatRestriction F S g.val ξ = _ at h
  rw [h, Complex.real_smul, ← mul_assoc]
  dsimp only [c]
  rw [inv_mul_cancel₀ hm, one_mul]

end AdditiveHaar

/-- The paired transform of (5.4.1.2) with the local Fourier integral. -/
def sLocalPairedBergmanMellin : Q F S ν ω →L[ℂ] SchwartzBergman R × SchwartzBergman L := by
  let U := ((sLocalFourierTailVolume F S).toReal : ℂ)⁻¹ • (exists_sLocalHomogeneousFourier F S ν ω).choose
  exact (sLocalRightBergmanMellin F S ν ω).prod
    (bergmanReflectOne.comp ((sLocalRightBergmanMellin F S ν ω⁻¹).comp U))

/-- Lemma 5.4.1.3 at every finite stage. -/
theorem sLocalPairedBergmanMellin_injective :
    Injective (sLocalPairedBergmanMellin F S ν ω) :=
  fun _ _ h ↦ sLocalRightBergmanMellin_injective F S ν ω (congrArg Prod.fst h)

theorem sLocalPairedBergmanMellin_apply (f : E F S) :
    (∀ z (_hz : 0 < z.re),
      (sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk f)).1.val z =
        sLocalThetaZetaIntegral F S ν ω f z) ∧
    (∀ z (_hz : z.re < 1),
      (sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk f)).2.val z =
        sLocalThetaZetaIntegral F S ν ω⁻¹
          (sLocalSelectedFourier F S f) (1-z)) := by
  refine ⟨fun z hz ↦ sLocalRightBergmanMellin_apply F S ν ω f z hz, fun z hz ↦ ?_⟩
  let U := (exists_sLocalHomogeneousFourier F S ν ω).choose
  have hU := (exists_sLocalHomogeneousFourier F S ν ω).choose_spec
  have he := congrArg (fun A : SLocalThetaQuotient F S →L[ℂ] Q F S ν ω⁻¹ ↦
    A (Submodule.Quotient.mk f)) hU
  change U (Submodule.Quotient.mk f) =
    (sLocalThetaToComponent F S ν ω⁻¹) (sLocalThetaCompressedFourier F S (Submodule.Quotient.mk f)) at he
  rw [sLocalThetaCompressedFourier_mk] at he
  change (bergmanReflectOne (sLocalRightBergmanMellin F S ν ω⁻¹
    (((sLocalFourierTailVolume F S).toReal : ℂ)⁻¹ • U (Submodule.Quotient.mk f)))).val z = _
  rw [bergmanReflectOne_apply, he]
  have hq : ((sLocalFourierTailVolume F S).toReal : ℂ)⁻¹ •
      (sLocalThetaToComponent F S ν ω⁻¹) (Submodule.Quotient.mk (sLocalFourierCompression F S f)) =
        Submodule.Quotient.mk (sLocalSelectedFourier F S f) := by
    change _ • (M F S ν ω⁻¹).mkQ _ = _
    rw [← map_smul]
    rfl
  rw [hq]
  exact sLocalRightBergmanMellin_apply F S ν ω⁻¹ _ _ ((reflect_re_pos z).mpr hz)

attribute [local instance] sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

/-- Both components are the actual idelic zeta integrals for compatible
multiplicative Haar measures. The second uses the selected-place Fourier
integral and the reflected exponent and character. -/
theorem sLocalPairedBergmanMellin_idelic
    (μ : Measure (SAdeles F S)ˣ) [μ.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (sUnitImage F S) μ Measure.count (sLocalClassHaar F S ν))
    (f : E F S) :
    (∀ z, 0 < z.re →
      (sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk f)).1.val z =
        sLocalIdelicZetaIntegral F S μ ω f z) ∧
    (∀ z, z.re < 1 →
      (sLocalPairedBergmanMellin F S ν ω (Submodule.Quotient.mk f)).2.val z =
        sLocalIdelicZetaIntegral F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z)) := by
  obtain ⟨hR, hL⟩ := sLocalPairedBergmanMellin_apply F S ν ω f
  constructor
  · intro z hz
    exact (hR z hz).trans (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω f z hz).2.symm
  · intro z hz
    exact (hL z hz).trans (sLocalIdelicZeta_integrable_eq_theta F S μ ν hν ω⁻¹
      (sLocalSelectedFourier F S f) (1-z) ((reflect_re_pos z).mpr hz)).2.symm

/-- Relative to the canonical radial splitting, a continuous section
changes the chosen unitary character by a purely imaginary exponent. -/
theorem exists_sLocalSection_phase
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ)
    (hn : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t) :
    ∃ d : ℂ, d.re = 0 ∧ ∀ z (t : ℝ) (k : K F S),
      sLocalZetaWeight F S ω (z-d) (τ (Multiplicative.ofAdd t) * k.val) =
        Complex.exp (z * (t : ℂ)) * (ω k : ℂ) := by
  let a : Multiplicative ℝ →* SIdeleQuotient F S :=
    (QuotientGroup.mk' (sUnitImage F S)).comp (sLocalExpSection F S)
  have ha : Continuous a := QuotientGroup.continuous_mk.comp (sLocalExpSection_continuous F S)
  have ham (t : ℝ) : sLocalClassModulus F S (a (Multiplicative.ofAdd t)) = Real.exp t :=
    sLocalIdeleNorm_expSection F S t
  let r : Multiplicative ℝ →* SIdeleQuotient F S :=
    { toFun := fun t ↦ τ t / a t
      map_one' := by simp
      map_mul' := fun x y ↦ by
        rw [map_mul, map_mul]
        exact (div_mul_div_comm (τ x) (a x) (τ y) (a y)).symm }
  let b : Multiplicative ℝ →* K F S :=
    r.codRestrict _ (fun t ↦ by
      change sQuotientNorm F S (τ t / a t) = 1
      rw [map_div, div_eq_one]
      apply Units.ext
      apply NNReal.eq
      exact (hn t.toAdd).trans (ham t.toAdd).symm)
  have hb : Continuous b := (hτ.div' ha).subtype_mk _
  let χ := (Circle.coeHom.comp (ω.toMonoidHom.comp b)).toHomUnits
  have hχ : Continuous (fun t : ℝ ↦ (χ (Multiplicative.ofAdd t) : ℂ)) :=
    (continuous_subtype_val.comp (ω.continuous.comp hb)).comp continuous_ofAdd
  obtain ⟨d, hd, _⟩ := complex_oneParameter_exp χ hχ
  have hRe : d.re = 0 := by
    have h := congrArg norm (hd 1)
    change ‖(ω (b (Multiplicative.ofAdd (1 : ℝ))) : ℂ)‖ =
      ‖Complex.exp (d * ((1 : ℝ) : ℂ))‖ at h
    rw [Circle.norm_coe, Complex.ofReal_one, mul_one, Complex.norm_exp,
      ← Real.exp_zero] at h
    exact Real.exp_injective h.symm
  refine ⟨d, hRe, fun z t k ↦ ?_⟩
  let u := Multiplicative.ofAdd t
  have hu : τ u * k.val = sLocalZetaSplit F S (t, b u * k) := by
    change τ u * k.val = a u * ((τ u / a u) * k.val)
    rw [← mul_assoc, mul_comm (a u) (τ u / a u), div_mul_cancel]
  rw [hu, sLocalZetaWeight_split, map_mul, Circle.coe_mul]
  have hp : (ω (b u) : ℂ) = Complex.exp (d * (t : ℂ)) := hd t
  rw [hp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The operator in any chart differing from the canonical one by a unitary
radial exponent. Both coordinates use the same translated spectral argument. -/
def sLocalPairedBergmanMellin_shift (d : ℂ) (hd : d.re = 0) :
    Q F S ν ω →L[ℂ] SchwartzBergman R × SchwartzBergman L :=
  ((schwartzBergmanVerticalShift R isOpen_Ioi ordConnected_Ioi nonempty_Ioi d hd).prodMap
    (schwartzBergmanVerticalShift L isOpen_Iio ordConnected_Iio nonempty_Iio d hd)).comp
      (sLocalPairedBergmanMellin F S ν ω)

theorem sLocalPairedBergmanMellin_shift_apply (d : ℂ) (hd : d.re = 0) (q : Q F S ν ω) (z : ℂ) :
    (sLocalPairedBergmanMellin_shift F S ν ω d hd q).1.val z =
      (sLocalPairedBergmanMellin F S ν ω q).1.val (z+d) ∧
    (sLocalPairedBergmanMellin_shift F S ν ω d hd q).2.val z =
      (sLocalPairedBergmanMellin F S ν ω q).2.val (z+d) := ⟨rfl, rfl⟩

/-- A change of radial section preserves injectivity. -/
theorem sLocalPairedBergmanMellin_shift_injective (d : ℂ) (hd : d.re = 0) :
    Injective (sLocalPairedBergmanMellin_shift F S ν ω d hd) := by
  intro q r h
  apply sLocalPairedBergmanMellin_injective F S ν ω
  apply Prod.ext
  · apply Subtype.ext
    funext z
    have he := congrArg (fun p : SchwartzBergman R × SchwartzBergman L ↦ p.1.val (z-d)) h
    simpa only [sLocalPairedBergmanMellin_shift_apply, sub_add_cancel] using he
  · apply Subtype.ext
    funext z
    have he := congrArg (fun p : SchwartzBergman R × SchwartzBergman L ↦ p.2.val (z-d)) h
    simpa only [sLocalPairedBergmanMellin_shift_apply, sub_add_cancel] using he

private theorem sLocalZetaWeight_reflect_character (z : ℂ) (q : SIdeleQuotient F S) :
    sLocalZetaWeight F S ω⁻¹ z q = (sLocalZetaWeight F S ω (-z) q)⁻¹ := by
  let p := (sLocalZetaSplit F S).symm q
  change Complex.exp (z * (p.1 : ℂ)) * (ω⁻¹ p.2 : ℂ) =
    (Complex.exp (-z * (p.1 : ℂ)) * (ω p.2 : ℂ))⁻¹
  rw [neg_mul, Complex.exp_neg, mul_inv, inv_inv]
  rfl

/-- The paired Mellin map for any continuous homomorphic norm section
is continuous and injective. The two displayed weight identities specify
its coordinates relative to that section. -/
theorem exists_sLocalPairedBergmanMellin_for_section
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ)
    (hn : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (μ : Measure (SAdeles F S)ˣ) [μ.IsHaarMeasure]
    (hν : IsWeilQuotientMeasure (sUnitImage F S) μ Measure.count (sLocalClassHaar F S ν)) :
    ∃ (U : Q F S ν ω →L[ℂ] SchwartzBergman R × SchwartzBergman L)
      (d : ℂ), Injective U ∧ d.re = 0 ∧
      (∀ (z : ℂ) (t : ℝ) (k : K F S),
        let q := τ (Multiplicative.ofAdd t) * k.val
        sLocalZetaWeight F S ω (z-d) q =
          Complex.exp (z * (t : ℂ)) * (ω k : ℂ) ∧
        sLocalZetaWeight F S ω⁻¹ (1-z+d) q =
          Complex.exp ((1-z) * (t : ℂ)) * (ω⁻¹ k : ℂ)) ∧
      (∀ (f : E F S) z, 0 < z.re →
        (U (Submodule.Quotient.mk f)).1.val z =
          sLocalIdelicZetaIntegral F S μ ω f (z-d)) ∧
      (∀ (f : E F S) z, z.re < 1 →
        (U (Submodule.Quotient.mk f)).2.val z =
          sLocalIdelicZetaIntegral F S μ ω⁻¹ (sLocalSelectedFourier F S f) (1-z+d)) := by
  obtain ⟨d, hd, hphase⟩ := exists_sLocalSection_phase F S ω τ hτ hn
  have hd' : (-d).re = 0 := by simp [hd]
  let U := sLocalPairedBergmanMellin_shift F S ν ω (-d) hd'
  refine ⟨U, d, sLocalPairedBergmanMellin_shift_injective F S ν ω (-d) hd', hd, ?_, ?_, ?_⟩
  · intro z t k
    refine ⟨hphase z t k, ?_⟩
    let q := τ (Multiplicative.ofAdd t) * k.val
    change sLocalZetaWeight F S ω⁻¹ (1-z+d) q = _
    rw [sLocalZetaWeight_reflect_character,
      show -(1-z+d) = -(1-z)-d by ring, hphase (-(1-z)) t k, mul_inv, neg_mul, Complex.exp_neg, inv_inv]
    rfl
  · intro f z hz
    rw [(sLocalPairedBergmanMellin_shift_apply F S ν ω (-d) hd' _ z).1, ← sub_eq_add_neg]
    exact (sLocalPairedBergmanMellin_idelic F S ν ω μ hν f).1 (z-d)
      (by simpa [hd] using hz)
  · intro f z hz
    rw [(sLocalPairedBergmanMellin_shift_apply F S ν ω (-d) hd' _ z).2,
      ← sub_eq_add_neg, (sLocalPairedBergmanMellin_idelic F S ν ω μ hν f).2 (z-d)
        (by simpa [hd] using hz)]
    congr 1
    ring

end
end Masullo
