import MellinBergman
import FrechetFactorization
import ExponentialDecayStructure
import SchwartzCompactTranslation
import ThetaTranslationContinuity

open MeasureTheory Set Topology TopologicalSpace WithSeminorms
open scoped SchwartzMap

namespace Masullo

noncomputable section

private theorem continuous_logDecayTranslation (I : Set ℝ) (hne : I.Nonempty) :
    Continuous (fun p : ℝ × PositiveRealExponentialDecay I ↦
      logExponentialDecayTranslation I hne p.1 p.2) := by
  letI : BarrelledSpace ℂ 𝓢(ℝ, ℂ) :=
    isFrechetTVS_barrelled (classicalSchwartz_isFrechet ℝ)
  letI : PolynormableSpace ℂ 𝓢(ℝ, ℂ) := (classicalSchwartz_isFrechet ℝ).choose_spec.1
  have hSch := continuous_joint_of_barrelled
    (fun a : ℝ ↦ SchwartzMap.compSubConstCLM ℂ a) continuous_schwartz_compSubConst
  have hE := (positiveRealExponentialDecay_isEmbedding I hne).isInducing
  apply hE.continuous_iff.mpr
  apply continuous_pi
  intro a
  have ht : Continuous (fun p : ℝ × PositiveRealExponentialDecay I ↦ logExponentialDecayTwist I a p.2) :=
    ((continuous_apply a).comp hE.continuous).comp continuous_snd
  have h := (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp ((continuous_const.mul continuous_fst).neg :
      Continuous (fun p : ℝ × PositiveRealExponentialDecay I ↦ -((a : ℝ) * p.1))))).smul
      (hSch.comp (continuous_fst.neg.prodMk ht))
  apply h.congr
  intro p
  apply SchwartzMap.ext
  intro x
  change ((Real.exp (-((a : ℝ) * p.1)) : ℂ) •
    SchwartzMap.compSubConstCLM ℂ (-p.1) (logExponentialDecayTwist I a p.2)) x =
      logExponentialDecayTwist I a (logExponentialDecayTranslation I hne p.1 p.2) x
  simp only [smul_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul]
  erw [logExponentialDecayTwist_apply, logExponentialDecayTwist_apply]
  change (Real.exp (-((a : ℝ) * p.1)) : ℂ) *
      ((Real.exp ((a : ℝ) * (x+p.1)) : ℂ) * p.2.val (x+p.1)) =
    (Real.exp ((a : ℝ) * x) : ℂ) * p.2.val (x+p.1)
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

/-- Translation of the underlying logarithmic test multiplies its Mellin
transform by the indicated exponential character. -/
def schwartzBergmanRadialTranslate (I : Set ℝ) (hI : IsOpen I) (ho : OrdConnected I)
    (hne : I.Nonempty) (t : ℝ) : SchwartzBergman I →L[ℂ] SchwartzBergman I :=
  let e := positiveRealFourierMellin I hI ho hne
  e.toContinuousLinearMap.comp ((logExponentialDecayTranslation I hne (-t)).comp
    e.symm.toContinuousLinearMap)

theorem continuous_schwartzBergmanRadialTranslate (I : Set ℝ) (hI : IsOpen I)
    (ho : OrdConnected I) (hne : I.Nonempty) :
    Continuous (fun p : ℝ × SchwartzBergman I ↦ schwartzBergmanRadialTranslate I hI ho hne p.1 p.2) :=
  let e := positiveRealFourierMellin I hI ho hne
  e.continuous.comp ((continuous_logDecayTranslation I hne).comp
    (continuous_fst.neg.prodMk (e.symm.continuous.comp continuous_snd)))

theorem schwartzBergmanRadialTranslate_apply (I : Set ℝ) (hI : IsOpen I)
    (ho : OrdConnected I) (hne : I.Nonempty) (t : ℝ) (b : SchwartzBergman I)
    (z : ℂ) (hz : z.re ∈ I) :
    (schwartzBergmanRadialTranslate I hI ho hne t b).val z = Complex.exp (z * (t : ℂ)) * b.val z := by
  let e := positiveRealFourierMellin I hI ho hne
  let f := e.symm b
  have hb : e f = b := e.apply_symm_apply b
  change (e (logExponentialDecayTranslation I hne (-t) f)).val z =
    Complex.exp (z * (t : ℂ)) * b.val z
  rw [← hb, positiveRealFourierMellin_apply I hI ho hne _ z hz,
    positiveRealFourierMellin_apply I hI ho hne _ z hz, mellin_eq_log_integral, mellin_eq_log_integral]
  simp only [Real.log_exp, logExponentialDecayTranslation_apply, ← sub_eq_add_neg]
  rw [← integral_const_mul, ← integral_add_right_eq_self
    (fun x : ℝ ↦ Complex.exp (z * (x : ℂ)) * f.val (x-t)) t]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    change Complex.exp (z * ((x+t : ℝ) : ℂ)) * f.val (x+t-t) =
      Complex.exp (z * (t : ℂ)) * (Complex.exp (z * (x : ℂ)) * f.val x)
    rw [add_sub_cancel_right, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring

private theorem verticalShift_mem {I : Set ℝ} (d : ℂ) (hd : d.re = 0)
    (G : SchwartzBergman I) :
    (fun z ↦ G.val (z+d)) ∈ schwartzBergmanSubmodule I := by
  have hre (z : ℂ) : (z+d).re = z.re := by simp [hd]
  refine ⟨fun z hz ↦ G.property.1 (fun hm ↦ hz (by simpa only [mem_preimage, hre] using hm)),
    G.property.2.1.comp (by fun_prop) (fun z hz ↦ by simpa only [mem_preimage, hre] using hz), ?_⟩
  intro a b hab hI n
  obtain ⟨M, hM⟩ := G.property.2.2 a b hab hI n
  obtain ⟨B, hB⟩ := G.property.2.2 a b hab hI 0
  refine ⟨(1+‖d‖)^n * max M B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  let w := z+d
  have hw : w.re ∈ Icc a b := by simpa only [w, hre, mem_preimage] using hz
  have hnorm := norm_sub_le w d
  rw [show w-d=z by simp [w]] at hnorm
  have hle : ‖z‖ ≤ (1+‖d‖) * max 1 ‖w‖ := hnorm.trans (by
    have h₁ := le_max_right (1 : ℝ) ‖w‖
    have h₂ := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) ‖w‖) (norm_nonneg d)
    linarith)
  change ‖z^n * G.val w‖ ≤ _
  rw [norm_mul, norm_pow]
  calc
    _ ≤ ((1+‖d‖) * max 1 ‖w‖)^n * ‖G.val w‖ := by gcongr
    _ = (1+‖d‖)^n * ((max 1 ‖w‖)^n * ‖G.val w‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total ‖w‖ 1 with h | h
      · rw [max_eq_left h, one_pow, one_mul]
        exact (by simpa only [pow_zero, one_mul] using hB (mem_image_of_mem _ hw) :
          ‖G.val w‖ ≤ B).trans (le_max_right _ _)
      · rw [max_eq_right h]
        exact (by simpa only [norm_mul, norm_pow] using hM (mem_image_of_mem _ hw) :
          ‖w‖^n * ‖G.val w‖ ≤ M).trans (le_max_left _ _)

/-- A purely imaginary displacement acts continuously on every open-strip
Schwartz–Bergman test space. -/
def schwartzBergmanVerticalShift (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I)
    (hne : I.Nonempty) (d : ℂ) (hd : d.re = 0) :
    SchwartzBergman I →L[ℂ] SchwartzBergman I := by
  let E := SchwartzBergman I
  let A : E →ₗ[ℂ] E :=
    { toFun := fun G ↦ ⟨fun z ↦ G.val (z+d), verticalShift_mem d hd G⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  have hre (z : ℂ) : (z+d).re = z.re := by simp [hd]
  have hEval (z : ℂ) (hz : z.re ∈ I) : Continuous (fun G : E ↦ G.val z) := by
    obtain ⟨e, he⟩ := exists_schwartzBergman_jetEvaluation hI hord z hz 0
    exact e.continuous.congr (fun G ↦ (he G).trans (congrFun iteratedDeriv_zero z))
  have hgraph : IsClosed (A.graph : Set (E × E)) := by
    rw [show (A.graph : Set (E × E)) =
      ⋂ (z : ℂ) (_hz : z.re ∈ I), {p | p.2.val z = p.1.val (z+d)} from by
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
          by_cases hz : z.re ∈ I
          · exact h z hz
          · exact (p.2.property.1 (show z ∈ (Complex.re ⁻¹' I)ᶜ from hz)).trans
              ((A p.1).property.1 (show z ∈ (Complex.re ⁻¹' I)ᶜ from hz)).symm]
    exact isClosed_iInter fun z ↦ isClosed_iInter fun hz ↦
      isClosed_eq ((hEval z hz).comp continuous_snd)
        ((hEval (z+d) (by rwa [hre])).comp continuous_fst)
  have hc : Continuous A := by
    obtain ⟨ha, hp, hm, hc⟩ := schwartzBergman_frechet I hI hord hne
    letI : IsTopologicalAddGroup E := ha
    letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace _
    letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    letI : CompleteSpace E := hc
    letI : MetrizableSpace E := hm
    letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
    letI : T2Space (PositiveRealExponentialDecay I) :=
      (positiveRealExponentialDecay_isEmbedding I hne).t2Space
    letI : T2Space E := ((positiveRealFourierMellin I hI hord hne).symm.toHomeomorph.isEmbedding).t2Space
    exact frechet_continuous_of_closed_graph A hgraph
  exact ⟨A, hc⟩

@[simp] theorem schwartzBergmanVerticalShift_apply (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I)
    (hne : I.Nonempty) (d : ℂ) (hd : d.re = 0) (G : SchwartzBergman I) (z : ℂ) :
    (schwartzBergmanVerticalShift I hI hord hne d hd G).val z = G.val (z+d) := rfl

/-- Vertical translation is a continuous linear automorphism of the strip
space, with inverse given by the opposite translation. -/
def schwartzBergmanVerticalShiftEquiv (I : Set ℝ) (hI : IsOpen I) (hord : OrdConnected I)
    (hne : I.Nonempty) (d : ℂ) (hd : d.re = 0) :
    SchwartzBergman I ≃L[ℂ] SchwartzBergman I := by
  let A := schwartzBergmanVerticalShift I hI hord hne d hd
  let B := schwartzBergmanVerticalShift I hI hord hne (-d) (by simp [hd])
  refine ⟨⟨A.toLinearMap, B, ?_, ?_⟩, A.continuous, B.continuous⟩
  · intro g
    exact Subtype.ext (funext fun z ↦ by
      change g.val (z + -d + d) = g.val z
      simp)
  · intro g
    exact Subtype.ext (funext fun z ↦ by
      change g.val (z + d + -d) = g.val z
      simp)

@[simp] theorem schwartzBergmanVerticalShiftEquiv_apply (I : Set ℝ) (hI : IsOpen I)
    (hord : OrdConnected I) (hne : I.Nonempty) (d : ℂ) (hd : d.re = 0)
    (g : SchwartzBergman I) (z : ℂ) :
    (schwartzBergmanVerticalShiftEquiv I hI hord hne d hd g).val z = g.val (z+d) := rfl

private def decayWeightCongr {I J : Set ℝ} (h : I = J) :
    PositiveRealExponentialDecay I ≃L[ℂ] PositiveRealExponentialDecay J := by
  subst J
  exact ContinuousLinearEquiv.refl ℂ _

private theorem decayWeightCongr_val {I J : Set ℝ} (h : I = J)
    (f : PositiveRealExponentialDecay I) : (decayWeightCongr h f).val = f.val := by
  subst J
  rfl

/-- In logarithmic coordinates, a vertical Mellin translation modulates
the original profile by the corresponding unitary exponential. -/
theorem schwartzBergmanVerticalShift_mellin_inverse_apply {I : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (d : ℂ) (hd : d.re = 0) (G : SchwartzBergman I) (t : ℝ) :
    ((positiveRealFourierMellin I hI hIo hIn).symm
        (schwartzBergmanVerticalShift I hI hIo hIn d hd G)).val t =
      Complex.exp (d * (t : ℂ)) * ((positiveRealFourierMellin I hI hIo hIn).symm G).val t := by
  let M := positiveRealFourierMellin I hI hIo hIn
  let u := M.symm G
  have h : (fun x : ℝ ↦ x-d.re) '' I = I := by simp [hd]
  let v := decayWeightCongr h (positiveRealExponentialDecay_complexTwist I hIn d u)
  have hv (x : ℝ) : v.val x = Complex.exp (d * (x : ℂ)) * u.val x := by
    change (decayWeightCongr h (positiveRealExponentialDecay_complexTwist I hIn d u)).val x = _
    rw [decayWeightCongr_val, positiveRealExponentialDecay_complexTwist_apply]
  have he : M v = schwartzBergmanVerticalShift I hI hIo hIn d hd G := by
    apply Subtype.ext
    funext z
    by_cases hz : z.re ∈ I
    · have hz' : (z+d).re ∈ I := by simpa [Complex.add_re, hd] using hz
      rw [schwartzBergmanVerticalShift_apply, ← M.apply_symm_apply G]
      change (M v).val z = (M u).val (z+d)
      simp only [M, positiveRealFourierMellin_apply _ hI hIo hIn _ _ hz,
        positiveRealFourierMellin_apply _ hI hIo hIn _ _ hz', mellin_eq_log_integral, Real.log_exp, hv]
      congr 1
      funext x
      rw [add_mul, Complex.exp_add, mul_assoc]
    · exact ((M v).property.1 hz).trans
        ((schwartzBergmanVerticalShift I hI hIo hIn d hd G).property.1 hz).symm
  change (M.symm (schwartzBergmanVerticalShift I hI hIo hIn d hd G)).val t = _
  rw [← he, M.symm_apply_apply]
  exact hv t

private theorem entire_twist_weights (d : ℂ) : (fun x : ℝ ↦ x - d.re) '' univ = univ := by
  apply eq_univ_of_forall
  intro x
  exact ⟨x + d.re, mem_univ _, add_sub_cancel_right _ _⟩

private abbrev EntireBergman := SchwartzBergman (univ : Set ℝ)
private abbrev EntireDecay := PositiveRealExponentialDecay (univ : Set ℝ)

private def entireMellinEquiv : EntireDecay ≃L[ℂ] EntireBergman :=
  positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty

/-- All complex translations of the spectral parameter are continuous linear
automorphisms of the entire Schwartz–Bergman space. In Mellin coordinates they
are multiplication by the corresponding complex power of the modulus. -/
def schwartzBergmanEntireShift (d : ℂ) : EntireBergman ≃L[ℂ] EntireBergman :=
  (entireMellinEquiv.symm.trans
    ((positiveRealExponentialDecay_complexTwist univ univ_nonempty d).trans
      (decayWeightCongr (entire_twist_weights d)))).trans entireMellinEquiv

/-- The entire spectral shift multiplies the logarithmic profile by the
corresponding complex exponential. -/
theorem schwartzBergmanEntireShift_inverse_profile (d : ℂ) (G : EntireBergman) (t : ℝ) :
    ((positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty).symm
      (schwartzBergmanEntireShift d G)).val t =
      Complex.exp (d * (t : ℂ)) *
        ((positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty).symm G).val t := by
  change (entireMellinEquiv.symm (entireMellinEquiv
      (decayWeightCongr (entire_twist_weights d)
        (positiveRealExponentialDecay_complexTwist univ univ_nonempty d (entireMellinEquiv.symm G))))).val t = _
  rw [entireMellinEquiv.symm_apply_apply, decayWeightCongr_val,
    positiveRealExponentialDecay_complexTwist_apply]
  rfl

@[simp] theorem schwartzBergmanEntireShift_apply (d : ℂ) (G : EntireBergman) (z : ℂ) :
    (schwartzBergmanEntireShift d G).val z = G.val (z + d) := by
  let f := entireMellinEquiv.symm G
  let h := decayWeightCongr (entire_twist_weights d)
    (positiveRealExponentialDecay_complexTwist univ univ_nonempty d f)
  have hf : entireMellinEquiv f = G := entireMellinEquiv.apply_symm_apply _
  change (entireMellinEquiv h).val z = G.val (z + d)
  rw [← hf]
  have hM (u : EntireDecay) (w : ℂ) :
      (entireMellinEquiv u).val w = mellin (fun t ↦ u.val (Real.log t)) w :=
    positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty u w (mem_univ _)
  rw [hM, hM, ← mellin_cpow_smul _ z d]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht₀ : 0 < t := ht
  have hp : (t : ℂ) ^ d = Complex.exp (d * (Real.log t : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht₀.ne'),
      ← Complex.ofReal_log ht₀.le, mul_comm]
  simp only [h, decayWeightCongr_val, positiveRealExponentialDecay_complexTwist_apply, hp, smul_eq_mul]

end

end Masullo
