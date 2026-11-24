import SLocalOrdinaryPairedMellin
import ModulatedExponentialRadial

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology TopologicalSpace

open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

private abbrev RightStrip := Ioi (0 : ℝ)
private abbrev LeftStrip := Iio (1 : ℝ)
private abbrev Overlap := Ioo (0 : ℝ) 1
private abbrev RightBergman := SchwartzBergman RightStrip
private abbrev LeftBergman := SchwartzBergman LeftStrip
private abbrev OverlapBergman := SchwartzBergman Overlap

private theorem bergman_ext {I : Set ℝ} {u v : SchwartzBergman I}
    (h : EqOn u.val v.val (Complex.re ⁻¹' I)) : u = v := by
  apply Subtype.ext
  funext z
  by_cases hz : z.re ∈ I
  · exact h hz
  · exact (u.property.1 hz).trans (v.property.1 hz).symm

private def boundedStripMultiplier {I J : Set ℝ} (hIJ : J ⊆ I) (w : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ w (Complex.re ⁻¹' J))
    (hb : ∀ l r : ℝ, l ≤ r → Icc l r ⊆ J →
      ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
        ‖w z‖ ≤ C * (1+|z.im|)^k)
    (p : SchwartzBergman I) : SchwartzBergman J := by
  let f (z : ℂ) := if z.re ∈ J then w z * p.val z else 0
  refine ⟨f, ?_, ?_, ?_⟩
  · intro z hz
    exact ite_eq_right hz
  · have hw : DifferentiableOn ℂ w (Complex.re ⁻¹' J) :=
      fun z hz ↦ (ha z hz).differentiableAt.differentiableWithinAt
    have hD : DifferentiableOn ℂ (fun z ↦ w z * p.val z) (Complex.re ⁻¹' J) :=
      hw.mul
        (p.property.2.1.mono fun _ hz ↦ hIJ hz)
    exact hD.congr fun z hz ↦ ite_eq_left hz
  · intro l r hlr hsub n
    obtain ⟨C,k,hC,hw⟩ := hb l r hlr hsub
    obtain ⟨A,hA⟩ := p.property.2.2 l r hlr (hsub.trans hIJ) n
    obtain ⟨B,hB⟩ := p.property.2.2 l r hlr (hsub.trans hIJ) (n+k)
    refine ⟨C * 2^k * max (max A 0) (max B 0), ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    change ‖z^n * f z‖ ≤ _
    rw [show f z = w z * p.val z from ite_eq_left (hsub hz),
      show z^n * (w z * p.val z) = w z * (z^n * p.val z) by ring, norm_mul]
    have hbase : 1 + |z.im| ≤ 2 * max 1 ‖z‖ := by
      linarith [le_max_left (1:ℝ) ‖z‖, (Complex.abs_im_le_norm z).trans (le_max_right 1 ‖z‖)]
    calc
      _ ≤ (C * (1+|z.im|)^k) * ‖z^n * p.val z‖ :=
        mul_le_mul_of_nonneg_right (hw z hz) (norm_nonneg _)
      _ ≤ (C * (2 * max 1 ‖z‖)^k) * ‖z^n * p.val z‖ := by gcongr
      _ = C * 2^k * ((max 1 ‖z‖)^k * ‖z^n * p.val z‖) := by rw [mul_pow]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total ‖z‖ 1 with h | h
        · rw [max_eq_left h, one_pow, one_mul]
          exact (hA (mem_image_of_mem _ hz)).trans
            ((le_max_left _ _).trans (le_max_left _ _))
        · rw [max_eq_right h, ← norm_pow, ← norm_mul, ← mul_assoc, ← pow_add, add_comm k n]
          exact (hB (mem_image_of_mem _ hz)).trans
            ((le_max_left _ _).trans (le_max_right _ _))

private theorem bergmanContinuous_of_closedGraph {I J : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (hJ : IsOpen J) (hJo : OrdConnected J) (hJn : J.Nonempty)
    (A : SchwartzBergman I →ₗ[ℂ] SchwartzBergman J)
    (h : IsClosed (A.graph : Set (SchwartzBergman I × SchwartzBergman J))) : Continuous A := by
  obtain ⟨hXadd,hXp,hXm,hXc⟩ := schwartzBergman_frechet I hI hIo hIn
  obtain ⟨hYadd,hYp,hYm,hYc⟩ := schwartzBergman_frechet J hJ hJo hJn
  let X := SchwartzBergman I
  let Y := SchwartzBergman J
  letI : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  letI : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace X := hXc
  letI : CompleteSpace Y := hYc
  letI : MetrizableSpace X := hXm
  letI : MetrizableSpace Y := hYm
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  exact frechet_continuous_of_closed_graph A h

/-- Restriction followed by multiplication by a holomorphic multiplier of
polynomial growth is continuous between the indicated Bergman spaces. -/
def schwartzBergmanRestrictMul {I J : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (hJ : IsOpen J) (hJo : OrdConnected J) (hJn : J.Nonempty)
    (hIJ : J ⊆ I) (w : ℂ → ℂ) (ha : AnalyticOnNhd ℂ w (Complex.re ⁻¹' J))
    (hb : ∀ l r : ℝ, l ≤ r → Icc l r ⊆ J →
      ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
        ‖w z‖ ≤ C * (1+|z.im|)^k) :
    SchwartzBergman I →L[ℂ] SchwartzBergman J := by
  let A : SchwartzBergman I →ₗ[ℂ] SchwartzBergman J :=
    { toFun := boundedStripMultiplier hIJ w ha hb
      map_add' := fun p q ↦ bergman_ext fun z hz ↦ by
        change z.re ∈ J at hz
        change (if z.re ∈ J then w z * (p.val z + q.val z) else 0) =
          (if z.re ∈ J then w z * p.val z else 0) + (if z.re ∈ J then w z * q.val z else 0)
        simp only [ite_eq_left hz, mul_add]
      map_smul' := fun a p ↦ bergman_ext fun z hz ↦ by
        change z.re ∈ J at hz
        change (if z.re ∈ J then w z * (a * p.val z) else 0) =
          a * (if z.re ∈ J then w z * p.val z else 0)
        simp only [ite_eq_left hz]
        ring }
  have he (p : SchwartzBergman I) (z : ℂ) (hz : z.re ∈ J) : (A p).val z = w z * p.val z :=
    ite_eq_left hz
  refine ⟨A, bergmanContinuous_of_closedGraph hI hIo hIn hJ hJo hJn A ?_⟩
  have hgraph : (A.graph : Set (SchwartzBergman I × SchwartzBergman J)) =
      ⋂ (z : ℂ) (_ : z.re ∈ J), {p | p.2.val z = w z * p.1.val z} := by
    ext p
    change p ∈ A.graph ↔ _
    rw [LinearMap.mem_graph_iff]
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h z hz
      rw [h, he p.1 z hz]
    · intro h
      exact bergman_ext (fun z hz ↦ (h z hz).trans (he p.1 z hz).symm)
  rw [hgraph]
  exact isClosed_iInter fun z ↦ isClosed_iInter fun hz ↦ isClosed_eq
    ((bergman_continuous_evaluation hJ hJo z hz).comp continuous_snd)
    (continuous_const.mul ((bergman_continuous_evaluation hI hIo z (hIJ hz)).comp continuous_fst))

theorem schwartzBergmanRestrictMul_apply {I J : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (hJ : IsOpen J) (hJo : OrdConnected J) (hJn : J.Nonempty)
    (hIJ : J ⊆ I) (w : ℂ → ℂ) (ha : AnalyticOnNhd ℂ w (Complex.re ⁻¹' J))
    (hb : ∀ l r : ℝ, l ≤ r → Icc l r ⊆ J →
      ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
        ‖w z‖ ≤ C * (1+|z.im|)^k)
    (p : SchwartzBergman I) (z : ℂ) (hz : z.re ∈ J) :
    (schwartzBergmanRestrictMul hI hIo hIn hJ hJo hJn hIJ w ha hb p).val z = w z * p.val z :=
  ite_eq_left hz

private abbrev OverlapGrowth (ρ : ℂ → ℂ) :=
  ∀ l r : ℝ, 0 < l → r < 1 →
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc l r →
      ‖ρ z‖ ≤ C * (1 + |z.im|)^k

private def overlapRestrict :
    RightBergman →L[ℂ] OverlapBergman :=
  schwartzBergmanRestrictMul isOpen_Ioi ordConnected_Ioi nonempty_Ioi
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr zero_lt_one)
    (fun _ h ↦ h.1) (fun _ ↦ 1) (fun _ _ ↦ analyticAt_const)
    (fun _ _ _ _ ↦ ⟨1, 0, zero_le_one, by simp⟩)

private def overlapMultiply (ρ : ℂ → ℂ)
    (ha : ∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ ρ z)
    (hb : OverlapGrowth ρ) : LeftBergman →L[ℂ] OverlapBergman :=
  schwartzBergmanRestrictMul isOpen_Iio ordConnected_Iio nonempty_Iio
    isOpen_Ioo ordConnected_Ioo (nonempty_Ioo.mpr zero_lt_one)
    (fun _ h ↦ h.2) ρ (fun z hz ↦ ha z hz.1 hz.2)
    (fun l r hlr hsub ↦ hb l r (hsub ⟨le_rfl, hlr⟩).1 (hsub ⟨hlr, le_rfl⟩).2)

/-- Difference of the two holomorphic profiles after restricting to the overlap. -/
def sLocalBergmanCechDifference (ρ : ℂ → ℂ)
    (ha : ∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ ρ z)
    (hb : OverlapGrowth ρ) :
    (RightBergman × LeftBergman) →L[ℂ] OverlapBergman :=
  overlapRestrict.comp (ContinuousLinearMap.fst ℂ RightBergman LeftBergman) -
    (overlapMultiply ρ ha hb).comp (ContinuousLinearMap.snd ℂ RightBergman LeftBergman)

theorem sLocalBergmanCechDifference_apply (ρ : ℂ → ℂ)
    (ha : ∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ ρ z) (hb : OverlapGrowth ρ)
    (p : RightBergman × LeftBergman) (z : ℂ) (hz : z.re ∈ Overlap) :
    (sLocalBergmanCechDifference ρ ha hb p).val z = p.1.val z - ρ z * p.2.val z := by
  have hR : (overlapRestrict p.1).val z = p.1.val z :=
    (ite_eq_left hz).trans (one_mul _)
  have hL : (overlapMultiply ρ ha hb p.2).val z = ρ z * p.2.val z :=
    ite_eq_left hz
  exact congrArg₂ (· - ·) hR hL

theorem sLocalBergmanCechDifference_eq_zero_iff (ρ : ℂ → ℂ)
    (ha : ∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ ρ z) (hb : OverlapGrowth ρ)
    (p : RightBergman × LeftBergman) :
    sLocalBergmanCechDifference ρ ha hb p = 0 ↔ p ∈ sLocalBergmanGluing ρ := by
  constructor
  · intro hp z hz hr
    apply sub_eq_zero.mp
    rw [← sLocalBergmanCechDifference_apply ρ ha hb p z ⟨hz, hr⟩, hp]
    rfl
  · intro hp
    apply bergman_ext
    intro z hz
    rw [sLocalBergmanCechDifference_apply ρ ha hb p z hz, hp z hz.1 hz.2, sub_self]
    rfl

private theorem overlapGrowth_shift {ρ : ℂ → ℂ} (hb : OverlapGrowth ρ)
    (d : ℂ) (hd : d.re = 0) : OverlapGrowth (fun z ↦ ρ (z+d)) := by
  intro l r hl hr
  obtain ⟨C,k,hC,h⟩ := hb l r hl hr
  refine ⟨C * (1+|d.im|)^k, k, by positivity, fun z hz ↦ ?_⟩
  have hz' : (z+d).re ∈ Icc l r := by simpa [Complex.add_re, hd] using hz
  have hbase : 1 + |(z+d).im| ≤ (1+|d.im|) * (1+|z.im|) := by
    rw [Complex.add_im]
    have hm : 0 ≤ |d.im| * |z.im| := by positivity
    nlinarith [abs_add_le z.im d.im]
  calc
    _ ≤ C * (1 + |(z+d).im|)^k := h _ hz'
    _ ≤ C * ((1+|d.im|) * (1+|z.im|))^k := by gcongr
    _ = _ := by rw [mul_pow, mul_assoc]

private abbrev RightProfile := PositiveRealExponentialDecay RightStrip
private abbrev OverlapProfile := PositiveRealExponentialDecay Overlap

def cechPhaseMellin {I : Set ℝ} (hI : IsOpen I) (hIo : OrdConnected I)
    (hIn : I.Nonempty) (α : ℂ) (hα : α.re = 0) :
    PositiveRealExponentialDecay I ≃L[ℂ] SchwartzBergman I :=
  (positiveRealFourierMellin I hI hIo hIn).trans
    (schwartzBergmanVerticalShiftEquiv I hI hIo hIn α hα)

private abbrev rightPhaseMellin := cechPhaseMellin isOpen_Ioi ordConnected_Ioi
  (nonempty_Ioi : RightStrip.Nonempty)

private abbrev overlapPhaseMellin := cechPhaseMellin isOpen_Ioo ordConnected_Ioo
  (nonempty_Ioo.mpr zero_lt_one : Overlap.Nonempty)

/-- The Mellin transform in a unitary chart is evaluated at the phase-shifted argument. -/
theorem cechPhaseMellin_apply {I : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (α : ℂ) (hα : α.re = 0) (u : PositiveRealExponentialDecay I) (z : ℂ) (hz : z.re ∈ I) :
    (cechPhaseMellin hI hIo hIn α hα u).val z =
      mellin (fun t ↦ u.val (Real.log t)) (z+α) := by
  have he : (z+α).re ∈ I := by simpa [Complex.add_re,hα] using hz
  exact positiveRealFourierMellin_apply _ hI hIo hIn u (z+α) he

/-- The upper difference uses ordinary restriction in its first coordinate. -/
def sLocalCechProfileRestrict (u : RightProfile) : OverlapProfile :=
  ⟨u.val, (Submodule.mem_iInf _).mpr fun a ↦
    (Submodule.mem_iInf _).mp u.property ⟨a.val, a.property.1⟩⟩

private theorem overlapPhaseMellin_restrict (α : ℂ) (hα : α.re = 0) (u : RightProfile) :
    overlapPhaseMellin α hα (sLocalCechProfileRestrict u) =
      overlapRestrict (rightPhaseMellin α hα u) := by
  apply bergman_ext
  intro z hz
  change z.re ∈ Overlap at hz
  have hr : (overlapRestrict (rightPhaseMellin α hα u)).val z =
      (rightPhaseMellin α hα u).val z := (ite_eq_left hz).trans (one_mul _)
  exact (cechPhaseMellin_apply _ _ _ α hα (sLocalCechProfileRestrict u) z hz).trans
    ((cechPhaseMellin_apply _ _ _ α hα u z hz.1).symm.trans hr.symm)

private theorem cechPhaseMellin_inverse_apply {I : Set ℝ}
    (hI : IsOpen I) (hIo : OrdConnected I) (hIn : I.Nonempty)
    (α : ℂ) (hα : α.re = 0) (G : SchwartzBergman I) (t : ℝ) :
    ((cechPhaseMellin hI hIo hIn α hα).symm G).val t =
      Complex.exp ((-α) * (t : ℂ)) * ((positiveRealFourierMellin I hI hIo hIn).symm G).val t :=
  schwartzBergmanVerticalShift_mellin_inverse_apply hI hIo hIn (-α) (by simp [hα]) G t

/-- The pure reflection before multiplying by the Tate factor. -/
def sLocalCechProfileReflection : RightProfile ≃L[ℂ] PositiveRealExponentialDecay LeftStrip :=
  (positiveRealFourierMellin RightStrip isOpen_Ioi ordConnected_Ioi nonempty_Ioi).trans
    (bergmanReflectOneEquiv.trans
      (positiveRealFourierMellin LeftStrip isOpen_Iio ordConnected_Iio nonempty_Iio).symm)

/-- In logarithmic coordinates, reflection sends the profile at t to
exp(-t) times its value at -t. -/
theorem sLocalCechProfileReflection_apply (u : RightProfile) (t : ℝ) :
    (sLocalCechProfileReflection u).val t = Complex.exp (-(t : ℂ)) * u.val (-t) := by
  let v : PositiveRealExponentialDecay LeftStrip :=
    ⟨fun x ↦ Complex.exp (-(x : ℂ)) * u.val (-x), (Submodule.mem_iInf _).mpr fun a ↦ by
      let b : RightStrip := ⟨1-a.val, show 0 < 1-a.val from sub_pos.mpr a.property⟩
      let n := (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ).toContinuousLinearEquiv
      refine ⟨schwartzChangeVariable ℂ n (logExponentialDecayTwist RightStrip b u), funext fun x ↦ ?_⟩
      change (logExponentialDecayTwist RightStrip b u) (-x) =
        (Real.exp (a.val*x) : ℂ) * (Complex.exp (-(x : ℂ)) * u.val (-x))
      calc
        _ = (Real.exp ((1-a.val)*(-x)) : ℂ) * u.val (-x) :=
          logExponentialDecayTwist_apply RightStrip b u (-x)
        _ = _ := by
          simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
            Complex.ofReal_neg, ← mul_assoc, ← Complex.exp_add]
          exact congrArg (fun w : ℂ ↦ Complex.exp w * u.val (-x)) (by ring)⟩
  let M := positiveRealFourierMellin LeftStrip isOpen_Iio ordConnected_Iio nonempty_Iio
  let N := positiveRealFourierMellin RightStrip isOpen_Ioi ordConnected_Ioi nonempty_Ioi
  have hv : M v = bergmanReflectOneEquiv (N u) := by
    apply bergman_ext
    intro z hz
    change z.re < 1 at hz
    have hz' : 0 < (1-z).re := by simpa [Complex.sub_re, sub_pos] using hz
    change (M v).val z = (N u).val (1-z)
    rw [show (M v).val z = mellin (fun x ↦ v.val (Real.log x)) z from
        positiveRealFourierMellin_apply _ isOpen_Iio ordConnected_Iio nonempty_Iio v z hz,
      show (N u).val (1-z) = mellin (fun x ↦ u.val (Real.log x)) (1-z) from
        positiveRealFourierMellin_apply _ isOpen_Ioi ordConnected_Ioi nonempty_Ioi u (1-z) hz',
      mellin_eq_log_integral, mellin_eq_log_integral]
    simp only [Real.log_exp]
    rw [← integral_neg_eq_self (fun x : ℝ ↦ Complex.exp (z * (x : ℂ)) * v.val x) volume]
    apply integral_congr_ae
    filter_upwards [] with x
    change Complex.exp (z * ((-x : ℝ) : ℂ)) *
      (Complex.exp (-((-x : ℝ) : ℂ)) * u.val (- -x)) =
        Complex.exp ((1-z) * (x : ℂ)) * u.val x
    rw [neg_neg, Complex.ofReal_neg, neg_neg, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  change (M.symm (bergmanReflectOneEquiv (N u))).val t = _
  rw [← hv, M.symm_apply_apply]

/-- With the same unitary phase in the two Mellin integrals, pure reflection
uses the second argument 1-s-2α in the shifted spectral chart. -/
theorem sLocalCechProfileReflection_mellin (α : ℂ) (hα : α.re = 0)
    (u : RightProfile) (z : ℂ) :
    (cechPhaseMellin isOpen_Iio ordConnected_Iio nonempty_Iio α hα
      (sLocalCechProfileReflection u)).val z =
    (rightPhaseMellin α hα u).val (1-z-(α+α)) := by
  let M := positiveRealFourierMellin LeftStrip isOpen_Iio ordConnected_Iio nonempty_Iio
  let N := positiveRealFourierMellin RightStrip isOpen_Ioi ordConnected_Ioi nonempty_Ioi
  change (M (M.symm (bergmanReflectOneEquiv (N u)))).val (z+α) =
    (N u).val (1-z-(α+α)+α)
  rw [M.apply_symm_apply, bergmanReflectOneEquiv_apply,
    show (1 : ℂ)-(z+α) = 1-z-(α+α)+α by ring]

def cechPhaseReflection (α : ℂ) (hα : α.re = 0) :
    (RightBergman × RightBergman) ≃L[ℂ] (RightBergman × LeftBergman) :=
  (ContinuousLinearEquiv.refl ℂ RightBergman).prodCongr
    ((schwartzBergmanVerticalShiftEquiv RightStrip isOpen_Ioi ordConnected_Ioi nonempty_Ioi
      (-(α+α)) (by simp [hα])).trans bergmanReflectOneEquiv)

theorem cechPhaseReflection_apply (α : ℂ) (hα : α.re = 0)
    (p : RightBergman × RightBergman) (z : ℂ) :
    ((cechPhaseReflection α hα p).2).val z = p.2.val (1-z-(α+α)) := by
  rfl

private theorem cechPhaseReflection_symm_apply (α : ℂ) (hα : α.re = 0)
    (p : RightBergman × LeftBergman) (z : ℂ) :
    (((cechPhaseReflection α hα).symm p).2).val z = p.2.val (1-z-(α+α)) := by
  have he := congrArg (fun q : RightBergman × LeftBergman ↦ q.2.val (1-z-(α+α)))
    ((cechPhaseReflection α hα).apply_symm_apply p)
  rw [cechPhaseReflection_apply, show (1 : ℂ)-(1-z-(α+α))-(α+α) = z by ring] at he
  exact he

section ActualSequence

set_option maxHeartbeats 1400000

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev V (v : S) := v.val.adicCompletion F

local instance : LocallyCompactSpace (SAdeles F S)ˣ := sLocalIdeles_locallyCompact F S

local instance : SecondCountableTopology (SAdeles F S)ˣ := sLocalIdeles_secondCountable F S

local instance : LocallyCompactSpace (SIdeleQuotient F S) :=
  QuotientGroup.isOpenQuotientMap_mk.locallyCompactSpace

local instance : SecondCountableTopology (SIdeleQuotient F S) :=
  TopologicalSpace.Quotient.secondCountableTopology
    (QuotientGroup.isOpenMap_coe (N := sUnitImage F S))

local instance : T2Space (SIdeleQuotient F S) := by
  letI : T1Space (SIdeleQuotient F S) := QuotientGroup.t1Space_iff.mpr (sUnitImage_closed F S)
  exact inferInstance

/-- The logarithmic modulus used in the weighted Schwartz–Bruhat space. -/
def sLocalCechModulation : SIdeleQuotient F S →ₜ* Multiplicative ℝ where
  toFun q := Multiplicative.ofAdd (Real.log (sLocalClassModulus F S q))
  map_one' := by simp [sLocalClassModulus]
  map_mul' x y := by
    change Multiplicative.ofAdd (Real.log (sLocalClassModulus F S (x*y))) =
      Multiplicative.ofAdd (Real.log (sLocalClassModulus F S x) + Real.log (sLocalClassModulus F S y))
    rw [← Real.log_mul (sLocalClassModulus_pos F S x).ne' (sLocalClassModulus_pos F S y).ne']
    congr 2
    unfold sLocalClassModulus
    rw [map_mul]
    rfl
  continuous_toFun := by
    have h (q : SIdeleQuotient F S) :
        Real.log (sLocalClassModulus F S q) = ((sLocalZetaSplit F S).symm q).1 := by
      simpa only [Homeomorph.apply_symm_apply] using
        sLocalZetaSplit_logModulus F S ((sLocalZetaSplit F S).symm q)
    exact continuous_ofAdd.comp
      ((continuous_fst.comp (sLocalZetaSplit F S).symm.continuous).congr (fun q ↦ (h q).symm))

theorem sLocalCechModulation_proper : IsProperMap (sLocalCechModulation F S) := by
  letI : CompactSpace (K F S) := sLocalThetaNormOne_compact F S
  have he : (sLocalCechModulation F S : SIdeleQuotient F S → Multiplicative ℝ) =
      Multiplicative.ofAdd ∘ Prod.fst ∘ (sLocalZetaSplit F S).symm := by
    funext q
    change Multiplicative.ofAdd (Real.log (sLocalClassModulus F S q)) =
      Multiplicative.ofAdd ((sLocalZetaSplit F S).symm q).1
    rfl
  rw [he]
  let e : ℝ ≃ₜ Multiplicative ℝ :=
    ⟨⟨Multiplicative.ofAdd, Multiplicative.toAdd, fun _ ↦ rfl, fun _ ↦ rfl⟩,
      continuous_ofAdd, continuous_toAdd⟩
  exact e.isProperMap.comp
    (isProperMap_fst_of_compactSpace.comp (sLocalZetaSplit F S).symm.isProperMap)

private def cechNormOne (k : (sLocalCechModulation F S).toMonoidHom.ker) : K F S :=
  ⟨k.val, by
    change sQuotientNorm F S k.val = 1
    have hk : Real.log (sLocalClassModulus F S k.val) = 0 :=
      congrArg Multiplicative.toAdd k.property
    apply Units.ext
    apply NNReal.eq
    change sLocalClassModulus F S k.val = 1
    exact (Real.exp_log (sLocalClassModulus_pos F S k.val)).symm.trans
      (hk ▸ Real.exp_zero)⟩

/-- The norm-one character on the kernel of the logarithmic modulus. -/
def sLocalCechCharacter (ω : PontryaginDual (K F S)) :
    PontryaginDual (sLocalCechModulation F S).toMonoidHom.ker :=
  (show CircleCharacter (K F S) from ω).comp
    { toFun := cechNormOne F S
      map_one' := Subtype.ext rfl
      map_mul' _ _ := Subtype.ext rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _ }

/-- The norm-one isotype in the actual weighted inductive-limit space. -/
abbrev sLocalCechDecayIsotype (ω : PontryaginDual (K F S)) (I : Set ℝ) : Type _ := by
  let m : SIdeleQuotient F S →ₜ* Multiplicative ℝ := sLocalCechModulation F S
  let w : PontryaginDual m.toMonoidHom.ker := sLocalCechCharacter F S ω
  exact ↥(@modulatedDecayIsotype (SIdeleQuotient F S) inferInstance inferInstance inferInstance
    inferInstance inferInstance m w I)

private abbrev GlobalProfile (ω : PontryaginDual (K F S)) := sLocalCechDecayIsotype F S ω RightStrip

/-- Evaluation of a weighted Schwartz–Bruhat isotype on the S-local class group. -/
def sLocalCechIsotypeEval (ω : PontryaginDual (K F S)) (u : GlobalProfile F S ω) :
    SIdeleQuotient F S → ℂ := u.val.val

/-- The actual norm-one isotype for the weighted inductive-limit topology
is identified with the scalar section profiles. -/
theorem exists_sLocalCechRadialIsotype (ω : PontryaginDual (K F S))
    (I : Set ℝ) (hI : I.Nonempty)
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t) :
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ] sLocalCechDecayIsotype F S ω I,
      ∀ u t, (e.symm u).val t = u.val.val (τ (Multiplicative.ofAdd t)) := by
  let T : Multiplicative ℝ →ₜ* SIdeleQuotient F S := ⟨τ,hτ⟩
  have hm (t : Multiplicative ℝ) : sLocalCechModulation F S (T t) = t := by
    change Multiplicative.ofAdd (Real.log (sLocalClassModulus F S (τ t))) = t
    exact congrArg Multiplicative.ofAdd ((congrArg Real.log (hmod t.toAdd)).trans (Real.log_exp _))
  let m : SIdeleQuotient F S →ₜ* Multiplicative ℝ := sLocalCechModulation F S
  let w : PontryaginDual m.toMonoidHom.ker := sLocalCechCharacter F S ω
  obtain ⟨e,_,he⟩ := @exists_modulatedDecayRadialIsotype (SIdeleQuotient F S)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance m T hm
    w I hI (sLocalCechModulation_proper F S)
  exact ⟨e,he⟩

/-- Pure reflection on the actual weighted isotypes exchanges the characters
and gives the half-plane reflection before overlap multiplication. -/
theorem exists_sLocalCechIsotypeReflection (ω : PontryaginDual (K F S))
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t) :
    ∃ J : GlobalProfile F S ω ≃L[ℂ] sLocalCechDecayIsotype F S ω⁻¹ LeftStrip,
      ∀ u (t : ℝ), (J u).val.val (τ (Multiplicative.ofAdd t)) =
        Complex.exp (-(t : ℂ)) * u.val.val (τ (Multiplicative.ofAdd (-t))) := by
  obtain ⟨epos,hpos⟩ := exists_sLocalCechRadialIsotype F S ω RightStrip nonempty_Ioi τ hτ hmod
  obtain ⟨eneg,hneg⟩ := exists_sLocalCechRadialIsotype F S ω⁻¹ LeftStrip nonempty_Iio τ hτ hmod
  let J := epos.symm.trans (sLocalCechProfileReflection.trans eneg)
  refine ⟨J, fun u t ↦ ?_⟩
  calc
    _ = (eneg.symm (J u)).val t := (hneg (J u) t).symm
    _ = (sLocalCechProfileReflection (epos.symm u)).val t :=
      congrArg (fun v : PositiveRealExponentialDecay LeftStrip ↦ v.val t)
        (eneg.symm_apply_apply _)
    _ = _ := (sLocalCechProfileReflection_apply _ t).trans
      (congrArg (Complex.exp (-(t : ℂ)) * ·) (hpos u (-t)))

/-- Section phases account for every continuous unitary character in the
statement of the Čech theorem. -/
theorem existsUnique_sLocalCechCharacter_phase (χ : PontryaginDual (SIdeleQuotient F S))
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ) :
    ∃! α : ℂ, α.re = 0 ∧ ∀ t : ℝ,
      (χ (τ (Multiplicative.ofAdd t)) : ℂ) = Complex.exp (α * (t : ℂ)) := by
  let γ := (Circle.coeHom.comp (χ.toMonoidHom.comp τ)).toHomUnits
  have hγ : Continuous (fun t : ℝ ↦ (γ (Multiplicative.ofAdd t) : ℂ)) :=
    (continuous_subtype_val.comp (χ.continuous.comp hτ)).comp continuous_ofAdd
  obtain ⟨α,hα,hUnique⟩ := complex_oneParameter_exp γ hγ
  have hre : α.re = 0 := by
    have he := congrArg norm (hα 1)
    change ‖(χ (τ (Multiplicative.ofAdd (1 : ℝ))) : ℂ)‖ =
      ‖Complex.exp (α * ((1 : ℝ) : ℂ))‖ at he
    rw [Circle.norm_coe, Complex.ofReal_one, mul_one, Complex.norm_exp, ← Real.exp_zero] at he
    exact Real.exp_injective he.symm
  exact ⟨α, ⟨hre,hα⟩, fun β hβ ↦ hUnique β hβ.2⟩

variable [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  (μ : ∀ v : S, Measure (V F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable sLocalZetaUnfolding_idelesBorel

variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
  (hν : IsWeilQuotientMeasure (sUnitImage F S)
    (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F)) Measure.count
    (sLocalClassHaar F S ν))
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)]

private abbrev E := sLocalBruhatImage F S

omit [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
private theorem sectionRadialProfiles (ω : PontryaginDual (K F S))
    (τ : Multiplicative ℝ →* SIdeleQuotient F S)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (d : ℂ)
    (hphase : ∀ z (t : ℝ) (k : K F S),
      sLocalZetaWeight F S ω (z-d) (τ (Multiplicative.ofAdd t) * k.val) =
        Complex.exp (z * (t : ℂ)) * (ω k : ℂ))
    (f g : E F S) (t : ℝ) :
    let a : SIdeleQuotient F S := QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))
    sLocalHomogeneousTheta F S ν ω f.val (τ (Multiplicative.ofAdd t)) =
      Complex.exp (-d * (t : ℂ)) * sLocalHomogeneousTheta F S ν ω f.val a ∧
    sLocalHomogeneousTheta F S ν ω⁻¹ g.val (τ (Multiplicative.ofAdd t)) =
      Complex.exp (d * (t : ℂ)) * sLocalHomogeneousTheta F S ν ω⁻¹ g.val a := by
  intro a
  let b : K F S := ⟨τ (Multiplicative.ofAdd t) / a, by
    change sQuotientNorm F S (τ (Multiplicative.ofAdd t) / a) = 1
    rw [map_div, div_eq_one]
    apply Units.ext
    apply NNReal.eq
    exact (hmod t).trans (sLocalIdeleNorm_expSection F S t).symm⟩
  have htau : τ (Multiplicative.ofAdd t) = b.val * a :=
    (div_mul_cancel _ _).symm
  have hsplit : τ (Multiplicative.ofAdd t) = sLocalZetaSplit F S (t,b) :=
    htau.trans (mul_comm (b.val : SIdeleQuotient F S) a)
  have hw : sLocalZetaWeight F S ω 0 (τ (Multiplicative.ofAdd t)) =
      Complex.exp (d * (t : ℂ)) := by
    have he : τ (Multiplicative.ofAdd t) * (1 : K F S).val =
        τ (Multiplicative.ofAdd t) := mul_one (τ (Multiplicative.ofAdd t))
    refine (congrArg (sLocalZetaWeight F S ω 0) he.symm).trans ?_
    simpa only [sub_self, map_one, Circle.coe_one, mul_one] using (hphase d t (1 : K F S))
  have hχ : (ω b : ℂ) = Complex.exp (d * (t : ℂ)) := by
    calc
      _ = sLocalZetaWeight F S ω 0 (sLocalZetaSplit F S (t,b)) := by
        rw [sLocalZetaWeight_split, zero_mul, Complex.exp_zero, one_mul]
      _ = _ := (congrArg (sLocalZetaWeight F S ω 0) hsplit.symm).trans hw
  constructor
  · rw [htau, sLocalHomogeneousTheta_translate, hχ, neg_mul, Complex.exp_neg]
  · rw [htau, sLocalHomogeneousTheta_translate]
    change (((ω b : Circle)⁻¹ : Circle) : ℂ)⁻¹ * _ = _
    rw [Circle.coe_inv, inv_inv, hχ]

omit [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
private theorem recoveredSectionProfiles (ω : PontryaginDual (K F S))
    (τ : Multiplicative ℝ →* SIdeleQuotient F S)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (α d : ℂ) (hα : α.re = 0) (hd : d.re = 0)
    (hphase : ∀ z (t : ℝ) (k : K F S),
      sLocalZetaWeight F S ω (z-d) (τ (Multiplicative.ofAdd t) * k.val) =
        Complex.exp (z * (t : ℂ)) * (ω k : ℂ))
    (f : E F S) (t : ℝ) :
    let P := (cechPhaseReflection α hα).symm
      (sLocalPairedBergmanMellin_shift F S ν ω (α-d) (by simp [hα,hd])
        (Submodule.Quotient.mk f))
    ((rightPhaseMellin α hα).symm P.1).val t =
      sLocalHomogeneousTheta F S ν ω f.val (τ (Multiplicative.ofAdd t)) ∧
    ((rightPhaseMellin α hα).symm P.2).val t =
      sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val
        (τ (Multiplicative.ofAdd t)) := by
  intro P
  let δ := α-d
  have hδ : δ.re = 0 := by simp [δ,hα,hd]
  let g := sLocalSelectedFourier F S f
  let M₁ := sLocalRightBergmanMellin F S ν ω (Submodule.Quotient.mk f)
  let M₂ := sLocalRightBergmanMellin F S ν ω⁻¹ (Submodule.Quotient.mk g)
  have h₁ : P.1 =
      schwartzBergmanVerticalShift RightStrip isOpen_Ioi ordConnected_Ioi nonempty_Ioi δ hδ M₁ := by
    apply bergman_ext
    intro z hz
    change 0 < z.re at hz
    have hz' : 0 < (z+δ).re := by simpa [Complex.add_re,hδ] using hz
    change (sLocalPairedBergmanMellin_shift F S ν ω δ hδ (Submodule.Quotient.mk f)).1.val z =
      M₁.val (z+δ)
    rw [(sLocalPairedBergmanMellin_shift_apply F S ν ω δ hδ _ z).1,
      (sLocalPairedBergmanMellin_apply F S ν ω f).1 _ hz']
    exact (sLocalRightBergmanMellin_apply F S ν ω f _ hz').symm
  have h₂ : P.2 =
      schwartzBergmanVerticalShift RightStrip isOpen_Ioi ordConnected_Ioi nonempty_Ioi
        (α+d) (by simp [hα,hd]) M₂ := by
    apply bergman_ext
    intro z hz
    change 0 < z.re at hz
    let w := 1-z-(α+α)
    have hw : (w+δ).re < 1 := by
      simp only [w,Complex.add_re,Complex.sub_re,Complex.one_re,hα,hδ,add_zero,sub_zero]
      linarith
    have hwd : 1-(w+δ) = z+(α+d) := by dsimp [w,δ]; ring
    change (((cechPhaseReflection α hα).symm
      (sLocalPairedBergmanMellin_shift F S ν ω δ hδ (Submodule.Quotient.mk f))).2).val z =
        M₂.val (z+(α+d))
    rw [cechPhaseReflection_symm_apply, ← show w = 1-z-(α+α) from rfl,
      (sLocalPairedBergmanMellin_shift_apply F S ν ω δ hδ _ w).2,
      (sLocalPairedBergmanMellin_apply F S ν ω f).2 _ hw, hwd]
    exact (sLocalRightBergmanMellin_apply F S ν ω⁻¹ g _ (by simpa [hα,hd])).symm
  have hc := sectionRadialProfiles F S ν ω τ hmod d hphase f g t
  constructor
  · rw [cechPhaseMellin_inverse_apply, h₁, schwartzBergmanVerticalShift_mellin_inverse_apply,
      sLocalRightBergmanMellin_inverse_apply, ← mul_assoc, ← Complex.exp_add, hc.1]
    congr 2
    dsimp [δ]
    ring
  · rw [cechPhaseMellin_inverse_apply, h₂, schwartzBergmanVerticalShift_mellin_inverse_apply,
      sLocalRightBergmanMellin_inverse_apply, ← mul_assoc, ← Complex.exp_add, hc.2]
    congr 2
    ring

include hν in
/-- The lower Čech row is a closed embedding followed by an exact continuous
difference map. The second half-plane is written in the reflected coordinate. -/
theorem exists_sLocalCechBergman (ω : PontryaginDual (K F S)) (d : ℂ) (hd : d.re = 0) :
    ∃ (ε : ℂ → ℂ) (D : (RightBergman × LeftBergman) →L[ℂ] OverlapBergman),
      AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      IsClosedEmbedding (sLocalPairedBergmanMellin_shift F S ν ω d hd) ∧
      Function.Exact (sLocalPairedBergmanMellin_shift F S ν ω d hd) D ∧
      (∀ p z, z.re ∈ Overlap →
        (D p).val z = p.1.val z - sLocalExplicitTateFactor F S ω ε (z+d) * p.2.val z) := by
  obtain ⟨ε, hε, hε₀, ha, hb, hclosed, hRange⟩ :=
    exists_sLocalOrdinaryPaired_shift_closedEmbedding F S μ ν hν ω d hd
  let ρ (z : ℂ) := sLocalExplicitTateFactor F S ω ε (z+d)
  have hA (z : ℂ) (hz : 0 < z.re) (hr : z.re < 1) : AnalyticAt ℂ ρ z := by
    have hre : (z+d).re = z.re := by simp [Complex.add_re, hd]
    exact (ha _ (by rwa [hre]) (by rwa [hre])).comp (analyticAt_id.add analyticAt_const)
  let D := sLocalBergmanCechDifference ρ hA (overlapGrowth_shift hb d hd)
  refine ⟨ε, D, hε, hε₀, hclosed, ?_, sLocalBergmanCechDifference_apply _ _ _⟩
  intro p
  rw [hRange]
  exact sLocalBergmanCechDifference_eq_zero_iff _ _ _ _

set_option maxHeartbeats 1000000 in
include hν in
/-- Corrected S-local Čech diagram of Theorem 5.4.2.2. The Tate factor acts on
the overlap. For phase α the positive-coordinate second term is evaluated at
1-s-2α, so that reflection sends the actual quasicaracter to its Tate dual. -/
theorem exists_sLocalCech_radialDiagram (ω : PontryaginDual (K F S))
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (α : ℂ) (hα : α.re = 0) :
    ∃ (d : ℂ) (hd : d.re = 0) (ε : ℂ → ℂ)
      (U : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] (RightBergman × RightBergman))
      (A : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] (RightProfile × RightProfile))
      (D : (RightBergman × RightBergman) →L[ℂ] OverlapBergman)
      (B : (RightProfile × RightProfile) →L[ℂ] OverlapProfile),
      let M := (rightPhaseMellin α hα).prodCongr (rightPhaseMellin α hα)
      let N := overlapPhaseMellin α hα
      AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ z (t : ℝ) (k : K F S),
        sLocalZetaWeight F S ω (z-d) (τ (Multiplicative.ofAdd t) * k.val) =
          Complex.exp (z * (t : ℂ)) * (ω k : ℂ)) ∧
      (∀ q, cechPhaseReflection α hα (U q) =
        sLocalPairedBergmanMellin_shift F S ν ω (α-d) (by simp [hα,hd]) q) ∧
      (∀ q, M (A q) = U q) ∧ (∀ p, N (B p) = D (M p)) ∧
      IsClosedEmbedding U ∧ IsClosedEmbedding A ∧
      Function.Exact U D ∧ Function.Exact A B ∧
      (∀ p z, z.re ∈ Overlap →
        (D p).val z =
          p.1.val z - sLocalExplicitTateFactor F S ω ε (z+α-d) * p.2.val (1-z-(α+α))) ∧
      (∀ p z, z.re ∈ Overlap →
        (N (sLocalCechProfileRestrict p.1 - B p)).val z =
          sLocalExplicitTateFactor F S ω ε (z+α-d) *
            (rightPhaseMellin α hα p.2).val (1-z-(α+α))) ∧
      (∀ (f : E F S) (t : ℝ),
        (A (Submodule.Quotient.mk f)).1.val t =
          sLocalHomogeneousTheta F S ν ω f.val (τ (Multiplicative.ofAdd t)) ∧
        (A (Submodule.Quotient.mk f)).2.val t =
          sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val
            (τ (Multiplicative.ofAdd t))) := by
  obtain ⟨d,hd,hphase⟩ := exists_sLocalSection_phase F S ω τ hτ hmod
  let δ := α-d
  have hδ : δ.re = 0 := by simp [δ,hα,hd]
  obtain ⟨ε,D₀,hε,hε₀,hClosed,hExact,hD⟩ := exists_sLocalCechBergman F S μ ν hν ω δ hδ
  let U₀ := sLocalPairedBergmanMellin_shift F S ν ω δ hδ
  let R := cechPhaseReflection α hα
  let M := (rightPhaseMellin α hα).prodCongr (rightPhaseMellin α hα)
  let N := overlapPhaseMellin α hα
  let U := R.symm.toContinuousLinearMap.comp U₀
  let A := M.symm.toContinuousLinearMap.comp U
  let D := D₀.comp R.toContinuousLinearMap
  let B := N.symm.toContinuousLinearMap.comp (D.comp M.toContinuousLinearMap)
  have hU : ∀ q, R (U q) = U₀ q := fun q ↦ R.apply_symm_apply (U₀ q)
  have hA : ∀ q, M (A q) = U q := fun q ↦ M.apply_symm_apply (U q)
  have hB : ∀ p, N (B p) = D (M p) := fun p ↦ N.apply_symm_apply (D (M p))
  have hExact₁ : Function.Exact U D := by
    intro p
    change D₀ (R p) = 0 ↔ p ∈ range U
    rw [hExact (R p)]
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q, R.injective ((hU q).trans hq)⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q,(hU q).symm⟩
  have hExact₂ : Function.Exact A B := by
    intro p
    have he : B p = 0 ↔ D (M p) = 0 := by
      rw [← hB p, ← N.map_zero]
      exact N.injective.eq_iff.symm
    rw [he, hExact₁ (M p)]
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q,M.injective ((hA q).trans hq)⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q,(hA q).symm⟩
  have hClosed₁ : IsClosedEmbedding U := R.symm.toHomeomorph.isClosedEmbedding.comp hClosed
  have hClosed₂ : IsClosedEmbedding A := M.symm.toHomeomorph.isClosedEmbedding.comp hClosed₁
  have hDiff (p : RightBergman × RightBergman) (z : ℂ) (hz : z.re ∈ Overlap) :
      (D p).val z =
        p.1.val z - sLocalExplicitTateFactor F S ω ε (z+α-d) * p.2.val (1-z-(α+α)) := by
    change (D₀ (R p)).val z = _
    rw [hD _ z hz, cechPhaseReflection_apply]
    change p.1.val z - sLocalExplicitTateFactor F S ω ε (z+δ) * p.2.val (1-z-(α+α)) = _
    rw [show z+δ = z+α-d by dsimp [δ]; ring]
  refine ⟨d,hd,ε,U,A,D,B,hε,hε₀,hphase,hU,hA,hB,hClosed₁,hClosed₂,hExact₁,hExact₂,hDiff,?_,?_⟩
  · intro p z hz
    rw [map_sub, hB p]
    have hR : (N (sLocalCechProfileRestrict p.1)).val z = (M p).1.val z := by
      change (overlapPhaseMellin α hα (sLocalCechProfileRestrict p.1)).val z = _
      rw [overlapPhaseMellin_restrict]
      exact (ite_eq_left hz).trans (one_mul _)
    change (N (sLocalCechProfileRestrict p.1)).val z - (D (M p)).val z = _
    rw [hR, hDiff (M p) z hz, sub_sub_cancel]
    rfl
  · exact recoveredSectionProfiles F S ν ω τ hmod α d hα hd hphase

omit [∀ v : S, MeasurableSpace (V F S v)ˣ] [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
/-- Section evaluation identifies a weighted isotype with the actual
homogeneous theta function as soon as their section profiles agree. -/
theorem sLocalCechIsotype_eq_theta_of_section (ω : PontryaginDual (K F S))
    {I : Set ℝ}
    (τ : Multiplicative ℝ →* SIdeleQuotient F S)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (f : E F S) (u : sLocalCechDecayIsotype F S ω I)
    (hu : ∀ t : ℝ, u.val.val (τ (Multiplicative.ofAdd t)) =
      sLocalHomogeneousTheta F S ν ω f.val (τ (Multiplicative.ofAdd t)))
    (q : SIdeleQuotient F S) :
    u.val.val q = sLocalHomogeneousTheta F S ν ω f.val q := by
  let m := sLocalCechModulation F S
  let t := m q
  have hm : m (τ t) = t := by
    exact congrArg Multiplicative.ofAdd ((congrArg Real.log (hmod t.toAdd)).trans (Real.log_exp _))
  let k : m.toMonoidHom.ker := ⟨q / τ t, by
    change m (q / τ t) = 1
    rw [map_div, hm]
    exact div_self' t⟩
  have he : k.val⁻¹ * q = τ t := by
    calc
      _ = (τ t / q) * q :=
        congrArg (fun a : SIdeleQuotient F S ↦ a * q) (inv_div q (τ t))
      _ = _ := div_mul_cancel (τ t) q
  have hq : q = (cechNormOne F S k).val * τ t := (div_mul_cancel _ _).symm
  have hc : sLocalHomogeneousTheta F S ν ω f.val (τ t) =
      (ω (cechNormOne F S k) : ℂ) * u.val.val q :=
    (hu t.toAdd).symm.trans ((congrArg u.val.val he).symm.trans (u.property k q))
  have htheta :
      sLocalHomogeneousTheta F S ν ω f.val q =
        ((ω (cechNormOne F S k) : ℂ)⁻¹) * sLocalHomogeneousTheta F S ν ω f.val (τ t) := by
    conv_lhs => rw [hq]
    exact sLocalHomogeneousTheta_translate F S ν ω f.val (cechNormOne F S k) (τ t)
  rw [htheta, hc, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]

set_option maxHeartbeats 9000000 in
include hν in
/-- The corrected S-local Čech sequences on the actual weighted
Schwartz–Bruhat isotypes and their Mellin transforms. Both rows are exact
on the left and in the middle, with closed left embeddings. -/
theorem exists_sLocalCech_for_section (ω : PontryaginDual (K F S))
    (τ : Multiplicative ℝ →* SIdeleQuotient F S) (hτ : Continuous τ)
    (hmod : ∀ t : ℝ, sLocalClassModulus F S (τ (Multiplicative.ofAdd t)) = Real.exp t)
    (α : ℂ) (hα : α.re = 0) :
    ∃ (d : ℂ) (hd : d.re = 0) (ε : ℂ → ℂ)
      (U : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ] (RightBergman × RightBergman))
      (A : SLocalHomogeneousThetaQuotient F S ν ω →L[ℂ]
        (GlobalProfile F S ω × GlobalProfile F S ω⁻¹))
      (D : (RightBergman × RightBergman) →L[ℂ] OverlapBergman)
      (B : (GlobalProfile F S ω × GlobalProfile F S ω⁻¹) →L[ℂ] OverlapProfile)
      (M : (GlobalProfile F S ω × GlobalProfile F S ω⁻¹) ≃L[ℂ] (RightBergman × RightBergman))
      (P : GlobalProfile F S ω →L[ℂ] OverlapProfile),
      let N := overlapPhaseMellin α hα
      AnalyticOnNhd ℂ ε univ ∧ (∀ z, ε z ≠ 0) ∧
      (∀ z (t : ℝ) (k : K F S),
        sLocalZetaWeight F S ω (z-d) (τ (Multiplicative.ofAdd t) * k.val) =
          Complex.exp (z * (t : ℂ)) * (ω k : ℂ)) ∧
      (∀ q, cechPhaseReflection α hα (U q) =
        sLocalPairedBergmanMellin_shift F S ν ω (α-d) (by simp [hα,hd]) q) ∧
      (∀ q, M (A q) = U q) ∧ (∀ p, N (B p) = D (M p)) ∧
      IsClosedEmbedding U ∧ IsClosedEmbedding A ∧
      Function.Exact U D ∧ Function.Exact A B ∧
      (∀ p (z : ℂ), (0 : ℝ) < z.re →
        (M p).1.val z = mellin (fun t ↦ sLocalCechIsotypeEval F S ω p.1
          (τ (Multiplicative.ofAdd (Real.log t)))) (z+α) ∧
        (M p).2.val z = mellin (fun t ↦ sLocalCechIsotypeEval F S ω⁻¹ p.2
          (τ (Multiplicative.ofAdd (Real.log t)))) (z+α)) ∧
      (∀ p z, z.re ∈ Overlap →
        (D p).val z =
          p.1.val z - sLocalExplicitTateFactor F S ω ε (z+α-d) * p.2.val (1-z-(α+α))) ∧
      (∀ p t, (P p).val t = sLocalCechIsotypeEval F S ω p (τ (Multiplicative.ofAdd t))) ∧
      (∀ p z, z.re ∈ Overlap →
        (N (P p.1 - B p)).val z =
          sLocalExplicitTateFactor F S ω ε (z+α-d) * (M p).2.val (1-z-(α+α))) ∧
      (∀ (f : E F S) g,
        sLocalCechIsotypeEval F S ω (A (Submodule.Quotient.mk f)).1 g =
          sLocalHomogeneousTheta F S ν ω f.val g ∧
        sLocalCechIsotypeEval F S ω⁻¹ (A (Submodule.Quotient.mk f)).2 g =
          sLocalHomogeneousTheta F S ν ω⁻¹ (sLocalSelectedFourier F S f).val g) := by
  obtain ⟨d,hd,ε,U,A₀,D,B₀,hε,hε₀,hphase,hU,hA,hB,hClosedU,hClosedA,hExactU,hExactA,hD,hTopD,hTheta⟩ :=
    exists_sLocalCech_radialDiagram F S μ ν hν ω τ hτ hmod α hα
  obtain ⟨e₁,he₁⟩ := exists_sLocalCechRadialIsotype F S ω RightStrip nonempty_Ioi τ hτ hmod
  obtain ⟨e₂,he₂⟩ := exists_sLocalCechRadialIsotype F S ω⁻¹ RightStrip nonempty_Ioi τ hτ hmod
  let e := e₁.prodCongr e₂
  let M₀ := (rightPhaseMellin α hα).prodCongr (rightPhaseMellin α hα)
  let M := e.symm.trans M₀
  let A := e.toContinuousLinearMap.comp A₀
  let B := B₀.comp e.symm.toContinuousLinearMap
  let N := overlapPhaseMellin α hα
  let P := N.symm.toContinuousLinearMap.comp (overlapRestrict.comp
    ((rightPhaseMellin α hα).toContinuousLinearMap.comp e₁.symm.toContinuousLinearMap))
  have hP (u : GlobalProfile F S ω) :
      P u = sLocalCechProfileRestrict (e₁.symm u) := by
    apply N.injective
    exact (N.apply_symm_apply (overlapRestrict (rightPhaseMellin α hα (e₁.symm u)))).trans
      (overlapPhaseMellin_restrict α hα (e₁.symm u)).symm
  have he (q) : e.symm (A q) = A₀ q := e.symm_apply_apply (A₀ q)
  refine ⟨d,hd,ε,U,A,D,B,M,P,hε,hε₀,hphase,hU,?_,?_,hClosedU,?_,hExactU,?_,?_,hD,?_,?_,?_⟩
  · intro q
    exact (congrArg M₀ (he q)).trans (hA q)
  · intro p
    exact hB (e.symm p)
  · exact e.toHomeomorph.isClosedEmbedding.comp hClosedA
  · intro p
    change B₀ (e.symm p) = 0 ↔ p ∈ range A
    rw [hExactA (e.symm p)]
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q,(congrArg e hq).trans (e.apply_symm_apply p)⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q,(he q).symm⟩
  · intro p z hz
    have e₁' : (e₁.symm p.1).val ∘ Real.log =
        (fun t ↦ sLocalCechIsotypeEval F S ω p.1 (τ (Multiplicative.ofAdd (Real.log t)))) :=
      funext fun t ↦ he₁ p.1 (Real.log t)
    have e₂' : (e₂.symm p.2).val ∘ Real.log =
        (fun t ↦ sLocalCechIsotypeEval F S ω⁻¹ p.2 (τ (Multiplicative.ofAdd (Real.log t)))) :=
      funext fun t ↦ he₂ p.2 (Real.log t)
    exact ⟨(cechPhaseMellin_apply _ _ _ α hα (e₁.symm p.1) z hz).trans
      (congrArg (fun u ↦ mellin u (z+α)) e₁'),
      (cechPhaseMellin_apply _ _ _ α hα (e₂.symm p.2) z hz).trans
      (congrArg (fun u ↦ mellin u (z+α)) e₂')⟩
  · intro p t
    exact (congrArg (fun u : OverlapProfile ↦ u.val t) (hP p)).trans (he₁ p t)
  · intro p z hz
    exact (congrArg (fun u : OverlapProfile ↦ (N (u-B p)).val z) (hP p.1)).trans
      (hTopD (e.symm p) z hz)
  · intro f g
    constructor
    · apply sLocalCechIsotype_eq_theta_of_section F S ν ω τ hmod f _ _ g
      intro t
      exact (he₁ _ t).symm.trans ((congrArg (fun p : RightProfile × RightProfile ↦ p.1.val t)
        (he (Submodule.Quotient.mk f))).trans (hTheta f t).1)
    · apply sLocalCechIsotype_eq_theta_of_section F S ν ω⁻¹ τ hmod (sLocalSelectedFourier F S f) _ _ g
      intro t
      exact (he₂ _ t).symm.trans ((congrArg (fun p : RightProfile × RightProfile ↦ p.2.val t)
        (he (Submodule.Quotient.mk f))).trans (hTheta f t).2)


omit [∀ v : S, BorelSpace (V F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)] [BorelSpace (InfiniteAdeleRing F)] in
/-- The Tate-weighted reflection in the printed theorem fails to give a
left-half-plane Bergman function, even on the Gaussian. -/
theorem exists_sLocalCech_globalReflection_obstruction (ω : PontryaginDual (K F S))
    (ε : ℂ → ℂ) (hε : ∀ z, AnalyticAt ℂ ε z) (hε₀ : ∀ z, ε z ≠ 0) :
    ∃ g : RightBergman, ¬ ∃ H : LeftBergman,
      ∀ z : ℂ, z.re < 1 → H.val z = sLocalExplicitTateFactor F S ω ε z * g.val (1-z) := by
  let g : RightBergman := ⟨(Complex.re ⁻¹' RightStrip).indicator (fun z ↦ Complex.exp (z^2)),
    gaussian_mem_schwartzBergmanSubmodule RightStrip isOpen_Ioi⟩
  refine ⟨g, ?_⟩
  obtain ⟨c,hc,hpole⟩ : ∃ c : ℂ, c.re < 1 ∧ sLocalEulerPoleLattices F S ω c := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rcases v.isReal_or_isComplex with hv | hv
    · let v' : {w : InfinitePlace F // w.IsReal} := ⟨v,hv⟩
      let p := sLocalRealArchParameters F S ω v'
      refine ⟨-p.1 - (p.2 % 2 : ℕ) - 2 * (0 : ℂ), ?_, Or.inl ⟨v',0,by simp [p]⟩⟩
      have hp : p.1.re = 0 := sLocalRealArchParameters_re F S ω v'
      simp only [mul_zero, sub_zero, Complex.sub_re, Complex.neg_re, Complex.natCast_re, hp, neg_zero]
      linarith [Nat.cast_nonneg (α := ℝ) (p.2 % 2)]
    · let v' : {w : InfinitePlace F // w.IsComplex} := ⟨v,hv⟩
      let p := sLocalComplexArchParameters F S ω v'
      refine ⟨-p.1 - (p.2.natAbs : ℂ) / 2 - (0 : ℂ), ?_, Or.inr (Or.inl ⟨v',0,by simp [p]⟩)⟩
      have hp : p.1.re = 0 := sLocalComplexArchParameters_re F S ω v'
      simp only [sub_zero, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re, Complex.natCast_re,
        hp, neg_zero]
      linarith [Nat.cast_nonneg (α := ℝ) p.2.natAbs]
  let ρ := sLocalExplicitTateFactor F S ω ε
  let G := bergmanReflectOne g
  have hA (H : LeftBergman) : AnalyticAt ℂ H.val c :=
    H.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re) c hc
  have hGc : G.val c ≠ 0 := by
    change ((Complex.re ⁻¹' RightStrip).indicator (fun z ↦ Complex.exp (z^2))) (1-c) ≠ 0
    have hm : (1-c) ∈ Complex.re ⁻¹' RightStrip := by
      change 0 < (1-c).re
      simpa [Complex.sub_re, sub_pos] using hc
    rw [indicator_of_mem hm]
    exact Complex.exp_ne_zero _
  have hord : meromorphicOrderAt ρ c < 0 :=
    (sLocalExplicitTateFactor_poles F S ω ε hε hε₀ c).mpr hpole
  have hm : MeromorphicAt ρ c := sLocalExplicitTateFactor_meromorphic F S ω ε hε c
  rintro ⟨H,hH⟩
  have he : H.val =ᶠ[𝓝[≠] c] ρ * G.val := by
    apply Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [(isOpen_Iio.preimage Complex.continuous_re).mem_nhds hc] with z hz
    exact hH z hz
  have hlt : meromorphicOrderAt H.val c < 0 := by
    rw [meromorphicOrderAt_congr he, meromorphicOrderAt_mul hm (hA G).meromorphicAt,
      (hA G).meromorphicOrderAt_eq, (hA G).analyticOrderAt_eq_zero.mpr hGc]
    simpa using hord
  exact (not_lt_of_ge (hA H).meromorphicOrderAt_nonneg) hlt

end ActualSequence

end

end Masullo
