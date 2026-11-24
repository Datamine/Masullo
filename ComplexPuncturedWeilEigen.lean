import ComplexWeilRadialProjection
import RealPuncturedWeilEigen
import Mathlib.MeasureTheory.Measure.Haar.Basic

open Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped Classical SchwartzMap

namespace Masullo

noncomputable section

private abbrev CT := 𝓢(ℂ, ℂ)
private abbrev RT := 𝓢(ℝ, ℂ)

attribute [local instance] complexZeta_circleMeasurable complexZeta_circleBorel

private abbrev D (v : ℝˣ) := archSchwartzDilation v

private theorem dilation_comp (u v : ℝˣ) (f : RT) : D u (D v f) = D (u * v) f := by
  ext x
  simp [D, mul_assoc, mul_comm (u : ℝ)⁻¹]

private theorem dilation_negOne (f : RT) (x : ℝ) : D (-1) f x = f (-x) := by
  simp [D]

private def radialRestriction (T : StrongDual ℂ CT) (m : ℤ) (a : ℕ) : StrongDual ℂ RT :=
  (T.comp (complexWeilRadialLift m)) +
    (-1 : ℂ) ^ a • (T.comp ((complexWeilRadialLift m).comp (D (-1))))

private theorem radialRestriction_apply (T : StrongDual ℂ CT) (m : ℤ) (a : ℕ) (f : RT) :
    radialRestriction T m a f =
      T (complexWeilRadialLift m f) + (-1 : ℂ) ^ a * T (complexWeilRadialLift m (D (-1) f)) := rfl

private theorem radialRestriction_covariance (T : StrongDual ℂ CT) (m : ℤ) (z : ℂ)
    (hT : ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f)
    (a : ℕ) (v : ℝˣ) (f : RT) :
    radialRestriction T m a (D v f) =
      realArchUnitWeight a (z + (m.natAbs : ℂ) / 2) v * radialRestriction T m a f := by
  let q := z + (m.natAbs : ℂ) / 2
  have hpos (u : ℝˣ) (hu : 0 < (u : ℝ)) (g : RT) :
      radialRestriction T m a (D u g) =
        realArchUnitWeight a q u * radialRestriction T m a g := by
    have hcomm : D (-1) (D u g) = D u (D (-1) g) := by
      rw [dilation_comp, dilation_comp, mul_comm]
    rw [radialRestriction_apply, hcomm, complexWeilEigen_radialLift_positive T m z hT u hu,
      complexWeilEigen_radialLift_positive T m z hT u hu, radialRestriction_apply,
      realArchUnitWeight, abs_of_pos hu, ite_eq_right hu.not_gt, mul_one]
    dsimp only [q]
    ring
  rcases lt_or_gt_of_ne v.ne_zero with hv | hv
  · have hnv : 0 < ((-v : ℝˣ) : ℝ) := by simpa using neg_pos.mpr hv
    have hcomp : D (-1) (D (-1) f) = f := by
      ext x
      rw [dilation_negOne, dilation_negOne, neg_neg]
    have hsign : radialRestriction T m a (D (-1) f) =
        realArchUnitWeight a q (-1) * radialRestriction T m a f := by
      have hs : realArchUnitWeight a q (-1) = (-1 : ℂ) ^ a := by
        norm_num [realArchUnitWeight]
      rw [radialRestriction_apply, hcomp, hs, radialRestriction_apply, mul_add, ← mul_assoc,
        ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, add_comm]
    calc
      _ = radialRestriction T m a (D (-v) (D (-1) f)) := by
        rw [dilation_comp, show (-v) * (-1 : ℝˣ) = v by simp]
      _ = _ := by
        rw [hpos (-v) hnv, hsign, ← mul_assoc, ← realArchUnitWeight_mul,
          show (-v) * (-1 : ℝˣ) = v by simp]
  · exact hpos v hv f

private theorem radialRestriction_apply_of_positiveSupport
    (T : StrongDual ℂ CT) (m : ℤ) (a : ℕ) (f : RT) (hf : tsupport f ⊆ Ioi 0) :
    radialRestriction T m a f = T (complexWeilRadialLift m f) := by
  have hzero : complexWeilRadialLift m (D (-1) f) = 0 := by
    ext x
    have hx : -Complex.normSq x ∉ tsupport f := fun hx =>
      (not_lt_of_ge (neg_nonpos.mpr (Complex.normSq_nonneg x))) (hf hx)
    rw [complexWeilRadialLift_apply, dilation_negOne, image_eq_zero_of_notMem_tsupport hx, mul_zero]
    rfl
  rw [radialRestriction_apply, hzero, map_zero, mul_zero, add_zero]

private theorem supported_of_radialRestriction_vanishes (T : StrongDual ℂ CT)
    (m : ℤ) (z : ℂ) (hT : ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f)
    (hvan : ∀ f : RT, HasCompactSupport f → tsupport f ⊆ Ioi 0 → T (complexWeilRadialLift m f) = 0) :
    Distribution.dsupport (⇑T) ⊆ {0} := by
  let μ := Measure.haarMeasure (⊤ : PositiveCompacts Circle)
  haveI : IsProbabilityMeasure μ := ⟨by
    simpa only [PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts Circle)))⟩
  have hv : Distribution.IsVanishingOn (⇑T) ({0} : Set ℂ)ᶜ := by
    intro f hf
    obtain ⟨g, hg, hlim⟩ := exists_schwartz_compactSupport_sequence_subset f
    have hz (n : ℕ) : T (g n) = 0 := by
      have h0 : (0 : ℂ) ∉ tsupport (g n) := fun h =>
        ((hg n).2.trans hf h) (mem_singleton 0)
      obtain ⟨r, hrc, hrp, hr⟩ := exists_complexSchwartz_radialAngularAverage μ m (g n) (hg n).1 h0
      rw [← complexWeilEigen_eq_angularAverage μ T m z hT (g n) _ hr]
      exact hvan r hrc hrp
    have ht : Tendsto (fun n => T (g n)) atTop (𝓝 (T f)) :=
      T.continuous.continuousAt.tendsto.comp hlim
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n => (hz n).symm))
  exact Set.subset_compl_iff_disjoint_left.mpr
    (hv.disjoint_dsupport isClosed_singleton.isOpen_compl) |>.trans (by simp)

private theorem jet_shifted_weight (a b : ℕ) :
    -((a + b : ℕ) : ℂ) / 2 + (((b : ℤ) - a).natAbs : ℂ) / 2 = -((min a b : ℕ) : ℂ) := by
  have h : ((b : ℤ) - a).natAbs + 2 * min a b = a + b := by omega
  have hc := congrArg (fun n : ℕ => (n : ℂ)) h
  push_cast at hc ⊢
  linear_combination hc / 2

/-- All complex local eigendistributions lie on the normalized line. At every
exceptional parameter the radial restriction off the origin vanishes. -/
theorem complexWeilEigen_eq_normalized (T : StrongDual ℂ CT) (m : ℤ) (z : ℂ)
    (hT : ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f) :
    ∃ c : ℂ, T = c • complexWeilNormalizedFamily m z := by
  let q := z + (m.natAbs : ℂ) / 2
  let N := complexWeilNormalizedFamily m z
  have hN : ∀ u f, N (archSchwartzDilation u f) = complexArchUnitWeight m z u * N f :=
    fun u f => complexWeilNormalizedFamily_dilate m u f z
  have hNne : N ≠ 0 := by
    intro h
    have h1 := (complexGammaNormalized_distribution m).choose_spec.choose_spec.2.2.1 z
    change N (complexGammaNormalized_distribution m).choose = 1 at h1
    rw [h, zero_apply] at h1
    exact zero_ne_one h1
  by_cases hq : ∃ n : ℕ, q = -(n : ℂ)
  · obtain ⟨n, hn⟩ := hq
    obtain ⟨c, hc⟩ := realWeilEigen_eq_normalized (radialRestriction T m n) n q
      (radialRestriction_covariance T m z hT n)
    have hs : Distribution.dsupport (⇑T) ⊆ {0} := by
      apply supported_of_radialRestriction_vanishes T m z hT
      intro f _ hf
      rw [← radialRestriction_apply_of_positiveSupport T m n f hf, hc, hn]
      obtain ⟨_, hj⟩ := realWeilNormalizedFamily_eq_jet n n (by exact ⟨n, rfl⟩)
      rw [hj]
      have h0 : (0 : ℝ) ∉ tsupport f := fun h => lt_irrefl (0 : ℝ) (hf h)
      have hzero : (f : ℝ → ℂ) =ᶠ[𝓝 0] 0 := notMem_tsupport_iff_eventuallyEq.mp h0
      change c * (_ * realSchwartzJet n f) = 0
      have hj0 : realSchwartzJet n f = 0 := by
        rw [realSchwartzJet_apply, hzero.iteratedDeriv_eq]
        simp
      rw [hj0, mul_zero, mul_zero]
    by_cases h0 : T = 0
    · refine ⟨(0 : ℂ), ?_⟩
      ext f
      rw [h0]
      change (0 : ℂ) = 0 * complexWeilNormalizedFamily m z f
      rw [zero_mul]
    obtain ⟨d, _, hd⟩ := complexSupportedWeilEigen_eq_normalized T hs h0 m z hT
    exact ⟨d, hd⟩
  · have hzero (U : StrongDual ℂ CT) (hU : ∀ u f,
        U (archSchwartzDilation u f) = complexArchUnitWeight m z u * U f)
        (hs : Distribution.dsupport (⇑U) ⊆ {0}) : U = 0 := by
      by_contra h0
      obtain ⟨a, b, c, hc, hz, hm, hUj⟩ := complexSupportedWeilEigen_eq_jet U hs h0 m z hU
      exact hq ⟨min a b, by dsimp [q]; rw [hz, hm, jet_shifted_weight]⟩
    obtain ⟨c, hc⟩ := realWeilEigen_eq_normalized (radialRestriction T m 0) 0 q
      (radialRestriction_covariance T m z hT 0)
    obtain ⟨d, hd⟩ := realWeilEigen_eq_normalized (radialRestriction N m 0) 0 q
      (radialRestriction_covariance N m z hN 0)
    have he (f : RT) (hf : tsupport f ⊆ Ioi 0) :
        T (complexWeilRadialLift m f) = c * realWeilNormalizedFamily 0 q f ∧
        N (complexWeilRadialLift m f) = d * realWeilNormalizedFamily 0 q f := by
      rw [← radialRestriction_apply_of_positiveSupport T m 0 f hf, hc,
        ← radialRestriction_apply_of_positiveSupport N m 0 f hf, hd]
      exact ⟨rfl, rfl⟩
    have hdne : d ≠ 0 := by
      intro hd0
      apply hNne
      apply hzero N hN
      apply supported_of_radialRestriction_vanishes N m z hN
      intro f _ hf
      rw [(he f hf).2, hd0, zero_mul]
    let U := T - (c / d) • N
    have hU : ∀ u f, U (archSchwartzDilation u f) = complexArchUnitWeight m z u * U f := by
      intro u f
      change T (archSchwartzDilation u f) - c / d * N (archSchwartzDilation u f) = _
      rw [hT, hN]
      change _ = complexArchUnitWeight m z u * (T f - c / d * N f)
      ring
    refine ⟨c / d, sub_eq_zero.mp (hzero U hU (supported_of_radialRestriction_vanishes U m z hU ?_))⟩
    intro f _ hf
    change T (complexWeilRadialLift m f) - c / d * N (complexWeilRadialLift m f) = 0
    rw [(he f hf).1, (he f hf).2, ← mul_assoc, div_mul_cancel₀ c hdne, sub_self]

/-- The complex local zeta eigenspace at an angular character and a spectral parameter. -/
def complexWeilEigenspace (m : ℤ) (z : ℂ) : Submodule ℂ (StrongDual ℂ CT) where
  carrier := {T | ∀ u f, T (archSchwartzDilation u f) = complexArchUnitWeight m z u * T f}
  zero_mem' := by intro u f; simp
  add_mem' {T U} hT hU := by
    intro u f
    change T (archSchwartzDilation u f) + U (archSchwartzDilation u f) =
      complexArchUnitWeight m z u * (T f + U f)
    rw [hT u f, hU u f, mul_add]
  smul_mem' c T hT := by
    intro u f
    change c * T (archSchwartzDilation u f) = complexArchUnitWeight m z u * (c * T f)
    rw [hT u f, mul_left_comm]

/-- Evaluation on the Gaussian reference is a linear coordinate at every
complex local parameter, including the exceptional jets. -/
def complexWeilEigenspace_equiv (m : ℤ) (z : ℂ) : complexWeilEigenspace m z ≃ₗ[ℂ] ℂ := by
  let f₀ := (complexGammaNormalized_distribution m).choose
  let N : complexWeilEigenspace m z :=
    ⟨complexWeilNormalizedFamily m z, fun u f => complexWeilNormalizedFamily_dilate m u f z⟩
  have hN : N.val f₀ = 1 :=
    (complexGammaNormalized_distribution m).choose_spec.choose_spec.2.2.1 z
  refine
    { toFun := fun T => T.val f₀
      invFun := fun c => c • N
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := ?_
      right_inv := ?_ }
  · intro T
    obtain ⟨c, hc⟩ := complexWeilEigen_eq_normalized T.val m z T.property
    apply Subtype.ext
    change T.val f₀ • N.val = T.val
    have he : T.val f₀ = c := by
      rw [hc]
      change c * N.val f₀ = c
      rw [hN, mul_one]
    rw [he]
    exact hc.symm
  · intro c
    change c * N.val f₀ = c
    rw [hN, mul_one]

theorem complexWeilEigenspace_finrank (m : ℤ) (z : ℂ) :
    Module.finrank ℂ (complexWeilEigenspace m z) = 1 :=
  (complexWeilEigenspace_equiv m z).finrank_eq.trans (Module.finrank_self ℂ)

end
end Masullo
