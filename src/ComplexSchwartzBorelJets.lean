import ComplexPointTemperedExpansion
import RealSchwartzBorelJets
import Mathlib.Data.Nat.Pairing
import Mathlib.RingTheory.MvPowerSeries.PiTopology

open Filter Function Set Topology
open scoped ContDiff SchwartzMap MvPowerSeries.WithPiTopology

namespace Masullo

noncomputable section

private abbrev S := 𝓢(ℂ, ℂ)

private theorem covariant_Z (r : ℝ) (hr : 0 < r) (f : S) :
    complexWirtingerZ (schwartzPositiveDilate r hr f) =
      (r : ℂ) • schwartzPositiveDilate r hr (complexWirtingerZ f) := by
  ext z
  rw [complexWirtingerZ_apply]
  change (1/2 : ℂ) * (fderiv ℝ (fun y ↦ f.toFun (r • y)) z 1 -
    Complex.I * fderiv ℝ (fun y ↦ f.toFun (r • y)) z Complex.I) =
      (r : ℂ) * complexWirtingerZ f (r • z)
  rw [fderiv_comp_smul, complexWirtingerZ_apply]
  rw [show (⇑f : ℂ → ℂ) = f.toFun from rfl]
  simp only [smul_apply, Complex.real_smul]
  ring

private theorem covariant_Bar (r : ℝ) (hr : 0 < r) (f : S) :
    complexWirtingerBar (schwartzPositiveDilate r hr f) =
      (r : ℂ) • schwartzPositiveDilate r hr (complexWirtingerBar f) := by
  ext z
  rw [complexWirtingerBar_apply]
  change (1/2 : ℂ) * (fderiv ℝ (fun y ↦ f.toFun (r • y)) z 1 +
    Complex.I * fderiv ℝ (fun y ↦ f.toFun (r • y)) z Complex.I) =
      (r : ℂ) * complexWirtingerBar f (r • z)
  rw [fderiv_comp_smul, complexWirtingerBar_apply]
  rw [show (⇑f : ℂ → ℂ) = f.toFun from rfl]
  simp only [smul_apply, Complex.real_smul]
  ring

private theorem covariant_pow (r : ℝ) (hr : 0 < r) (P : S →L[ℂ] S)
    (hP : ∀ f, P (schwartzPositiveDilate r hr f) = (r : ℂ) • schwartzPositiveDilate r hr (P f))
    (n : ℕ) (f : S) :
    (P ^ n) (schwartzPositiveDilate r hr f) =
      (r : ℂ) ^ n • schwartzPositiveDilate r hr ((P ^ n) f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change P ((P ^ n) (schwartzPositiveDilate r hr f)) =
      (r : ℂ) ^ (n+1) • schwartzPositiveDilate r hr (P ((P ^ n) f))
    rw [ih, map_smul, hP, smul_smul, pow_succ]

private theorem complexSchwartzPointJet_dilate (r : ℝ) (hr : 0 < r) (f : S) (a b : ℕ) :
    complexSchwartzPointJet a b (schwartzPositiveDilate r hr f) =
      (r : ℂ) ^ (a+b) * complexSchwartzPointJet a b f := by
  let g := (complexWirtingerZ ^ a) ((complexWirtingerBar ^ b) f)
  change ((complexWirtingerZ ^ a) ((complexWirtingerBar ^ b) (schwartzPositiveDilate r hr f))) 0 =
    (r : ℂ) ^ (a+b) * g 0
  rw [covariant_pow r hr complexWirtingerBar (covariant_Bar r hr), map_smul,
    covariant_pow r hr complexWirtingerZ (covariant_Z r hr), smul_smul]
  change ((r : ℂ)^b * (r : ℂ)^a) * g (r • (0 : ℂ)) = _
  rw [smul_zero, pow_add, mul_comm ((r : ℂ)^b)]

private def degree (n : ℕ) : ℕ := (Nat.unpair n).1 + (Nat.unpair n).2

private theorem degree_tendsto_atTop : Tendsto degree atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  let s := complexPointJetIndices N
  let m := (s.image fun p ↦ Nat.pair p.1 p.2).sup id
  filter_upwards [eventually_gt_atTop m] with n hn
  by_contra h
  have hp : Nat.unpair n ∈ s := (mem_complexPointJetIndices N _).mpr (by
    change ¬ N ≤ (Nat.unpair n).1 + (Nat.unpair n).2 at h
    omega)
  have hmem : n ∈ s.image (fun p ↦ Nat.pair p.1 p.2) :=
    Finset.mem_image.mpr ⟨Nat.unpair n, hp, Nat.pair_unpair n⟩
  exact (not_le_of_gt hn) (Finset.le_sup (f := id) hmem)

/-- Arbitrary mixed Wirtinger data at zero are the jets of one complex
Schwartz function. -/
theorem exists_complexSchwartz_with_pointJets (a : ℕ × ℕ → ℂ) :
    ∃ f : S, ∀ p : ℕ × ℕ, complexSchwartzPointJet p.1 p.2 f = a p := by
  let J (n : ℕ) := complexSchwartzPointJet (Nat.unpair n).1 (Nat.unpair n).2
  have hSingle (n : ℕ) : ∃ f : S, ∀ j, J j f = if j = n then 1 else 0 := by
    obtain ⟨f, hf⟩ := exists_complexSchwartz_single_pointJet (Nat.unpair n).1 (Nat.unpair n).2
    refine ⟨f, fun j ↦ ?_⟩
    change complexSchwartzPointJet (Nat.unpair j).1 (Nat.unpair j).2 f = _
    rw [hf]
    have he : (Nat.unpair j).1 = (Nat.unpair n).1 ∧
      (Nat.unpair j).2 = (Nat.unpair n).2 ↔ j = n := by
      constructor
      · intro h
        have hh := congrArg (fun p : ℕ × ℕ ↦ Nat.pair p.1 p.2) (Prod.ext h.1 h.2)
        simpa [Nat.pair_unpair] using hh
      · rintro rfl
        exact ⟨rfl, rfl⟩
    simp only [he]
  obtain ⟨f, hf⟩ := exists_schwartz_interpolating_graded_jets J degree degree_tendsto_atTop
    hSingle (fun r hr f j ↦ complexSchwartzPointJet_dilate r hr f (Nat.unpair j).1 (Nat.unpair j).2)
    (fun n ↦ a (Nat.unpair n))
  refine ⟨f, fun ⟨i,j⟩ ↦ ?_⟩
  simpa only [J, Nat.unpair_pair] using hf (Nat.pair i j)

/-- The mixed Taylor map, in factorial-normalized monomial coordinates. -/
def complexSchwartzTaylor : S →L[ℂ] ((ℕ × ℕ) → ℂ) :=
  ContinuousLinearMap.pi fun p ↦
    (((p.1.factorial : ℂ) * (p.2.factorial : ℂ))⁻¹) • complexSchwartzPointJet p.1 p.2

theorem complexSchwartzTaylor_surjective : Surjective complexSchwartzTaylor := by
  intro a
  obtain ⟨f, hf⟩ := exists_complexSchwartz_with_pointJets
    (fun p ↦ ((p.1.factorial : ℂ) * (p.2.factorial : ℂ)) * a p)
  refine ⟨f, funext fun p ↦ ?_⟩
  change ((p.1.factorial : ℂ) * (p.2.factorial : ℂ))⁻¹ *
    complexSchwartzPointJet p.1 p.2 f = a p
  have h : (p.1.factorial : ℂ) * (p.2.factorial : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero p.1) (by exact_mod_cast Nat.factorial_ne_zero p.2)
  rw [hf, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- The complex Taylor quotient has the product topology of the mixed
coefficients. -/
def complexSchwartzTaylorQuotient :
    (S ⧸ complexSchwartzTaylor.ker) ≃L[ℂ] ((ℕ × ℕ) → ℂ) := by
  let M := complexSchwartzTaylor.ker
  let p := M.liftQL complexSchwartzTaylor le_rfl
  have hp : Bijective p := by
    constructor
    · apply (LinearMap.ker_eq_bot.mp _ : Injective p.toLinearMap)
      exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
    · intro a
      obtain ⟨x, rfl⟩ := complexSchwartzTaylor_surjective a
      exact ⟨M.mkQ x, rfl⟩
  letI : @CompleteSpace S (IsTopologicalAddGroup.rightUniformSpace S) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact completeSpace_schwartzMap
  have hOpen := isOpenMap_of_surjective_complete_baire complexSchwartzTaylor complexSchwartzTaylor_surjective
  have hOpenQ : IsOpenMap p := IsOpenMap.of_comp M.continuous_mkQ M.mkQ_surjective hOpen
  let e := LinearEquiv.ofBijective p.toLinearMap hp
  exact ⟨e, p.continuous, (e.toEquiv.toHomeomorphOfContinuousOpen p.continuous hOpenQ).continuous_invFun⟩

/-- Identify the exponents of a monomial in two variables with its two
ordered degrees. -/
def complexTaylorMultiIndex : (Fin 2 →₀ ℕ) ≃ ℕ × ℕ :=
  Finsupp.equivFunOnFinite.trans (finTwoArrowEquiv ℕ)

private def coefficientSeriesEquiv : ((ℕ × ℕ) → ℂ) ≃L[ℂ] MvPowerSeries (Fin 2) ℂ where
  toFun a := fun s ↦ a (complexTaylorMultiIndex s)
  invFun f p := MvPowerSeries.coeff (complexTaylorMultiIndex.symm p) f
  left_inv a := funext fun p ↦ congrArg a (complexTaylorMultiIndex.apply_symm_apply p)
  right_inv f := MvPowerSeries.ext fun s ↦ by
    change MvPowerSeries.coeff (complexTaylorMultiIndex.symm (complexTaylorMultiIndex s)) f = _
    rw [Equiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro a
    apply (MvPowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _).mpr
    intro s
    exact (continuous_apply (complexTaylorMultiIndex s)).continuousAt.tendsto
  continuous_invFun := continuous_pi fun p ↦
    MvPowerSeries.WithPiTopology.continuous_coeff ℂ (complexTaylorMultiIndex.symm p)

/-- The complex Schwartz quotient is the space of two-variable formal
power series in its coefficient topology. -/
def complexSchwartzTaylorPowerSeries :
    (S ⧸ complexSchwartzTaylor.ker) ≃L[ℂ] MvPowerSeries (Fin 2) ℂ :=
  complexSchwartzTaylorQuotient.trans coefficientSeriesEquiv

theorem complexSchwartzTaylorPowerSeries_coeff (f : S) (a b : ℕ) :
    MvPowerSeries.coeff (complexTaylorMultiIndex.symm (a,b))
      (complexSchwartzTaylorPowerSeries (complexSchwartzTaylor.ker.mkQ f)) =
      ((a.factorial : ℂ) * (b.factorial : ℂ))⁻¹ * complexSchwartzPointJet a b f := by
  change complexSchwartzTaylor f (complexTaylorMultiIndex (complexTaylorMultiIndex.symm (a,b))) = _
  rw [Equiv.apply_symm_apply]
  rfl

end
end Masullo
