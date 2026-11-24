import LocallyConstantTests
import HeckeEulerProducts
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.SpecificLimits.Normed

open Filter Function Set Topology

namespace Masullo

noncomputable section

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev Q₃ := ℚ_[3]

/-- The principal-value difference for a fixed dilation. -/
def finitePrincipalValue {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (π : Kˣ) : locallyConstantTests K →ₗ[ℂ] locallyConstantTests K :=
  LinearMap.id - locallyConstantTestTranslate K π

theorem finitePrincipalValue_apply {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] (π : Kˣ) (f : locallyConstantTests K) (x : K) :
    (finitePrincipalValue π f).val x = f.val x - f.val ((π.val)⁻¹ * x) := by
  change f.val x - f.val ((↑π⁻¹ : K) * x) = _
  rw [Units.val_inv_eq_inv_val]

section Radial

variable {K : Type*} [NormedField K]

/-- Dilation by any two elements of equal norm agrees on radial tests. -/
theorem finitePrincipalValue_radial_independent (π π' : Kˣ)
    (hπ : ‖π.val‖ = ‖π'.val‖) (f : locallyConstantTests K)
    (hf : ∀ x y, ‖x‖ = ‖y‖ → f.val x = f.val y) :
    finitePrincipalValue π f = finitePrincipalValue π' f := by
  apply Subtype.ext
  funext x
  simp only [finitePrincipalValue_apply, sub_right_inj]
  apply hf
  simp only [norm_mul, norm_inv, hπ]

theorem finitePrincipalValue_eval_zero (π : Kˣ) (f : locallyConstantTests K) :
    (finitePrincipalValue π f).val 0 = 0 := by
  simp [finitePrincipalValue_apply]

theorem finitePrincipalValue_radial (π : Kˣ) (f : locallyConstantTests K)
    (hf : ∀ x y, ‖x‖ = ‖y‖ → f.val x = f.val y) :
    ∀ x y, ‖x‖ = ‖y‖ →
      (finitePrincipalValue π f).val x = (finitePrincipalValue π f).val y := by
  intro x y h
  have h' : ‖π.val⁻¹ * x‖ = ‖π.val⁻¹ * y‖ := by simp only [norm_mul, h]
  rw [finitePrincipalValue_apply, finitePrincipalValue_apply, hf x y h, hf _ _ h']

/-- For a contracting uniformizer, the difference is injective on all tests. -/
theorem finitePrincipalValue_injective (π : Kˣ) (hπ : ‖π.val‖ < 1) :
    Injective (finitePrincipalValue π) := by
  apply LinearMap.ker_eq_bot.mp
  refine LinearMap.ker_eq_bot'.mpr fun f hf => ?_
  have he (x : K) : f.val x = f.val (π.val⁻¹ * x) := by
    apply sub_eq_zero.mp
    have hx := congrArg (fun g : locallyConstantTests K => g.val x) hf
    simpa only [finitePrincipalValue_apply, ZeroMemClass.coe_zero, Pi.zero_apply] using hx
  have heach (x : K) (n : ℕ) : f.val (π.val ^ n * x) = f.val x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', he (π.val * π.val ^ n * x), ← mul_assoc, ← mul_assoc,
        inv_mul_cancel₀ π.ne_zero, one_mul, ih]
  have hconst (x : K) : f.val x = f.val 0 := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ
    have ht : Tendsto (fun n : ℕ => π.val ^ n * x) atTop (𝓝 0) := by
      simpa only [zero_mul] using hpow.mul_const x
    have hlimit : Tendsto (fun n : ℕ => f.val (π.val ^ n * x)) atTop (𝓝 (f.val 0)) :=
      f.property.1.continuous.continuousAt.tendsto.comp ht
    simp only [heach] at hlimit
    exact tendsto_nhds_unique tendsto_const_nhds hlimit
  obtain ⟨R, hR⟩ := f.property.2.isBounded.subset_closedBall (0 : K)
  have hpow : Tendsto (fun n : ℕ => ‖π.val‖⁻¹ ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ (norm_pos_iff.mpr π.ne_zero)).mpr hπ)
  obtain ⟨n, hn⟩ := (hpow.eventually (eventually_gt_atTop R)).exists
  have hz : f.val (π.val⁻¹ ^ n) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hle := hR hm
    rw [Metric.mem_closedBall, dist_zero_right, norm_pow, norm_inv] at hle
    exact hn.not_ge hle
  have h0 : f.val 0 = 0 := (hconst _).symm.trans hz
  apply Subtype.ext
  funext x
  exact (hconst x).trans h0

/-- The source embedding clause holds on all tests for each fixed uniformizer. -/
theorem finitePrincipalValue_isEmbedding (π : Kˣ) (hπ : ‖π.val‖ < 1) :
    letI : TopologicalSpace (locallyConstantTests K) := finestLocallyConvexTopology _
    IsEmbedding (finitePrincipalValue π) := by
  letI : TopologicalSpace (locallyConstantTests K) := finestLocallyConvexTopology _
  letI : PolynormableSpace ℂ (locallyConstantTests K) := (finest_withSeminorms _).toPolynormableSpace
  obtain ⟨L, hL⟩ := (finitePrincipalValue π).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (finitePrincipalValue_injective π hπ))
  have hleft : LeftInverse L (finitePrincipalValue π) := fun f =>
    DFunLike.congr_fun hL f
  exact hleft.isEmbedding (finest_linear_continuous L)
    (finest_linear_continuous (finitePrincipalValue π))

/-- The test function of the unit ball scaled by a power of the parameter. -/
def radialBall (π : Kˣ) (hK : IsCompact (Metric.closedBall (0 : K) 1))
    (hopen : IsOpen (Metric.closedBall (0 : K) 1)) (n : ℤ) : locallyConstantTests K := by
  let e : K ≃ₜ K := Homeomorph.smul (π ^ n)
  have he : Metric.closedBall (0 : K) (‖π.val‖ ^ n) =
      e '' Metric.closedBall (0 : K) 1 := by
    ext x
    change _ ↔ x ∈ e.toEquiv '' _
    rw [Set.mem_image_equiv, Metric.mem_closedBall, Metric.mem_closedBall]
    simp only [dist_zero_right]
    change ‖x‖ ≤ ‖π.val‖ ^ n ↔ ‖(↑((π ^ n)⁻¹) : K) * x‖ ≤ 1
    rw [norm_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, norm_inv, norm_zpow,
      inv_mul_le_iff₀ (zpow_pos (norm_pos_iff.mpr π.ne_zero) _), mul_one]
  exact compactOpenIndicator K
    ⟨_, he.symm ▸ hK.image e.continuous, he.symm ▸ e.isOpenMap _ hopen⟩

theorem radialBall_apply (π : Kˣ) (hK : IsCompact (Metric.closedBall (0 : K) 1))
    (hopen : IsOpen (Metric.closedBall (0 : K) 1)) (n : ℤ) (x : K) :
    (radialBall π hK hopen n).val x = if ‖x‖ ≤ ‖π.val‖ ^ n then 1 else 0 := by
  classical
  change (Metric.closedBall (0 : K) (‖π.val‖ ^ n)).indicator (fun _ => (1 : ℂ)) x = _
  rw [indicator_apply, Metric.mem_closedBall, dist_zero_right]

theorem finitePrincipalValue_radialBall (π : Kˣ) (hπ : ‖π.val‖ < 1)
    (hK : IsCompact (Metric.closedBall (0 : K) 1))
    (hopen : IsOpen (Metric.closedBall (0 : K) 1)) (n m : ℤ) {x : K}
    (hx : ‖x‖ = ‖π.val‖ ^ m) :
    (finitePrincipalValue π (radialBall π hK hopen n)).val x = if n = m then 1 else 0 := by
  have hr := norm_pos_iff.mpr π.ne_zero
  have hleft : ‖x‖ ≤ ‖π.val‖ ^ n ↔ n ≤ m := by
    rw [hx, zpow_le_zpow_iff_right_of_lt_one₀ hr hπ]
  have hright : ‖π.val⁻¹ * x‖ ≤ ‖π.val‖ ^ n ↔ n + 1 ≤ m := by
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hr, mul_comm ‖π.val‖, ← zpow_add_one₀ hr.ne',
      hx, zpow_le_zpow_iff_right_of_lt_one₀ hr hπ]
  simp only [finitePrincipalValue_apply, radialBall_apply, hleft, hright]
  by_cases h : n = m
  · simp [h]
  · by_cases hnm : n ≤ m
    · have : n + 1 ≤ m := by omega
      simp [h, hnm, this]
    · have : ¬ n + 1 ≤ m := by omega
      simp [h, hnm, this]

/-- A radial test vanishing at zero has a preimage which is a finite sum of
ball indicators. -/
theorem finitePrincipalValue_radial_range_sum (π : Kˣ) (hπ : ‖π.val‖ < 1)
    (hK : IsCompact (Metric.closedBall (0 : K) 1))
    (hopen : IsOpen (Metric.closedBall (0 : K) 1))
    (hdiscrete : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π.val‖ ^ n)
    (f : locallyConstantTests K) (hf : ∀ x y, ‖x‖ = ‖y‖ → f.val x = f.val y)
    (hf0 : f.val 0 = 0) :
    ∃ (I : Finset ℤ) (c : ℤ → ℂ),
      finitePrincipalValue π (∑ n ∈ I, c n • radialBall π hK hopen n) = f := by
  classical
  have hr := norm_pos_iff.mpr π.ne_zero
  obtain ⟨R, hR⟩ := f.property.2.isBounded.subset_closedBall (0 : K)
  have ht : Tendsto (fun n : ℕ => π.val ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ
  have hsmall := ht.eventually (f.property.1.eventually_eq 0)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  have ht' := tendsto_pow_atTop_atTop_of_one_lt ((one_lt_inv₀ hr).mpr hπ)
  obtain ⟨M, hM⟩ := (ht'.eventually (eventually_gt_atTop R)).exists
  let I := Finset.Icc (-(M : ℤ)) (N : ℤ)
  let c (n : ℤ) := f.val (π.val ^ n)
  have hc (m : ℤ) (hm : m ∉ I) : c m = 0 := by
    simp only [I, Finset.mem_Icc, not_and_or, not_le] at hm
    rcases hm with h | h
    · change f.val (π.val ^ m) = 0
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hh := hR hx
      rw [Metric.mem_closedBall, dist_zero_right, norm_zpow] at hh
      have hlt : ‖π.val‖ ^ (-(M : ℤ)) < ‖π.val‖ ^ m :=
        (zpow_lt_zpow_iff_right_of_lt_one₀ hr hπ).2 h
      rw [zpow_neg, zpow_natCast, ← inv_pow] at hlt
      exact (hM.trans hlt).not_ge hh
    · have hm_pos : 0 ≤ m := by omega
      have hNm : N ≤ m.toNat := by omega
      simpa only [c, ← zpow_natCast, Int.toNat_of_nonneg hm_pos, hf0] using hN _ hNm
  let g := ∑ n ∈ I, c n • radialBall π hK hopen n
  refine ⟨I, c, ?_⟩
  apply Subtype.ext
  funext x
  by_cases hx : x = 0
  · rw [hx, finitePrincipalValue_eval_zero, hf0]
  · obtain ⟨m, hm⟩ := hdiscrete x hx
    have hfx : f.val x = c m := hf _ _ (by rw [hm, norm_zpow])
    simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul_of_tower, Pi.smul_apply, finitePrincipalValue_radialBall π hπ hK hopen _ m hm,
      smul_ite, smul_zero, Finset.sum_ite_eq', hfx]
    split_ifs with h
    · simp
    · simp [hc m h]

/-- The evaluation-kernel range clause holds on radial tests. -/
theorem finitePrincipalValue_radial_range (π : Kˣ) (hπ : ‖π.val‖ < 1)
    (hK : IsCompact (Metric.closedBall (0 : K) 1))
    (hopen : IsOpen (Metric.closedBall (0 : K) 1))
    (hdiscrete : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π.val‖ ^ n)
    (f : locallyConstantTests K) (hf : ∀ x y, ‖x‖ = ‖y‖ → f.val x = f.val y)
    (hf0 : f.val 0 = 0) :
    ∃ g : locallyConstantTests K, (∀ x y, ‖x‖ = ‖y‖ → g.val x = g.val y) ∧
      finitePrincipalValue π g = f := by
  obtain ⟨I, c, h⟩ := finitePrincipalValue_radial_range_sum π hπ hK hopen hdiscrete f hf hf0
  refine ⟨∑ n ∈ I, c n • radialBall π hK hopen n, ?_, h⟩
  intro x y hxy
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
    Pi.smul_apply, radialBall_apply, hxy]

end Radial

section Completions

open IsDedekindDomain NumberField
open scoped NNReal NumberField WithZero

variable (F : Type*) [Field F] [NumberField F]

theorem finiteCompletion_closedBall (v : HeightOneSpectrum (𝓞 F)) :
    Metric.closedBall (0 : v.adicCompletion F) 1 =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext x
  change _ ↔ x ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Metric.mem_closedBall, dist_zero_right,
    FinitePlace.norm_def]
  exact WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)

theorem finiteCompletion_uniformizer_contracts (v : HeightOneSpectrum (𝓞 F))
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    ‖π.val‖ < 1 := by
  rw [norm_finiteUniformizer F v π.val hπ]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)

theorem finiteCompletion_norm_zpow (v : HeightOneSpectrum (𝓞 F))
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (x : v.adicCompletion F) (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = ‖π.val‖ ^ n := by
  have hn : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) x ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hx
  refine ⟨-(WithZero.unzero hn).toAdd, ?_⟩
  rw [norm_finiteUniformizer F v π.val hπ, FinitePlace.norm_def,
    WithZeroMulInt.toNNReal_neg_apply _ hn, zpow_neg, inv_zpow, inv_inv]
  exact NNReal.coe_zpow _ _

theorem finiteCompletion_norm_eq_one_iff (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    ‖u.val‖ = 1 ↔ (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) u.val = 1 := by
  have h := HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [FinitePlace.norm_def]
  exact (NNReal.coe_eq_one).trans (WithZeroMulInt.toNNReal_eq_one_iff _ h.ne_zero h.ne')

/-- The integer-ring indicator as a compactly supported locally constant test. -/
def finiteCompletionIntegerRingTest (v : HeightOneSpectrum (𝓞 F)) :
    locallyConstantTests (v.adicCompletion F) :=
  compactOpenIndicator _ ⟨v.adicCompletionIntegers F, finitePlaceIntegral_compact F v,
    Valued.isOpen_valuationSubring _⟩

/-- The inverse-uniformizer difference of the integer-ring test cuts out the
unit shell, as used in the proof of Theorem 3.4.1.1. The local proof uses the
radial ball calculation to implement the argument from original commit ef7da4e. -/
theorem finitePrincipalValue_integerRing_apply (v : HeightOneSpectrum (𝓞 F))
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (u : (v.adicCompletion F)ˣ) :
    (finitePrincipalValue π (finiteCompletionIntegerRingTest F v)).val u.val =
      if ‖u.val‖ = 1 then 1 else 0 := by
  have hK := (finiteCompletion_closedBall F v).symm ▸ finitePlaceIntegral_compact F v
  have hopen : IsOpen (Metric.closedBall (0 : v.adicCompletion F) 1) :=
    (finiteCompletion_closedBall F v).symm ▸ Valued.isOpen_valuationSubring _
  have he : finiteCompletionIntegerRingTest F v = radialBall π hK hopen 0 := by
    apply Subtype.ext
    funext x
    rw [radialBall_apply, zpow_zero]
    change (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
      (fun _ => (1 : ℂ)) x = _
    rw [← finiteCompletion_closedBall F v]
    by_cases h : ‖x‖ ≤ 1 <;> simp [h]
  obtain ⟨m, hm⟩ := finiteCompletion_norm_zpow F v π hπ u.val u.ne_zero
  have hr := norm_pos_iff.mpr π.ne_zero
  have hc := finiteCompletion_uniformizer_contracts F v π hπ
  have hunit : ‖u.val‖ = 1 ↔ (0 : ℤ) = m := by
    rw [hm, ← zpow_zero (‖π.val‖ : ℝ)]
    exact ⟨fun h => ((zpow_right_injective₀ hr hc.ne) h).symm, fun h => h ▸ rfl⟩
  rw [he, finitePrincipalValue_radialBall π hc hK hopen 0 m hm]
  simp only [hunit]

/-- Radial tests are exactly the tests invariant under multiplication by units of norm one. -/
theorem locallyConstantTests_radial_iff {K : Type*} [NormedField K]
    (f : locallyConstantTests K) :
    (∀ x y, ‖x‖ = ‖y‖ → f.val x = f.val y) ↔
      ∀ (u : Kˣ), ‖u.val‖ = 1 → ∀ x, f.val (u.val * x) = f.val x := by
  constructor
  · intro h u hu x
    exact h _ _ (by simp [norm_mul, hu])
  · intro h x y hxy
    by_cases hy : y = 0
    · have hx : x = 0 := norm_eq_zero.mp (by simpa [hy] using hxy)
      simp [hx, hy]
    · have hx : x ≠ 0 := fun hx => hy (norm_eq_zero.mp (by simpa [hx] using hxy.symm))
      let u := Units.mk0 (x / y) (div_ne_zero hx hy)
      have hu : ‖u.val‖ = 1 := by
        rw [show u.val = x / y from rfl, norm_div, hxy, div_self (norm_ne_zero_iff.mpr hy)]
      simpa [u, div_mul_cancel₀ _ hy] using h u hu y

/-- Corrected Lemma 5.3.1.1. For any finite completion, the difference with a
fixed uniformizer is a topological embedding. On unit-invariant tests it is
uniformizer independent and its range is exactly the kernel of evaluation at zero. -/
theorem finiteCompletion_principalValue (v : HeightOneSpectrum (𝓞 F))
    (π π' : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) (hπ' : Valued.v.IsUniformizer π'.val) :
    let K := v.adicCompletion F
    let S := locallyConstantTests K
    letI : TopologicalSpace S := finestLocallyConvexTopology _
    let radial (f : S) := ∀ x y : K, ‖x‖ = ‖y‖ → f.val x = f.val y
    IsEmbedding (finitePrincipalValue π) ∧
      (∀ f : S, radial f → finitePrincipalValue π f = finitePrincipalValue π' f) ∧
      (∀ f : S, (∃ g : S, radial g ∧ finitePrincipalValue π g = f) ↔
        radial f ∧ f.val 0 = 0) := by
  have hc := finiteCompletion_uniformizer_contracts F v π hπ
  refine ⟨finitePrincipalValue_isEmbedding π hc, ?_, ?_⟩
  · exact fun f hf => finitePrincipalValue_radial_independent π π'
      ((norm_finiteUniformizer F v _ hπ).trans (norm_finiteUniformizer F v _ hπ').symm)
      f hf
  · intro f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨finitePrincipalValue_radial π g hg, finitePrincipalValue_eval_zero π g⟩
    · intro hf
      apply finitePrincipalValue_radial_range π hc _ _ (finiteCompletion_norm_zpow F v π hπ)
        f hf.1 hf.2
      · rw [finiteCompletion_closedBall F v]
        exact finitePlaceIntegral_compact F v
      · rw [finiteCompletion_closedBall F v]
        exact Valued.isOpen_valuationSubring (v.adicCompletion F)

end Completions

private def principalValueWitness : locallyConstantTests Q₃ :=
  compactOpenIndicator Q₃ ⟨Metric.ball 1 1,
    (isCompact_closedBall 1 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall, Metric.isOpen_ball⟩

private theorem principalValueWitness_apply (x : Q₃) :
    principalValueWitness.val x = if dist x 1 < 1 then 1 else 0 := by
  classical
  change (Metric.ball (1 : Q₃) 1).indicator (fun _ => (1 : ℂ)) x = _
  rw [indicator_apply, Metric.mem_ball]

private theorem norm_eq_one_of_close_to_one {x : Q₃} (hx : dist x 1 < 1) : ‖x‖ = 1 := by
  have h₁ : dist (1 : Q₃) 0 = 1 := by simp
  have h := IsUltrametricDist.dist_eq_max_of_dist_ne_dist x 1 0 (by
    rw [h₁]
    exact hx.ne)
  simpa only [dist_zero_right, h₁, max_eq_right hx.le] using h

private theorem padicThree_norm : ‖(3 : Q₃)‖ = (3 : ℝ)⁻¹ :=
  Padic.norm_p

private theorem padicThree_ne_zero : (3 : Q₃) ≠ 0 := by
  intro h
  have hnorm := padicThree_norm
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

private theorem witness_three_orbit (x : Q₃) (hx : ‖x‖ = 1) (n : ℕ) :
    principalValueWitness.val ((3 : Q₃) ^ (n + 1) * x) = 0 ∧
      principalValueWitness.val (((3 : Q₃)⁻¹) ^ (n + 1) * x) = 0 := by
  have hpos : ‖(3 : Q₃) ^ (n + 1) * x‖ < 1 := by
    rw [norm_mul, norm_pow, hx, mul_one, padicThree_norm]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by simp)
  have hneg : 1 < ‖((3 : Q₃)⁻¹) ^ (n + 1) * x‖ := by
    rw [norm_mul, norm_pow, hx, mul_one, norm_inv, padicThree_norm, inv_inv]
    exact one_lt_pow₀ (by norm_num) (by simp)
  simp only [principalValueWitness_apply]
  exact ⟨ite_eq_right (fun h => hpos.ne (norm_eq_one_of_close_to_one h)),
    ite_eq_right (fun h => hneg.ne' (norm_eq_one_of_close_to_one h))⟩

private theorem witness_preimage_value (f : locallyConstantTests Q₃)
    (h : ∀ x, f.val x - f.val ((3 : Q₃)⁻¹ * x) = principalValueWitness.val x)
    (x : Q₃) (hx : ‖x‖ = 1) : f.val 0 = principalValueWitness.val x := by
  have hforward (n : ℕ) : f.val ((3 : Q₃) ^ n * x) = f.val x := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he := h ((3 : Q₃) ^ (n + 1) * x)
      rw [(witness_three_orbit x hx n).1] at he
      rw [pow_succ', ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ padicThree_ne_zero,
        one_mul] at he
      simpa only [pow_succ'] using (sub_eq_zero.mp he).trans ih
  have hbackward (n : ℕ) :
      f.val (((3 : Q₃)⁻¹) ^ (n + 1) * x) = f.val ((3 : Q₃)⁻¹ * x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he := h (((3 : Q₃)⁻¹) ^ (n + 1) * x)
      rw [(witness_three_orbit x hx n).2, ← mul_assoc, ← pow_succ'] at he
      exact (sub_eq_zero.mp he).symm.trans ih
  have ht : Tendsto (fun n : ℕ => (3 : Q₃) ^ n * x) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (x := (3 : Q₃)) (by rw [padicThree_norm]; norm_num)
    simpa only [zero_mul] using hpow.mul_const x
  have hlimit : Tendsto (fun n : ℕ => f.val ((3 : Q₃) ^ n * x)) atTop (𝓝 (f.val 0)) :=
    f.property.1.continuous.continuousAt.tendsto.comp ht
  simp only [hforward] at hlimit
  have hfx : f.val x = f.val 0 := tendsto_nhds_unique tendsto_const_nhds hlimit
  obtain ⟨R, hR⟩ := f.property.2.isBounded.subset_closedBall (0 : Q₃)
  have ht' : Tendsto (fun n : ℕ => (3 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨n, hn₁, hn⟩ := ((eventually_ge_atTop (1 : ℕ)).and
    (ht'.eventually (eventually_gt_atTop R))).exists
  have hnorm (k : ℕ) : ‖((3 : Q₃)⁻¹) ^ k * x‖ = (3 : ℝ) ^ k := by
    rw [norm_mul, hx, mul_one, norm_pow, norm_inv, padicThree_norm, inv_inv]
  have hz : f.val (((3 : Q₃)⁻¹) ^ n * x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hle := hR hm
    rw [Metric.mem_closedBall, dist_zero_right, hnorm] at hle
    exact hn.not_ge hle
  have hback : f.val ((3 : Q₃)⁻¹ * x) = 0 := by
    cases n with
    | zero => simp at hn₁
    | succ n => exact (hbackward n).symm.trans hz
  simpa only [hfx, hback, sub_zero] using h x

private def threeUnit : Q₃ˣ := Units.mk0 3 padicThree_ne_zero

private theorem witness_neg_one : principalValueWitness.val (-1) = 0 := by
  have htwo : ‖(2 : Q₃)‖ = 1 := by
    exact (Padic.norm_natCast_eq_one_iff (p := 3) (n := 2)).2 (by decide)
  have hdist : dist (-1 : Q₃) 1 = 1 := by
    rw [dist_eq_norm, show (-1 : Q₃) - 1 = -(2 : Q₃) by ring, norm_neg, htwo]
  simp [principalValueWitness_apply, hdist]

/-- The range on the full local test space is smaller than the kernel of evaluation at zero. -/
theorem finitePrincipalValue_range_counterexample :
    ∃ f : locallyConstantTests Q₃, f.val 0 = 0 ∧
      f ∉ LinearMap.range (finitePrincipalValue threeUnit) := by
  refine ⟨principalValueWitness, by simp [principalValueWitness_apply], ?_⟩
  rintro ⟨g, hg⟩
  have he (x : Q₃) := congrArg (fun f : locallyConstantTests Q₃ => f.val x) hg
  simp only [finitePrincipalValue_apply, threeUnit, Units.val_mk0] at he
  have h₁ := witness_preimage_value g he 1 norm_one
  have h₂ := witness_preimage_value g he (-1) (by simp)
  rw [witness_neg_one] at h₂
  rw [h₂] at h₁
  simp [principalValueWitness_apply] at h₁

/-- The two uniformizers 3 and -3 give different differences on the full test space. -/
theorem finitePrincipalValue_uniformizer_counterexample :
    finitePrincipalValue threeUnit ≠
      finitePrincipalValue (Units.mk0 (-3 : Q₃) (neg_ne_zero.mpr padicThree_ne_zero)) := by
  intro h
  have he := congrArg
    (fun L : locallyConstantTests Q₃ →ₗ[ℂ] locallyConstantTests Q₃ =>
      (L principalValueWitness).val 3) h
  simp only [finitePrincipalValue_apply, threeUnit, Units.val_mk0, inv_neg,
    neg_mul, inv_mul_cancel₀ padicThree_ne_zero, witness_neg_one, sub_zero] at he
  have hone : principalValueWitness.val (1 : Q₃) = 1 := by
    simp [principalValueWitness_apply]
  rw [hone] at he
  exact one_ne_zero (sub_eq_self.mp he)

end

end Masullo
