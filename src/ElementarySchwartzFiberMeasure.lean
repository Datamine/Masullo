/-
The lattice-box argument adapts RiemannMasullo AppD_SchwartzBruhat/Sec1c.lean
at a1d61084d11ef14e3119178113488c654be4da80 (Apache-2.0).
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import ElementarySchwartzHaar
import ElementarySchwartzRefinement
import Mathlib.MeasureTheory.Function.Floor

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace Masullo

noncomputable section

/-- Haar mass of a closed subgroup intersected with translates of a
fixed compact set is uniformly bounded. -/
private theorem fiber_measure_compactTranslate {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (K : Subgroup A) (hK : IsClosed (K : Set A)) (ν : Measure K) [ν.IsHaarMeasure]
    (C : Set A) (hC : IsCompact C) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ x : A, ν {k : K | x * k.val ∈ C} ≤ M := by
  let D := (Subtype.val : K → A) ⁻¹' (C⁻¹ * C)
  have hD : IsCompact D := hK.isClosedEmbedding_subtypeVal.isCompact_preimage (hC.inv.mul hC)
  refine ⟨ν D, hD.measure_lt_top, fun x => ?_⟩
  by_cases h : ∃ k : K, x * k.val ∈ C
  · obtain ⟨k₀, hk₀⟩ := h
    calc
      _ ≤ ν ((k₀⁻¹ * ·) ⁻¹' D) := by
        apply measure_mono
        intro k hk
        exact ⟨(x * k₀.val)⁻¹, Set.inv_mem_inv.mpr hk₀, x * k.val, hk, by
          change (x * k₀.val)⁻¹ * (x * k.val) = k₀.val⁻¹ * k.val
          group⟩
      _ = _ := measure_preimage_mul _ _ _
  · rw [show {k : K | x * k.val ∈ C} = ∅ from Set.eq_empty_iff_forall_notMem.mpr
      (fun k hk => h ⟨k, hk⟩), measure_empty]
    exact bot_le

variable {A : Type*} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [T2Space A] [MeasurableSpace A] [BorelSpace A]

def fibreCoordinate (e : ElementaryLCAPresentation A) (x : A) :
    Fin e.realDim ⊕ Fin e.latticeRank → ℝ :=
  Sum.elim (fun j => (e.equiv x).toAdd.1 j) (fun j => ((e.equiv x).toAdd.2.2.1 j : ℝ))

omit [IsTopologicalGroup A] [T2Space A] [MeasurableSpace A] [BorelSpace A] in
private theorem fibreCoordinate_continuous (e : ElementaryLCAPresentation A) :
    Continuous (fibreCoordinate e) := by
  apply continuous_pi
  intro j
  cases j with
  | inl i => exact (PiLp.continuous_apply 2 _ i).comp e.equiv.continuous.fst
  | inr i =>
    exact (continuous_of_discreteTopology (f := fun z : ℤ => (z : ℝ))).comp
      ((continuous_apply i).comp e.equiv.continuous.snd.snd.fst)

set_option maxHeartbeats 1500000 in
/-- A reciprocal quadratic weight in each real and lattice coordinate
is integrable with a uniform bound on every translated closed subgroup. -/
theorem elementary_fibreWeight_integrable (e : ElementaryLCAPresentation A)
    (K : Subgroup A) (hK : IsClosed (K : Set A)) (ν : Measure K) [ν.IsHaarMeasure] :
    ∃ C : ℝ, ∀ y : A,
      let w (k : K) := ∏ j, (1 + (fibreCoordinate e (y * k.val) j)^2)⁻¹
      Integrable w ν ∧ (∫ k, w k ∂ν) ≤ C := by
  classical
  let J := Fin e.realDim ⊕ Fin e.latticeRank
  let E := ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor
  let coord := fibreCoordinate e
  have hc : Continuous coord := fibreCoordinate_continuous e
  let box : Set E := ((EuclideanSpace.equiv (Fin e.realDim) ℝ) ⁻¹'
      (Set.pi univ fun _ : Fin e.realDim => Icc (0 : ℝ) 1)) ×ˢ (univ ×ˢ ({0} ×ˢ univ))
  have hbox : IsCompact box :=
    ((EuclideanSpace.equiv (Fin e.realDim) ℝ).toHomeomorph.isProperMap.isCompact_preimage
      (isCompact_univ_pi fun _ => isCompact_Icc)).prod
        (isCompact_univ.prod (isCompact_singleton.prod isCompact_univ))
  obtain ⟨M, hM, hm⟩ := fiber_measure_compactTranslate K hK ν _
    (e.equiv.toHomeomorph.isProperMap.isCompact_preimage hbox)
  let label (x : A) (j : J) := ⌊coord x j⌋
  have hlabel : Measurable label := measurable_pi_iff.mpr fun j =>
    ((continuous_apply j).comp hc).measurable.floor
  have hcell (y : A) (i : J → ℤ) : ν {k : K | label (y * k.val) = i} ≤ M := by
    let c : A := e.equiv.symm (.ofAdd (WithLp.toLp 2 (fun j => (i (.inl j) : ℝ)), 0,
      (fun j => i (.inr j)), 0))
    apply le_trans (measure_mono ?_) (hm (c⁻¹ * y))
    intro k hk
    have he : label (y * k.val) = i := hk
    have htrans : e.equiv (c⁻¹ * y * k.val) = (e.equiv c)⁻¹ * e.equiv (y * k.val) := by simp [mul_assoc]
    change (e.equiv (c⁻¹ * y * k.val)).toAdd ∈ box
    rw [htrans, show e.equiv c = _ from e.equiv.apply_symm_apply _]
    refine ⟨fun j _ => ⟨?_, ?_⟩, trivial, ?_, trivial⟩
    · change 0 ≤ -(i (.inl j) : ℝ) + coord (y * k.val) (.inl j)
      rw [← he]
      dsimp [label]
      linarith [Int.floor_le (coord (y * k.val) (.inl j))]
    · change -(i (.inl j) : ℝ) + coord (y * k.val) (.inl j) ≤ 1
      rw [← he]
      have := Int.lt_floor_add_one (coord (y * k.val) (.inl j))
      dsimp [label]
      linarith
    · change -(fun j => i (Sum.inr j)) + (e.equiv (y * k.val)).toAdd.2.2.1 = 0
      ext j
      have h := congrFun he (Sum.inr j)
      change ⌊((e.equiv (y * k.val)).toAdd.2.2.1 j : ℝ)⌋ = i (.inr j) at h
      simp [Pi.add_apply, Pi.neg_apply, ← h]
  let d (i : J → ℤ) : ℝ := ∏ j, (1 + (i j : ℝ)^2)⁻¹
  have hd : Summable d := summable_lattice_product
  have hd0 i : 0 ≤ d i := Finset.prod_nonneg fun _ _ => by positivity
  let B : ℝ := 8 ^ Fintype.card J
  have hB : 0 ≤ B := by positivity
  refine ⟨(B * M.toReal) * ∑' i, d i, fun y => ?_⟩
  let w (k : K) : ℝ := ∏ j, (1 + (coord (y * k.val) j)^2)⁻¹
  let S (i : J → ℤ) := {k : K | label (y * k.val) = i}
  have hS (i) : MeasurableSet (S i) := (measurableSet_singleton i).preimage
    (hlabel.comp (continuous_const.mul continuous_subtype_val).measurable)
  have hcov : ⋃ i, S i = univ := iUnion_eq_univ_iff.mpr fun k => ⟨_, rfl⟩
  have hw (k : K) : 0 ≤ w k := Finset.prod_nonneg fun _ _ => by positivity
  have hwc : Continuous w := continuous_finsetProd _ fun j _ =>
    (continuous_const.add ((((continuous_apply j).comp hc).comp
      (continuous_const.mul continuous_subtype_val)).pow 2)).inv₀ (fun k => by
        change 1 + coord (y * k.val) j ^ 2 ≠ 0
        positivity)
  have hbound (i) (k : K) (hk : k ∈ S i) : w k ≤ B * d i := by
    change label (y * k.val) = i at hk
    subst i
    dsimp [w, d, B]
    rw [show (8 : ℝ) ^ Fintype.card J = ∏ _ : J, (8 : ℝ) from by simp, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun _ _ => by positivity) (fun j _ => ?_)
    let t := coord (y * k.val) j
    change (1 + t^2)⁻¹ ≤ 8 * (1 + (⌊t⌋ : ℝ)^2)⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
    have h1 := Int.floor_le t
    have h2 := Int.lt_floor_add_one t
    nlinarith [sq_nonneg (t - 2 * (⌊t⌋ : ℝ)), mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2.le),
      sq_nonneg t]
  have hm' (i) : ν (S i) < ⊤ := (hcell y i).trans_lt hM
  have hi (i) : IntegrableOn w (S i) ν :=
    (integrableOn_const (C := B * d i) (hs := (hm' i).ne)).mono' hwc.aestronglyMeasurable
      ((ae_restrict_mem (hS i)).mono fun k hk => by
        simpa [Real.norm_of_nonneg (hw k)] using hbound i k hk)
  have hI (i) : ∫ k in S i, ‖w k‖ ∂ν ≤ (B * M.toReal) * d i := by
    calc
      _ ≤ ∫ _ in S i, B * d i ∂ν := integral_mono_ae (hi i).norm
        (integrableOn_const (C := B * d i) (hs := (hm' i).ne))
        ((ae_restrict_mem (hS i)).mono fun k hk => by
          simpa [Real.norm_of_nonneg (hw k)] using hbound i k hk)
      _ = (ν (S i)).toReal * (B * d i) := by rw [setIntegral_const, smul_eq_mul]; rfl
      _ ≤ _ := by
        calc
          _ ≤ M.toReal * (B * d i) :=
            mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hM.ne (hcell y i)) (mul_nonneg hB (hd0 _))
          _ = _ := by ring
  have hsum := hd.mul_left (B * M.toReal)
  have hs := hsum.of_nonneg_of_le (fun i => integral_nonneg fun k => norm_nonneg (w k)) hI
  have hint := integrableOn_iUnion_of_summable_integral_norm hi hs
  rw [hcov, integrableOn_univ] at hint
  refine ⟨hint, ?_⟩
  change ∫ k, w k ∂ν ≤ _
  have hdj : Pairwise (Disjoint on S) := fun i j hij => Set.disjoint_left.mpr
    fun k hi hj => hij ((show label (y * k.val) = i from hi).symm.trans hj)
  calc
    _ = ∑' i, ∫ k in S i, w k ∂ν := by
      rw [← integral_iUnion (fun i => hS i) hdj, hcov, setIntegral_univ]
      rwa [hcov, integrableOn_univ]
    _ ≤ ∑' i, (B * M.toReal) * d i := by
      simpa only [Real.norm_of_nonneg (hw _)] using hs.tsum_le_tsum hI hsum
    _ = _ := tsum_mul_left

set_option maxHeartbeats 850000 in
/-- Polynomially weighted elementary Schwartz tests have a reciprocal
quadratic majorant in every real and lattice coordinate. -/
theorem elementarySchwartz_fibreDecay_seminorm (e : ElementaryLCAPresentation A)
    (P : MvPolynomial (Fin e.realDim ⊕ Fin e.latticeRank) ℂ) :
    ∃ Q : Seminorm ℂ (ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor),
      Continuous Q ∧ ∀ f (x : A),
      let y := (e.equiv x).toAdd
      ‖MvPolynomial.eval (elementaryGrowthVariables y) P * f y‖ ≤
        Q f * ∏ j, (1 + (fibreCoordinate e x j)^2)⁻¹ := by
  let J := Fin e.realDim ⊕ Fin e.latticeRank
  let W (x : A) := ∏ j : J, (1 + (fibreCoordinate e x j)^2)⁻¹
  let R : MvPolynomial J ℂ := ∏ j, (1 + MvPolynomial.X j ^ 2)
  obtain ⟨Q, hQc, hQ⟩ := elementary_polynomialWord_bound
    (m := e.realDim) (n := e.torusDim) (F := e.finiteFactor) [] (R * P)
  refine ⟨Q, hQc, fun f x => ?_⟩
  let y := (e.equiv x).toAdd
  let D := ∏ j : J, (1 + (fibreCoordinate e x j)^2)
  have hD : 0 < D := Finset.prod_pos fun _ _ => by positivity
  have hEq : MvPolynomial.eval (elementaryGrowthVariables y) R = (D : ℂ) := by
    have h (j : J) : elementaryGrowthVariables y j = (fibreCoordinate e x j : ℂ) := by
      cases j <;> simp [elementaryGrowthVariables, fibreCoordinate, y]
    simp only [R, D, map_prod, map_add, map_one, map_pow, MvPolynomial.eval_X, h,
      Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  have h := hQ f y
  change ‖MvPolynomial.eval (elementaryGrowthVariables y) (R * P) * f y‖ ≤ Q f at h
  rw [map_mul, mul_assoc, hEq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le, mul_comm] at h
  change ‖MvPolynomial.eval (elementaryGrowthVariables y) P * f y‖ ≤ Q f * W x
  rwa [show W x = D⁻¹ from Finset.prod_inv_distrib _, ← div_eq_mul_inv, le_div_iff₀ hD]

/-- Pointwise polynomial decay of a fixed elementary Schwartz test. -/
theorem elementarySchwartz_fibreDecay (e : ElementaryLCAPresentation A)
    (P : MvPolynomial (Fin e.realDim ⊕ Fin e.latticeRank) ℂ)
    (f : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A,
      let y := (e.equiv x).toAdd
      ‖MvPolynomial.eval (elementaryGrowthVariables y) P * f y‖ ≤
        C * ∏ j, (1 + (fibreCoordinate e x j)^2)⁻¹ := by
  obtain ⟨Q, -, hQ⟩ := elementarySchwartz_fibreDecay_seminorm e P
  exact ⟨Q f, apply_nonneg Q f, hQ f⟩

set_option maxHeartbeats 1000000 in
/-- Fibre integrands of elementary Schwartz tests admit a locally uniform
integrable majorant. -/
theorem elementarySchwartz_fibre_integrable_dominated (e : ElementaryLCAPresentation A)
    (K : Subgroup A) (hK : IsClosed (K : Set A)) (ν : Measure K) [ν.IsHaarMeasure]
    (f : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor) :
    (∀ y : A, Integrable (fun k : K => f (e.equiv (y * k.val)).toAdd) ν) ∧
      ∀ y : A, ∃ b : K → ℝ, Integrable b ν ∧ ∀ᶠ z in 𝓝 y,
        ∀ k : K, ‖f (e.equiv (z * k.val)).toAdd‖ ≤ b k := by
  let E := ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor
  let J := Fin e.realDim ⊕ Fin e.latticeRank
  let W (x : A) := ∏ j : J, (1 + (fibreCoordinate e x j)^2)⁻¹
  obtain ⟨C₀, hC₀, hmain⟩ := elementarySchwartz_fibreDecay e 1 f
  simp only [map_one, one_mul] at hmain
  have hfc₀ : Continuous (fun y : E => f y) := by
    have h : (fun y : E => f y) = (elementarySchwartz_weightedWord [] [] f : E → ℂ) := by
      funext y
      simp [elementarySchwartz_weightedWord_apply, elementaryDualWord, elementaryOrbitWord]
    rw [h]
    exact (elementarySchwartz_weightedWord [] [] f).continuous
  have hfc : Continuous (fun y : A => f (e.equiv y).toAdd) := hfc₀.comp e.equiv.continuous
  obtain ⟨M, hM⟩ := elementary_fibreWeight_integrable e K hK ν
  have hI (y : A) : Integrable (fun k : K => f (e.equiv (y * k.val)).toAdd) ν :=
    ((hM y).1.const_mul C₀).mono'
      (hfc.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
      (.of_forall fun k => hmain (y * k.val))
  refine ⟨hI, fun y => ?_⟩
  let C : ℝ := 3 ^ Fintype.card J
  have hshift (z w : A) :
      fibreCoordinate e (z * w) = fibreCoordinate e z + fibreCoordinate e w := by
    funext j
    cases j <;> simp [fibreCoordinate, map_mul]
  have hclose (j : J) :
      Continuous (fun z : A => fibreCoordinate e (z * y⁻¹) j) := by
    exact ((continuous_apply j).comp (fibreCoordinate_continuous e)).comp
      (continuous_id.mul continuous_const)
  have hy (j : J) : fibreCoordinate e (y * y⁻¹) j = 0 := by
    rw [mul_inv_cancel]
    cases j <;> simp [fibreCoordinate, map_one]
  have he : ∀ᶠ z in 𝓝 y, ∀ j, |fibreCoordinate e (z * y⁻¹) j| ≤ 1 := by
    rw [eventually_all]
    intro j
    have h := (Metric.tendsto_nhds.mp ((hclose j).tendsto y) 1 zero_lt_one)
    exact h.mono fun z hz => by
      rw [dist_eq_norm, hy, sub_zero, Real.norm_eq_abs] at hz
      exact hz.le
  have hW (z : A) (hz : ∀ j, |fibreCoordinate e (z * y⁻¹) j| ≤ 1) (k : K) :
      W (z * k.val) ≤ C * W (y * k.val) := by
    have ht : fibreCoordinate e (z * k.val) =
        fibreCoordinate e (z * y⁻¹) + fibreCoordinate e (y * k.val) := by
      rw [← hshift]
      congr 1
      group
    dsimp only [W, C]
    rw [ht, show (3 : ℝ) ^ Fintype.card J = ∏ _ : J, (3 : ℝ) from by simp, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro j _
    let a := fibreCoordinate e (y * k.val) j
    let b := fibreCoordinate e (z * y⁻¹) j
    change (1 + (b + a)^2)⁻¹ ≤ 3 * (1 + a^2)⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div,
      div_le_iff₀ (by positivity)]
    obtain ⟨hb₁, hb₂⟩ := abs_le.mp (hz j)
    nlinarith [sq_nonneg (a + 2 * b), sq_nonneg (a + b),
      mul_nonneg (sub_nonneg.mpr hb₂) (show 0 ≤ 1 + b by linarith)]
  refine ⟨fun k => (C₀ * C) * W (y * k.val), (hM y).1.const_mul (C₀ * C), ?_⟩
  exact he.mono fun z hz k => by
    refine (hmain (z * k.val)).trans ?_
    change C₀ * W (z * k.val) ≤ (C₀ * C) * W (y * k.val)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hW z hz k) hC₀

/-- The integral over every translated closed subgroup is absolutely
convergent and varies continuously with the translating element. -/
theorem elementarySchwartz_fibre_integrable_continuous (e : ElementaryLCAPresentation A)
    (K : Subgroup A) (hK : IsClosed (K : Set A)) (ν : Measure K) [ν.IsHaarMeasure]
    (f : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor) :
    (∀ y : A, Integrable (fun k : K => f (e.equiv (y * k.val)).toAdd) ν) ∧
      Continuous (fun y : A => ∫ k : K, f (e.equiv (y * k.val)).toAdd ∂ν) := by
  let E := ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor
  letI : FirstCountableTopology (Multiplicative E) := (inferInstance : FirstCountableTopology E)
  letI : FirstCountableTopology A := e.equiv.toHomeomorph.isInducing.firstCountableTopology
  obtain ⟨hI, hD⟩ := elementarySchwartz_fibre_integrable_dominated e K hK ν f
  refine ⟨hI, continuous_iff_continuousAt.mpr fun y => ?_⟩
  obtain ⟨b, hb, hdom⟩ := hD y
  apply continuousAt_of_dominated (bound := b)
  · exact .of_forall fun z => (hI z).aestronglyMeasurable
  · exact hdom.mono fun z hz => .of_forall hz
  · exact hb
  · have hfc : Continuous (fun z : E => f z) := by
      have he : (fun z : E => f z) = (elementarySchwartz_weightedWord [] [] f : E → ℂ) := by
        funext z
        simp [elementarySchwartz_weightedWord_apply, elementaryDualWord, elementaryOrbitWord]
      rw [he]
      exact (elementarySchwartz_weightedWord [] [] f).continuous
    exact .of_forall fun k => (hfc.comp (e.equiv.continuous.comp
      (continuous_id.mul continuous_const))).continuousAt

/-- A single fibre integral is bounded by a continuous seminorm in the input
test, uniformly over the translating element. -/
theorem elementarySchwartz_fibreIntegral_seminorm (e : ElementaryLCAPresentation A)
    (K : Subgroup A) (hK : IsClosed (K : Set A)) (ν : Measure K) [ν.IsHaarMeasure] :
    ∃ Q : Seminorm ℂ (ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor),
      Continuous Q ∧ ∀ f (y : A), ‖∫ k : K, f (e.equiv (y * k.val)).toAdd ∂ν‖ ≤ Q f := by
  obtain ⟨Q, hQc, hQ⟩ := elementarySchwartz_fibreDecay_seminorm e 1
  simp only [map_one, one_mul] at hQ
  obtain ⟨C, hC⟩ := elementary_fibreWeight_integrable e K hK ν
  refine ⟨‖C‖₊ • Q, hQc.const_smul _, fun f y => ?_⟩
  let w (k : K) := ∏ j, (1 + (fibreCoordinate e (y * k.val) j)^2)⁻¹
  have hf := (elementarySchwartz_fibre_integrable_dominated e K hK ν f).1 y
  change ‖∫ k : K, f (e.equiv (y * k.val)).toAdd ∂ν‖ ≤ ‖C‖ * Q f
  calc
    _ ≤ ∫ k : K, ‖f (e.equiv (y * k.val)).toAdd‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ k : K, Q f * w k ∂ν :=
      integral_mono hf.norm ((hC y).1.const_mul (Q f)) (fun k => hQ f (y * k.val))
    _ ≤ Q f * C := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hC y).2 (apply_nonneg Q f)
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (apply_nonneg Q f)

end
end Masullo
