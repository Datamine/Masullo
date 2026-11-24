import SLocalPrimaryLattices
import SLocalOrbitalFourierJets
import SLocalFourierTail
import VerticalJetInterpolation
import HomogeneousThetaStructure
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

section WeightedExpansion

variable {X ι : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]

private theorem exists_continuous_weighted_coefficient_seminorm [BarrelledSpace ℂ X]
    (D : ι → StrongDual ℂ X) (u : ι → ℝ≥0)
    (hu : ∀ x : X, Summable (fun i ↦ (u i : ℝ) * ‖D i x‖)) :
    ∃ r : Seminorm ℂ X, Continuous r ∧
      ∀ x : X, (∑' i, (u i : ℝ) * ‖D i x‖) ≤ r x := by
  let p (i : ι) : Seminorm ℂ X := u i • (normSeminorm ℂ ℂ).comp (D i).toLinearMap
  let P (s : Finset ι) : Seminorm ℂ X := ∑ i ∈ s, p i
  have hp (i : ι) : Continuous (p i) := ((D i).continuous.norm).const_smul (u i)
  have hP (s : Finset ι) : Continuous (P s) := Seminorm.continuous_finsetSum fun i _ ↦ hp i
  have he (s : Finset ι) (x : X) : P s x = ∑ i ∈ s, (u i : ℝ) * ‖D i x‖ := by
    simp [P, p, NNReal.smul_def]
  have hb : BddAbove (range P) := Seminorm.bddAbove_range_iff.mpr fun x ↦
    ⟨∑' i, (u i : ℝ) * ‖D i x‖, Set.forall_mem_range.mpr fun s ↦ by
      rw [he]
      exact (hu x).sum_le_tsum s (fun i _ ↦ by positivity)⟩
  refine ⟨⨆ s, P s, ?_, fun x ↦ ?_⟩
  · rw [Seminorm.coe_iSup_eq hb]
    exact Seminorm.continuous_iSup P hP hb
  · refine le_of_tendsto (hu x).hasSum (Eventually.of_forall fun s ↦ ?_)
    rw [← he, Seminorm.iSup_apply hb]
    exact le_ciSup ((Seminorm.bddAbove_range_iff.mp hb) x) s

theorem quotient_barrelled (R : Submodule ℂ X) [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [BarrelledSpace ℂ X] : BarrelledSpace ℂ (X ⧸ R) where
  continuous_of_lowerSemicontinuous q hq :=
    R.isQuotientMap_mkQ.continuous_iff.mpr
      ((q.comp R.mkQ).continuous_of_lowerSemicontinuous
        (hq.comp R.isQuotientMap_mkQ.continuous))

private theorem exists_clm_of_weighted_series
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup X] [BarrelledSpace ℂ X] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℂ Y] [T2Space Y] [PolynormableSpace ℂ Y]
    (D : ι → StrongDual ℂ X) (b : ι → Y) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hcoef : ∀ N : ℕ, ∀ x : X, Summable (fun i ↦ w i ^ N * ‖D i x‖))
    (hgrowth : ∀ q : Seminorm ℂ Y, Continuous q →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (b i) ≤ C * w i ^ N)
    (hs : ∀ x : X, ∃ y : Y, HasSum (fun i ↦ D i x • b i) y) :
    ∃ L : X →L[ℂ] Y, ∀ x, HasSum (fun i ↦ D i x • b i) (L x) := by
  choose g hg using hs
  let L : X →ₗ[ℂ] Y :=
    { toFun := g
      map_add' := fun x y ↦ (hg (x+y)).unique (by
        simpa only [map_add, add_smul, Pi.add_apply] using (hg x).add (hg y))
      map_smul' := fun a x ↦ (hg (a • x)).unique (by
        simpa only [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply, Pi.smul_apply] using
          (hg x).const_smul a) }
  refine ⟨⟨L, ?_⟩, hg⟩
  let W := PolynormableSpace.withSeminorms ℂ Y
  apply W.continuous_of_continuous_comp L
  intro q
  obtain ⟨C, hC, N, hbound⟩ := hgrowth q.val q.property
  let u (i : ι) : ℝ≥0 := ⟨w i ^ N, pow_nonneg (hw i) _⟩
  obtain ⟨r, hr, hrb⟩ := exists_continuous_weighted_coefficient_seminorm D u (hcoef N)
  let Cn : ℝ≥0 := ⟨C,hC⟩
  have hr' : Continuous (Cn • r : Seminorm ℂ X) := hr.const_smul Cn
  apply Seminorm.continuous_of_le hr'
  intro x
  change q.val (g x) ≤ C * r x
  apply le_of_tendsto (q.property.tendsto _ |>.comp (hg x))
  refine Eventually.of_forall fun s ↦ ?_
  change q.val (∑ i ∈ s, D i x • b i) ≤ C * r x
  calc
    _ ≤ ∑ i ∈ s, q.val (D i x • b i) :=
      Finset.le_sum_of_subadditive q.val (map_zero _).le (map_add_le_add q.val) _ _
    _ ≤ ∑ i ∈ s, C * (w i ^ N * ‖D i x‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul_eq_mul]
      exact (mul_le_mul_of_nonneg_left (hbound i) (norm_nonneg _)).trans_eq (by ring)
    _ ≤ C * r x := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (((hcoef N x).sum_le_tsum s (fun i _ ↦
          mul_nonneg (pow_nonneg (hw i) _) (norm_nonneg _))).trans (hrb x)) hC

private theorem strongDual_hasSum_of_weighted_coefficients
    [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [PolynormableSpace ℂ X] [BarrelledSpace ℂ X]
    (x : ι → X) (D : ι → StrongDual ℂ X)
    (w : ι → ℝ) (hw : ∀ i, 1 ≤ w i) (hinv : Summable (fun i ↦ (w i ^ 2)⁻¹))
    (hsum : ∀ y : X, HasSum (fun i ↦ D i y • x i) y)
    (hcoef : ∀ n : ℕ, ∀ y : X, Summable (fun i ↦ w i ^ n * ‖D i y‖))
    (hgrowth : ∀ q : Seminorm ℂ X, Continuous q →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ i, q (x i) ≤ C * w i ^ n)
    (g : StrongDual ℂ X) : HasSum (fun i ↦ g (x i) • D i) g := by
  obtain ⟨C, hC, n, hg⟩ := hgrowth ((normSeminorm ℂ ℂ).comp g.toLinearMap) g.continuous.norm
  let v (i : ι) : ℝ≥0 := ⟨w i ^ (n+2), pow_nonneg (zero_le_one.trans (hw i)) _⟩
  obtain ⟨r, hr, hrbound⟩ := exists_continuous_weighted_coefficient_seminorm D v (hcoef (n+2))
  let P (s : Finset ι) : StrongDual ℂ X := ∑ i ∈ s, g (x i) • D i
  let f (i : ι) (y : X) := g (x i) * D i y
  have hval (y : X) : (∑' i, f i y) = g y := by
    have h := g.hasSum (hsum y)
    apply HasSum.tsum_eq
    simpa [f, map_smul, mul_comm] using h
  have hP (s : Finset ι) (y : X) : P s y = ∑ i ∈ s, f i y := by
    simp [P, f]
  change Tendsto P atTop (𝓝 g)
  apply tendsto_sub_nhds_zero_iff.mp
  apply (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_ball).tendsto_right_iff.mpr
  rintro ⟨B, ε⟩ ⟨hB, hε⟩
  obtain ⟨M, hM, hMr⟩ :=
    (PolynormableSpace.withSeminorms ℂ X).isVonNBounded_iff_seminorm_bounded.mp hB ⟨r, hr⟩
  have hmajor (i : ι) (y : X) (hy : y ∈ B) : ‖f i y‖ ≤ (C*M) * (w i ^ 2)⁻¹ := by
    have hw₀ : 0 < w i := zero_lt_one.trans_le (hw i)
    have hb : w i ^ (n+2) * ‖D i y‖ ≤ M :=
      ((hcoef (n+2) y).le_tsum i (fun j _ ↦
        mul_nonneg (pow_nonneg (zero_le_one.trans (hw j)) _) (norm_nonneg _))).trans
        ((hrbound y).trans (hMr y hy).le)
    change ‖g (x i) * D i y‖ ≤ _
    rw [norm_mul, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hw₀ _)]
    calc
      _ ≤ (C * w i ^ n * ‖D i y‖) * w i ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hg i) (norm_nonneg _))
          (pow_nonneg hw₀.le _)
      _ = C * (w i ^ (n+2) * ‖D i y‖) := by rw [pow_add]; ring
      _ ≤ C * M := mul_le_mul_of_nonneg_left hb hC
  have ht := tendstoUniformlyOn_tsum (hinv.mul_left (C*M)) hmajor
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with s hs
  intro y hy
  have h := hs y hy
  rw [hval, ← hP, dist_comm, dist_eq_norm] at h
  simpa only [Metric.mem_ball, dist_zero_right, sub_apply] using h

end WeightedExpansion

private theorem summable_primary_inverseSquare {J : Type*} [Finite J] {d : ℝ} (hd : 0 < d) :
    Summable (fun i : J × ℤ ↦ ((1 + |(i.2 : ℝ)| * d)^2)⁻¹) := by
  apply (summable_prod_of_nonneg (fun _ ↦ by positivity)).mpr
  refine ⟨fun _ ↦ ?_, Summable.of_finite⟩
  let u (m : ℤ) := (d^2)⁻¹ * ((m : ℝ)^2)⁻¹
  let v (m : ℤ) : ℝ := if m = 0 then 1 else 0
  have hu : Summable u := by
    apply Summable.mul_left
    simpa only [one_div] using (Real.summable_one_div_int_pow (p := 2)).mpr (by decide)
  have hv : Summable v := by
    apply summable_of_ne_finset_zero (s := ({0} : Finset ℤ))
    intro m hm
    have hm' : m ≠ 0 := fun he ↦ hm (he ▸ Finset.mem_singleton_self _)
    simp [v, hm']
  refine (hu.add hv).of_nonneg_of_le (fun _ ↦ by positivity) fun m ↦ ?_
  by_cases hm : m = 0
  · subst m
    simp [u, v]
  · have hm₀ : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have ha : 0 < |(m : ℝ)| * d := mul_pos (abs_pos.mpr hm₀) hd
    change ((1 + |(m : ℝ)| * d)^2)⁻¹ ≤ u m + v m
    rw [show v m = 0 by simp [v, hm], add_zero]
    calc
      _ ≤ ((|(m : ℝ)| * d)^2)⁻¹ :=
        inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le (by linarith) _)
      _ = u m := by rw [mul_pow, mul_inv_rev, sq_abs]

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev K := SLocalThetaNormOne F S
private abbrev E := sLocalBruhatImage F S

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  (μ : ∀ v : S, Measure (v.val.adicCompletion F)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]
variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

private abbrev Z (ω : PontryaginDual (K F S)) (f : E F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

variable (hS : ∀ v : HeightOneSpectrum (𝓞 F),
  v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)

private abbrev T := sLocalStageFourier F S (sLocalFourier_preserves_stage_of_different F S hS)

include hν in
/-- A continuous lift realizes each entire Schwartz–Bergman transform
through the compressed Fourier operator on any finite stage. -/
theorem exists_sLocalFourierCompression_zeta_eq_schwartzBergmanCLM
    (ω : PontryaginDual (K F S)) :
    ∃ L : SchwartzBergman (univ : Set ℝ) →L[ℂ] E F S,
      ∀ G, EqOn (Z F S μ ω (sLocalFourierCompression F S (L G))) G.val {z | 0 < z.re} := by
  obtain ⟨L, hL⟩ := exists_sLocalPolarFree_zeta_eq_schwartzBergmanCLM F S μ ν hν ω
  let P := sLocalPolarFreeTestSubspace F S
  let C := sLocalFourierCompression F S
  let a : ℂ := ideleNorm F (sLocalCodifferentTailIdele F S)
  refine ⟨a • ((C.comp P.subtypeL).comp L), fun G ↦ ?_⟩
  let g := L G
  let f := a • C g.val
  have he : sLocalThetaOperator F S (C f) = sLocalThetaOperator F S g.val := by
    change sLocalThetaOperator F S (C (a • C g.val)) = _
    rw [map_smul, map_smul]
    exact sLocalFourierCompression_double_theta F S g.val
  change EqOn (Z F S μ ω (C f)) G.val {z | 0 < z.re}
  intro z hz
  have hpos : 0 < z.re := hz
  have h₁ := sLocalContinuedZeta_eq_theta F S μ ν hν ω (C f) hpos
  have h₂ := sLocalContinuedZeta_eq_theta F S μ ν hν ω g.val hpos
  calc
    _ = sLocalThetaZetaIntegral F S ν ω (C f) z := h₁
    _ = sLocalThetaZetaIntegral F S ν ω g.val z := by
      unfold sLocalThetaZetaIntegral
      refine integral_congr_ae (.of_forall fun q ↦ ?_)
      exact congrArg (sLocalZetaWeight F S ω z q * ·) (congrFun he q)
    _ = Z F S μ ω g.val z := h₂.symm
    _ = G.val z := hL G hpos

include hν in
theorem exists_sLocalStageFourier_zeta_eq_schwartzBergmanCLM
    (ω : PontryaginDual (K F S)) :
    ∃ L : SchwartzBergman (univ : Set ℝ) →L[ℂ] E F S,
      ∀ G, EqOn (Z F S μ ω (T F S hS (L G))) G.val {z | 0 < z.re} := by
  simp only [T, sLocalStageFourier_eq_compression]
  exact exists_sLocalFourierCompression_zeta_eq_schwartzBergmanCLM F S μ ν hν ω

include hν in
/-- On a stage containing the different, every whole-plane
Schwartz–Bergman function can be realized on the Fourier side. -/
theorem exists_sLocalStageFourier_zeta_eq_schwartzBergman
    (ω : PontryaginDual (K F S)) (G : SchwartzBergman (univ : Set ℝ)) :
    ∃ f : E F S, EqOn (Z F S μ ω (T F S hS f)) G.val {z | 0 < z.re} := by
  obtain ⟨L, hL⟩ := exists_sLocalStageFourier_zeta_eq_schwartzBergmanCLM F S μ ν hν hS ω
  exact ⟨L G, hL G⟩

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem reflected_selectedEuler_order (ω : PontryaginDual (K F S)) (W : Finset S)
    (c : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ sLocalSelectedEulerMultiplier F S ω W (1-z)) c ∧
      analyticOrderAt (fun z : ℂ ↦ sLocalSelectedEulerMultiplier F S ω W (1-z)) c =
        sLocalSelectedFinitePoleCount F S ω W (1-c) := by
  let P := sLocalSelectedEulerMultiplier F S ω W
  let r (z : ℂ) := 1-z
  have ha := (sLocalSelectedEulerMultiplier_analytic_order F S ω W (1-c)).1
  have hr : AnalyticAt ℂ r c := analyticAt_const.sub analyticAt_id
  refine ⟨ha.comp (f := r) (x := c) hr, ?_⟩
  have hd : HasDerivAt r (-1) c := (hasDerivAt_id c).const_sub 1
  have ho := hr.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (hd.deriv ▸ neg_ne_zero.mpr one_ne_zero)
  change analyticOrderAt (P ∘ r) c = _
  rw [ha.analyticOrderAt_comp hr, ho, mul_one]
  exact (sLocalSelectedEulerMultiplier_analytic_order F S ω W (1-c)).2

include hν in
/-- An actual test realizes a single reflected Fourier jet at any
selected finite Euler pole and vanishes in every other selected jet.
The divisor keeps the full selected multiplicities at collisions. -/
theorem exists_sLocalStageFourier_cardinalJet
    (ω : PontryaginDual (K F S)) (W : Finset S) (c : ℂ)
    (k : ℕ) :
    ∃ f : E F S, ∀ w : ℂ, w.re = 0 →
      ∀ j < sLocalSelectedFinitePoleCount F S ω W w,
        iteratedDeriv j (fun z : ℂ ↦ Z F S μ ω⁻¹ (T F S hS f) (1-z)) w =
          if w = c ∧ j = k then 1 else 0 := by
  let m := sLocalSelectedFinitePoleCount F S ω W
  let P (z : ℂ) := sLocalSelectedEulerMultiplier F S ω W (1-z)
  let u := 1-c
  have horder : analyticOrderAt P u = m c := by
    have he := (reflected_selectedEuler_order F S ω W u).2
    change analyticOrderAt P u = m (1 - (1-c)) at he
    rwa [sub_sub_cancel] at he
  have hPa (z : ℂ) : AnalyticAt ℂ P z := (reflected_selectedEuler_order F S ω W z).1
  have hPb (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z.re ∈ Icc a b → ‖P z‖ ≤ C := by
    obtain ⟨C, hC, he⟩ := sLocalSelectedEulerMultiplier_stripBound F S ω W (1-b) (1-a)
    refine ⟨C, hC, fun z hz ↦ he (1-z) ?_⟩
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith [hz.1, hz.2]
  obtain ⟨g, hg, hgB, hgc, hgw⟩ := exists_verticalStrip_cardinalJet P hPa hPb u (m c) k horder
  let a : ℂ := (-1) ^ k
  let G : SchwartzBergman (univ : Set ℝ) :=
    ⟨a • g, (schwartzBergmanSubmodule univ).smul_mem a hgB⟩
  obtain ⟨f, hf⟩ := exists_sLocalStageFourier_zeta_eq_schwartzBergman F S μ ν hν hS ω⁻¹ G
  refine ⟨f, fun w hw j hj ↦ ?_⟩
  have ho : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have he : (fun z : ℂ ↦ Z F S μ ω⁻¹ (T F S hS f) (1-z)) =ᶠ[𝓝 w]
      (fun z : ℂ ↦ a * g (1-z)) := by
    filter_upwards [ho.mem_nhds (by change w.re < 1; simp [hw])] with z hz
    exact hf (by change 0 < (1-z).re; simp only [Complex.sub_re, Complex.one_re, sub_pos]; exact hz)
  rw [he.iteratedDeriv_eq, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_sub]
  change a * ((-1 : ℂ)^j * iteratedDeriv j g (1-w)) = _
  by_cases h : w = c
  · subst w
    rw [hgc j hj]
    by_cases e : j = k
    · subst j
      simp only [true_and, ite_true, mul_one, a, ← mul_pow, neg_mul_neg, one_pow]
    · simp [e]
  · have hn : 1-w ≠ u := fun h' ↦ h (sub_right_inj.mp h')
    have hm : (m w : ℕ∞) ≤ analyticOrderAt g (1-w) := by
      have hP := (reflected_selectedEuler_order F S ω W (1-w)).2
      change analyticOrderAt P (1-w) = m (1-(1-w)) at hP
      rw [sub_sub_cancel] at hP
      exact hP ▸ hgw (1-w) hn
    have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg (1-w))).mp hm j hj
    simp [hz, h]

/-- The finitely many derivative labels in one common period. -/
abbrev SLocalPrimaryEulerJetIndex (ω : PontryaginDual (K F S)) (p : ℕ) (W : Finset S) :=
  Σ x : ↥(sLocalPrimaryEulerCell F S ω p W),
    Fin (sLocalSelectedFinitePoleCount F S ω W ((x.val : ℂ) * Complex.I))

/-- The finite cell times the integers labels the actual center and derivative
pairs, with multiplicities preserved at coincident Euler poles. -/
def sLocalPrimaryEulerJetEquiv (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    SLocalPrimaryEulerJetIndex F S ω p W × ℤ ≃
      Σ c : ℂ, Fin (sLocalSelectedFinitePoleCount F S ω W c) := by
  let J := SLocalPrimaryEulerJetIndex F S ω p W
  let d := sLocalPrimaryEulerPeriod p
  let P := sLocalSelectedFinitePoleCount F S ω W
  let c (i : J × ℤ) : ℂ := (((i.1.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)
  have hc (i : J × ℤ) : P (c i) = P ((i.1.1.val : ℂ) * Complex.I) := by
    have he : c i = (i.1.1.val : ℂ) * Complex.I + (((i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I := by
      dsimp [c]
      push_cast
      ring
    rw [he]
    exact (sLocalPrimaryEulerProduct_periodic F S ω hp hW _ i.2).2
  let e (i : J × ℤ) : Σ z : ℂ, Fin (P z) :=
    ⟨c i, ⟨i.1.2.val, (hc i).symm ▸ i.1.2.isLt⟩⟩
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · rintro ⟨⟨⟨x,hx⟩,k⟩,m⟩ ⟨⟨⟨y,hy⟩,l⟩,n⟩ h
    have h₁ := congrArg (fun j : Σ z : ℂ, Fin (P z) ↦ j.1.im) h
    have h₂ := congrArg (fun j : Σ z : ℂ, Fin (P z) ↦ j.2.val) h
    have he : x + (m : ℝ) * d = y + (n : ℝ) * d := by
      simpa [e, c] using h₁
    obtain ⟨rfl, rfl⟩ := sLocalPrimaryEulerCell_representation_unique F S ω hp hx hy m n he
    have hkl : k = l := Fin.ext h₂
    subst l
    rfl
  · rintro ⟨z,k⟩
    obtain ⟨x,hx,m,hzm,hcount⟩ := sLocalPrimaryEulerCell_represents F S ω hp hW
      ((Nat.zero_le k.val).trans_lt k.isLt)
    let j : J := ⟨⟨x,hx⟩, ⟨k.val, hcount ▸ k.isLt⟩⟩
    refine ⟨(j,m), Sigma.ext hzm.symm ?_⟩
    exact (Fin.heq_ext_iff (congrArg P hzm.symm)).mpr rfl

theorem sLocalPrimaryEulerJetEquiv_apply_values (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p)
    (i : SLocalPrimaryEulerJetIndex F S ω p W × ℤ) :
    let j := sLocalPrimaryEulerJetEquiv F S ω hp hW i
    j.1 = (((i.1.1.val + (i.2 : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I) ∧
      j.2.val = i.1.2.val :=
  ⟨rfl, rfl⟩

/-- A polynomial weight in the common-period index is bounded linearly
by the corresponding weight in each individual Euler lattice index. -/
theorem sLocalPrimaryEulerIndex_weight_le_lattice (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) (W : Finset S) (b e : ℝ)
    (i : SLocalPrimaryEulerJetIndex F S ω p W × ℤ) (n : ℤ)
    (hi : i.1.1.val + (i.2 : ℝ) * sLocalPrimaryEulerPeriod p = b + (n : ℝ) * e) :
    1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p ≤
      (1 + sLocalPrimaryEulerPeriod p + |b| + |e|) * (1 + |(n : ℝ)|) := by
  let d := sLocalPrimaryEulerPeriod p
  have hd : 0 < d := sLocalPrimaryEulerPeriod_pos hp
  have hx : i.1.1.val ∈ Ico 0 d := (Finset.mem_filter.mp i.1.1.property).2.1
  have hb : |(i.2 : ℝ)| * d ≤ |b| + |(n : ℝ)| * |e| + d := by
    calc
      _ = |(i.2 : ℝ) * d| := by rw [abs_mul, abs_of_pos hd]
      _ = |b + (n : ℝ) * e - i.1.1.val| := by
        congr 1
        change i.1.1.val + (i.2 : ℝ) * d = _ at hi
        linarith
      _ ≤ |b + (n : ℝ) * e| + |i.1.1.val| := abs_sub _ _
      _ ≤ |b| + |(n : ℝ)| * |e| + d := by
        rw [abs_of_nonneg hx.1, ← abs_mul]
        exact add_le_add (abs_add_le _ _) hx.2.le
  change 1 + |(i.2 : ℝ)| * d ≤ (1 + d + |b| + |e|) * (1 + |(n : ℝ)|)
  have hn := abs_nonneg (n : ℝ)
  have hne := mul_nonneg (show 0 ≤ 1 + d + |b| by positivity) hn
  nlinarith [abs_nonneg b, abs_nonneg e]

omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The entire primary cardinal functions have one nonzero jet and
polynomial growth in the translation index in every weighted strip norm. -/
theorem exists_sLocalPrimaryEuler_cardinalFamily
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) {W : Finset S}
    (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let J := SLocalPrimaryEulerJetIndex F S ω p W
    let point (i : J) (n : ℤ) :=
      ((i.1.val + (n : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I
    ∃ G : J → ℤ → ℂ → ℂ,
      (∀ i n z, AnalyticAt ℂ (G i n) z) ∧
      (∀ i j n m, iteratedDeriv j.2.val (G i n) (point j m) =
        if i.1.val = j.1.val ∧ i.2.val = j.2.val ∧ n = m then 1 else 0) ∧
      ∀ (a b : ℝ) (N : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i (n : ℤ) z, z.re ∈ Icc a b →
        ‖z‖^N * ‖G i n z‖ ≤ C * (1 + |(n : ℝ)| * sLocalPrimaryEulerPeriod p)^N := by
  let J := SLocalPrimaryEulerJetIndex F S ω p W
  let d := sLocalPrimaryEulerPeriod p
  let P := sLocalSelectedEulerMultiplier F S ω W
  let M := sLocalSelectedFinitePoleCount F S ω W
  let c (i : J) := (i.1.val : ℂ) * Complex.I
  let point (i : J) (n : ℤ) := ((i.1.val + (n : ℝ) * d : ℝ) : ℂ) * Complex.I
  have hP (z : ℂ) := sLocalSelectedEulerMultiplier_analytic_order F S ω W z
  have hEx (i : J) := exists_verticalStrip_cardinalJet P (fun z ↦ (hP z).1)
    (sLocalSelectedEulerMultiplier_stripBound F S ω W) (c i) (M (c i)) i.2.val (hP (c i)).2
  choose g hg hgB hgc hgw using hEx
  let G (i : J) (n : ℤ) (z : ℂ) := g i (z - (((n : ℝ) * d : ℝ) : ℂ) * Complex.I)
  refine ⟨G, ?_, ?_, ?_⟩
  · intro i n z
    let y := (((n : ℝ) * d : ℝ) : ℂ) * Complex.I
    exact (hg i (z-y)).comp (f := fun w : ℂ ↦ w-y) (x := z)
      (analyticAt_id.sub analyticAt_const)
  · intro i j n m
    change iteratedDeriv j.2.val (fun z ↦ g i (z - (((n : ℝ) * d : ℝ) : ℂ) * Complex.I))
       (point j m) = _
    rw [iteratedDeriv_comp_sub_const]
    change iteratedDeriv j.2.val (g i) (point j m - (((n : ℝ) * d : ℝ) : ℂ) * Complex.I) = _
    have he : point j m - (((n : ℝ) * d : ℝ) : ℂ) * Complex.I = point j (m-n) := by
      dsimp only [point]; push_cast; ring
    rw [he]
    have hm : M (point j (m-n)) = M (c j) := by
      have h := (sLocalPrimaryEulerProduct_periodic F S ω hp hW (c j) (m-n)).2
      change M (c j + (((((m-n : ℤ) : ℝ) * d : ℝ) : ℂ) * Complex.I)) = _ at h
      have hp' : c j + (((((m-n : ℤ) : ℝ) * d : ℝ) : ℂ) * Complex.I) = point j (m-n) := by
        dsimp only [c, point]
        push_cast
        ring
      rwa [hp'] at h
    by_cases h : point j (m-n) = c i
    · have he' : j.1.val + ((m-n : ℤ) : ℝ) * d = i.1.val + ((0 : ℤ) : ℝ) * d := by
        have he' := congrArg Complex.im h
        simpa only [point, c, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          mul_one, mul_zero, add_zero, Int.cast_zero, zero_mul] using he'
      obtain ⟨hji, hmn⟩ := sLocalPrimaryEulerCell_representation_unique F S ω hp
        j.1.property i.1.property (m-n) 0 he'
      have hn : n = m := by omega
      have hj : j.2.val < M (c i) := by
        have hp := j.2.isLt
        change j.2.val < M (c j) at hp
        rwa [← hm, h] at hp
      rw [h, hgc i j.2.val hj]
      by_cases hk : i.2.val = j.2.val
      · rw [ite_eq_left hk.symm, ite_eq_left ⟨hji.symm, hk, hn⟩]
      · have hk' := Ne.symm hk
        rw [ite_eq_right hk', ite_eq_right (fun a ↦ hk a.2.1)]
    · have ht : (M (c j) : ℕ∞) ≤ analyticOrderAt (g i) (point j (m-n)) := by
        have ho := (hP (point j (m-n))).2
        change analyticOrderAt P (point j (m-n)) = (M (point j (m-n)) : ℕ∞) at ho
        rw [hm] at ho
        exact ho ▸ hgw i _ h
      rw [(natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg i (point j (m-n)))).mp
        ht _ j.2.isLt]
      have hf : ¬ (i.1.val = j.1.val ∧ i.2.val = j.2.val ∧ n = m) := by
        rintro ⟨hij, _, rfl⟩
        apply h
        simp [point, c, hij]
      rw [ite_eq_right hf]
  · intro a b N
    choose C hC hbound using fun i : J ↦ verticalStrip_heightTranslate_bound (g i) (hgB i) a b N
    let C₀ := ∑ i : J, C i
    have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun i _ ↦ hC i)
    refine ⟨C₀, hC₀, fun i n z hz ↦ ?_⟩
    have h := hbound i ((n : ℝ) * d) z hz
    change ‖z‖^N * ‖G i n z‖ ≤ _
    rw [abs_mul, abs_of_pos (sLocalPrimaryEulerPeriod_pos hp)] at h
    have hnonneg : 0 ≤ (1 + |(n : ℝ)| * sLocalPrimaryEulerPeriod p)^N :=
      pow_nonneg (add_nonneg zero_le_one (mul_nonneg (abs_nonneg _)
        (sLocalPrimaryEulerPeriod_pos hp).le)) _
    exact h.trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ i)) hnonneg)


omit [∀ v : S, MeasurableSpace (v.val.adicCompletion F)ˣ]
  [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- One entire Schwartz–Bergman function interpolates an entire primary
jet array with summable polynomial weights. The series of cardinal
functions converges normally on every interior strip. -/
theorem exists_sLocalPrimaryEuler_interpolate_hasSum
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) {W : Finset S}
    (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let J := SLocalPrimaryEulerJetIndex F S ω p W
    let d := sLocalPrimaryEulerPeriod p
    ∃ B : J × ℤ → SchwartzBergman (univ : Set ℝ),
      (∀ i (j : J) (m : ℤ), iteratedDeriv j.2.val (B i).val
        (((j.1.val + (m : ℝ) * d : ℝ) : ℂ) * Complex.I) = if i = (j,m) then 1 else 0) ∧
      (∀ (q : Seminorm ℂ (SchwartzBergman (univ : Set ℝ))), Continuous q →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (B i) ≤ C * (1 + |(i.2 : ℝ)| * d)^N) ∧
      ∀ a : J × ℤ → ℂ, (∀ N : ℕ, Summable (fun i ↦ ‖a i‖ * (1 + |(i.2 : ℝ)| * d)^N)) →
        ∃ H : SchwartzBergman (univ : Set ℝ), HasSum (fun i ↦ a i • B i) H ∧
          ∀ (j : J) (m : ℤ), iteratedDeriv j.2.val H.val
            (((j.1.val + (m : ℝ) * d : ℝ) : ℂ) * Complex.I) = a (j,m) := by
  let J := SLocalPrimaryEulerJetIndex F S ω p W
  let d := sLocalPrimaryEulerPeriod p
  obtain ⟨G, hGa, hjet, hG⟩ := exists_sLocalPrimaryEuler_cardinalFamily F S ω hp hW
  have hB (i : J × ℤ) : G i.1 i.2 ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
    refine ⟨by simp, (show Differentiable ℂ (G i.1 i.2) from
      fun z ↦ (hGa i.1 i.2 z).differentiableAt).differentiableOn, ?_⟩
    intro l r _ _ N
    obtain ⟨C, _, hb⟩ := hG l r N
    refine ⟨C * (1 + |(i.2 : ℝ)| * d)^N, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa only [norm_mul, norm_pow] using hb i.1 i.2 z hz
  let B : J × ℤ → SchwartzBergman (univ : Set ℝ) := fun i ↦ ⟨G i.1 i.2, hB i⟩
  have hcard (i : J × ℤ) (j : J) (m : ℤ) :
      iteratedDeriv j.2.val (B i).val (((j.1.val + (m : ℝ) * d : ℝ) : ℂ) * Complex.I) =
        if i = (j,m) then 1 else 0 := by
    rcases i with ⟨i,n⟩
    change iteratedDeriv j.2.val (G i n) _ = _
    rw [hjet i j n m]
    have hpair : (i.1.val = j.1.val ∧ i.2.val = j.2.val ∧ n = m) ↔ (i,n) = (j,m) := by
      constructor
      · rintro ⟨h₁, h₂, h₃⟩
        have hij : i = j := by
          rcases i with ⟨x,k⟩
          rcases j with ⟨y,l⟩
          have hxy : x = y := Subtype.ext h₁
          subst y
          have hkl : k = l := Fin.ext h₂
          subst l
          rfl
        exact Prod.ext hij h₃
      · rintro h
        cases h
        exact ⟨rfl, rfl, rfl⟩
    simp only [hpair]
  have hpoly (q : Seminorm ℂ (SchwartzBergman (univ : Set ℝ))) (hq : Continuous q) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (B i) ≤ C * (1 + |(i.2 : ℝ)| * d)^N := by
    have hd : 0 < d := sLocalPrimaryEulerPeriod_pos hp
    refine schwartzBergman_seminorm_polynomial_bound B (fun i ↦ 1 + |(i.2 : ℝ)| * d)
      (fun _ ↦ le_add_of_nonneg_right (by positivity)) ?_ q hq
    intro a k
    obtain ⟨C, hC, hb⟩ := hG a.val a.val k
    refine ⟨C, hC, fun i x ↦ ?_⟩
    let z : ℂ := (a.val : ℂ) + x * Complex.I
    change ‖z ^ k * G i.1 i.2 z‖ ≤ _
    simpa only [norm_mul, norm_pow] using hb i.1 i.2 z (by simp [z])
  refine ⟨B, hcard, hpoly, fun a ha ↦ ?_⟩
  let F₀ (i : J × ℤ) (z : ℂ) := a i * G i.1 i.2 z
  let H (z : ℂ) := ∑' i, F₀ i z
  let u (N : ℕ) (i : J × ℤ) := ‖a i‖ * (1 + |(i.2 : ℝ)| * d)^N
  have hFa (i : J × ℤ) (z : ℂ) : AnalyticAt ℂ (F₀ i) z :=
    analyticAt_const.mul (hGa i.1 i.2 z)
  have hweight (l r : ℝ) (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i z, z.re ∈ Icc l r →
      ‖z ^ N * F₀ i z‖ ≤ C * u N i := by
    obtain ⟨C, hC, hb⟩ := hG l r N
    refine ⟨C, hC, fun i z hz ↦ ?_⟩
    change ‖z ^ N * (a i * G i.1 i.2 z)‖ ≤ C * u N i
    rw [norm_mul, norm_pow, norm_mul, mul_left_comm]
    exact (mul_le_mul_of_nonneg_left (hb i.1 i.2 z hz) (norm_nonneg _)).trans_eq (by
      dsimp only [u, d]
      ring)
  have huniform (l r : ℝ) :
      TendstoLocallyUniformlyOn (fun s : Finset (J × ℤ) ↦ fun z : ℂ ↦ ∑ i ∈ s, F₀ i z)
        H atTop (Complex.re ⁻¹' Ioo l r) := by
    obtain ⟨C, _, hC⟩ := hweight l r 0
    refine (tendstoUniformlyOn_tsum ((ha 0).mul_left C) ?_).tendstoLocallyUniformlyOn
    intro i z hz
    simpa only [u, d, pow_zero, one_mul] using hC i z (Ioo_subset_Icc_self hz)
  have hanSum (s : Finset (J × ℤ)) (z : ℂ) :
      AnalyticAt ℂ (fun w ↦ ∑ i ∈ s, F₀ i w) z :=
    s.analyticAt_fun_sum fun i _ ↦ hFa i z
  have hd (z : ℂ) : DifferentiableAt ℂ H z := by
    let l := z.re - 1
    let r := z.re + 1
    have ho : IsOpen (Complex.re ⁻¹' Ioo l r) := isOpen_Ioo.preimage Complex.continuous_re
    have hz : z ∈ Complex.re ⁻¹' Ioo l r := by change l < z.re ∧ z.re < r; dsimp [l, r]; constructor <;> linarith
    exact ((huniform l r).differentiableOn (.of_forall fun s w _ ↦
      (hanSum s w).differentiableAt.differentiableWithinAt) ho).differentiableAt (ho.mem_nhds hz)
  have hH : H ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
    refine ⟨by simp, (show Differentiable ℂ H from hd).differentiableOn, ?_⟩
    intro l r _ _ N
    obtain ⟨C, hC, hb⟩ := hweight l r N
    refine ⟨∑' i, C * u N i, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hs : Summable (fun i ↦ ‖z ^ N * F₀ i z‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i ↦ hb i z hz) ((ha N).mul_left C)
    change ‖z ^ N * H z‖ ≤ _
    rw [show z ^ N * H z = ∑' i, z ^ N * F₀ i z from tsum_mul_left.symm]
    exact (norm_tsum_le_tsum_norm hs).trans
      (hs.tsum_le_tsum (fun i ↦ hb i z hz) ((ha N).mul_left C))
  refine ⟨⟨H, hH⟩, ?_, ?_⟩
  · apply schwartzBergman_tendsto_of_weightedTrace
    intro x N ε hε
    obtain ⟨C, _, hb⟩ := hweight x x N
    have hu := tendstoUniformlyOn_tsum (f := fun i z ↦ z ^ N * F₀ i z)
      ((ha N).mul_left C) (fun i z hz ↦ hb i z hz)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε] with s hs
    intro y
    let z : ℂ := (x.val : ℂ) + y * Complex.I
    have hz : z.re ∈ Icc x.val x.val := by simp [z]
    have he := (hs z hz).le
    rw [dist_eq_norm, ← Finset.mul_sum, tsum_mul_left] at he
    change ‖z ^ N * (((∑ i ∈ s, a i • B i : SchwartzBergman (univ : Set ℝ))).val z - H z)‖ ≤ ε
    rw [mul_sub]
    have hsum : (∑ i ∈ s, a i • B i : SchwartzBergman (univ : Set ℝ)).val z =
        ∑ i ∈ s, F₀ i z := by
      change (∑ i ∈ s, a i • (⟨G i.1 i.2, hB i⟩ :
        schwartzBergmanSubmodule (univ : Set ℝ))).val z = _
      simp only [Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [hsum]
    exact (norm_sub_rev _ _).trans_le he
  · intro j m
    let z := ((j.1.val + (m : ℝ) * d : ℝ) : ℂ) * Complex.I
    let V := Complex.re ⁻¹' Ioo (-1 : ℝ) 1
    have hV : IsOpen V := isOpen_Ioo.preimage Complex.continuous_re
    have hz : z ∈ V := by
      change z.re ∈ Ioo (-1 : ℝ) 1
      have hr : z.re = 0 := by
        dsimp only [z]
        simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      rw [hr]
      exact ⟨by norm_num, zero_lt_one⟩
    have hlim (k : ℕ) : TendstoLocallyUniformlyOn
        (fun s : Finset (J × ℤ) ↦ iteratedDeriv k (fun w ↦ ∑ i ∈ s, F₀ i w))
        (iteratedDeriv k H) atTop V := by
      induction k with
      | zero => simpa only [iteratedDeriv_zero] using huniform (-1) 1
      | succ k ih =>
        simp only [iteratedDeriv_succ]
        refine ih.deriv (.of_forall fun s w _ ↦ ?_) hV
        simpa only [iteratedDeriv_eq_iterate] using
          ((hanSum s w).iterated_deriv k).differentiableAt.differentiableWithinAt
    have ht := (hlim j.2.val).tendsto_at hz
    have hstep : (fun s : Finset (J × ℤ) ↦
        iteratedDeriv j.2.val (fun w ↦ ∑ i ∈ s, F₀ i w) z) =ᶠ[atTop] fun _ ↦ a (j,m) := by
      filter_upwards [eventually_ge_atTop ({(j,m)} : Finset (J × ℤ))] with s hs
      have hmem : (j,m) ∈ s := hs (Finset.mem_singleton_self _)
      have hsummand (i : J × ℤ) : iteratedDeriv j.2.val (F₀ i) z =
          a i * (if i = (j,m) then 1 else 0) := by
        change iteratedDeriv j.2.val (fun w ↦ a i * (B i).val w) z = _
        rw [iteratedDeriv_const_mul_field, hcard i j m]
      rw [iteratedDeriv_fun_sum (fun i _ ↦ (hFa i z).contDiffAt)]
      simp_rw [hsummand]
      rw [Finset.sum_eq_single_of_mem (j,m) hmem]
      · simp
      · intro i _ hi
        simp [hi]
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hstep.symm)

omit [∀ v : S, BorelSpace (v.val.adicCompletion F)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem exists_sLocalPrimaryEuler_interpolate_summable
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) {W : Finset S}
    (hW : W ⊆ sLocalPrimaryPlaces F S p)
    (a : SLocalPrimaryEulerJetIndex F S ω p W × ℤ → ℂ)
    (ha : ∀ N : ℕ, Summable (fun i ↦ ‖a i‖ *
      (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N)) :
    ∃ H : ℂ → ℂ, H ∈ schwartzBergmanSubmodule (univ : Set ℝ) ∧
      ∀ (j : SLocalPrimaryEulerJetIndex F S ω p W) (m : ℤ),
        iteratedDeriv j.2.val H
          (((j.1.val + (m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I) = a (j,m) := by
  obtain ⟨_, _, _, hsum⟩ := exists_sLocalPrimaryEuler_interpolate_hasSum F S ω hp hW
  obtain ⟨H, _, hH⟩ := hsum a ha
  exact ⟨H.val, H.property, hH⟩

private def schwartzBergmanReflectOneCLM :
    SchwartzBergman (univ : Set ℝ) →L[ℂ] SchwartzBergman (univ : Set ℝ) := by
  let E := SchwartzBergman (univ : Set ℝ)
  let R : E →ₗ[ℂ] E :=
    { toFun := fun G ↦ ⟨fun z ↦ G.val (1-z), schwartzBergmanSubmodule_reflect_one G.val G.property⟩
      map_add' := fun G H ↦ Subtype.ext (funext fun z ↦ rfl)
      map_smul' := fun c G ↦ Subtype.ext (funext fun z ↦ rfl) }
  have hcont : Continuous R := by
    obtain ⟨T, hT, hEmb⟩ :=
      schwartzBergman_schwartzLine_topology univ isOpen_univ ordConnected_univ univ_nonempty
    have hEval (z : ℂ) : Continuous (fun G : E ↦ G.val z) := by
      let a : (univ : Set ℝ) := ⟨z.re, mem_univ _⟩
      have hSchwartz : Continuous (fun g : 𝓢(ℝ, ℂ) ↦ g z.im) :=
        (BoundedContinuousFunction.lipschitz_eval_const z.im).continuous.comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous
      refine (hSchwartz.comp ((continuous_apply a).comp hEmb.continuous)).congr fun G ↦ ?_
      change T G a z.im = G.val z
      rw [hT]
      simp only [weightedVerticalTrace, pow_zero, one_mul]
      rw [show (a.val : ℂ) + z.im * Complex.I = z from Complex.re_add_im z]
    have hgraph : IsClosed (R.graph : Set (E × E)) := by
      rw [show (R.graph : Set (E × E)) =
        ⋂ z : ℂ, {q : E × E | q.2.val z = q.1.val (1-z)} from by
          ext q
          change q ∈ R.graph ↔ _
          rw [R.mem_graph_iff, mem_iInter]
          exact ⟨fun h z ↦ congrArg (fun G : E ↦ G.val z) h,
            fun h ↦ Subtype.ext (funext h)⟩]
      exact isClosed_iInter fun z ↦
        isClosed_eq ((hEval z).comp continuous_snd) ((hEval (1-z)).comp continuous_fst)
    obtain ⟨_, hNorm, hMetric, hComplete⟩ :=
      schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty
    letI : TopologicalSpace.MetrizableSpace E := hMetric
    letI : PolynormableSpace ℂ E := hNorm
    letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
    letI : CompleteSpace E := hComplete
    letI : T2Space E := hEmb.t2Space
    exact frechet_continuous_of_closed_graph R hgraph
  exact ⟨R, hcont⟩

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem compressedFourierLift_iteratedDeriv (ω : PontryaginDual (K F S))
    (L : SchwartzBergman (univ : Set ℝ) →L[ℂ] E F S)
    (hL : ∀ G, EqOn (Z F S μ ω (sLocalFourierCompression F S (L G))) G.val {z | 0 < z.re})
    (G : SchwartzBergman (univ : Set ℝ)) (c : ℂ) (hc : c.re = 0) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ ↦
      Z F S μ ω (sLocalFourierCompression F S (L (schwartzBergmanReflectOneCLM G))) (1-z)) c =
      iteratedDeriv k G.val c := by
  have ho : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have he : (fun z : ℂ ↦ Z F S μ ω (sLocalFourierCompression F S (L (schwartzBergmanReflectOneCLM G))) (1-z))
      =ᶠ[𝓝 c] G.val := by
    filter_upwards [ho.mem_nhds (by change c.re < 1; simp [hc])] with z hz
    have hpos : 0 < (1-z).re := by
      simp only [Complex.sub_re, Complex.one_re, sub_pos]
      exact hz
    have he := hL (schwartzBergmanReflectOneCLM G) hpos
    change Z F S μ ω (sLocalFourierCompression F S (L (schwartzBergmanReflectOneCLM G))) (1-z) =
      G.val (1-(1-z)) at he
    rwa [sub_sub_cancel] at he
  exact he.iteratedDeriv_eq k


include hν in
/-- Primary Fourier cardinal tests give an unconditionally convergent expansion
for each array summable with every polynomial weight. Convergence holds already
in the S-local test space and therefore in the principal-value quotient. -/
theorem exists_sLocalFourierCompression_hasSum_primary
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) {W : Finset S}
    (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let J := SLocalPrimaryEulerJetIndex F S ω p W
    let M := sLocalHomogeneousThetaKernel F S ν ω
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let Q := R.mkQL.comp M.mkQL
    let jet (f : E F S) (j : J) (m : ℤ) :=
      iteratedDeriv j.2.val (fun z : ℂ ↦ Z F S μ ω⁻¹ (sLocalFourierCompression F S f) (1-z))
        (((j.1.val + (m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)
    ∃ b : J × ℤ → E F S,
      (∀ i j m, jet (b i) j m = if i = (j,m) then 1 else 0) ∧
      (∀ (q : Seminorm ℂ ((SLocalHomogeneousThetaQuotient F S ν ω) ⧸ R)), Continuous q →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (Q (b i)) ≤
          C * (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N) ∧
      (∀ (q : Seminorm ℂ (E F S)), Continuous q →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (b i) ≤
          C * (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N) ∧
      ∀ a : J × ℤ → ℂ, (∀ N : ℕ, Summable (fun i ↦ ‖a i‖ *
          (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N)) →
        ∃ f : E F S,
          HasSum (fun i ↦ a i • b i) f ∧
          HasSum (fun i ↦ a i • Q (b i)) (Q f) ∧
          ∀ j m, jet f j m = a (j,m) := by
  dsimp only
  obtain ⟨B, hB, hpoly, htotal⟩ := exists_sLocalPrimaryEuler_interpolate_hasSum F S ω hp hW
  obtain ⟨L, hL⟩ := exists_sLocalFourierCompression_zeta_eq_schwartzBergmanCLM F S μ ν hν ω⁻¹
  let A := L.comp schwartzBergmanReflectOneCLM
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let Q := R.mkQL.comp M.mkQL
  refine ⟨fun i ↦ A (B i), fun i j m ↦ ?_, fun q hq ↦ ?_, fun q hq ↦ ?_, fun a ha ↦ ?_⟩
  · let c := (((j.1.val + (m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)
    have hc : c.re = 0 := by simp [c, Complex.mul_re]
    exact (compressedFourierLift_iteratedDeriv F S μ ω⁻¹ L hL (B i) c hc j.2.val).trans
      (hB i j m)
  · exact hpoly (q.comp (Q.comp A).toLinearMap) (hq.comp (Q.comp A).continuous)
  · exact hpoly (q.comp A.toLinearMap) (hq.comp A.continuous)
  · obtain ⟨H, hsum, hH⟩ := htotal a ha
    have hs : HasSum (fun i ↦ a i • A (B i)) (A H) := by
      simpa only [map_smul] using A.hasSum hsum
    refine ⟨A H, hs, ?_, fun j m ↦ ?_⟩
    · simpa only [map_smul] using Q.hasSum hs
    · let c := (((j.1.val + (m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)
      have hc : c.re = 0 := by simp [c, Complex.mul_re]
      exact (compressedFourierLift_iteratedDeriv F S μ ω⁻¹ L hL H c hc j.2.val).trans (hH j m)

include hν in
theorem exists_sLocalFourierCompression_interpolate_primary
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) {W : Finset S}
    (hW : W ⊆ sLocalPrimaryPlaces F S p)
    (a : SLocalPrimaryEulerJetIndex F S ω p W × ℤ → ℂ)
    (ha : ∀ N : ℕ, Summable (fun i ↦ ‖a i‖ *
      (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N)) :
    ∃ f : E F S, ∀ (j : SLocalPrimaryEulerJetIndex F S ω p W) (m : ℤ),
      iteratedDeriv j.2.val (fun z : ℂ ↦ Z F S μ ω⁻¹ (sLocalFourierCompression F S f) (1-z))
        (((j.1.val + (m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I) =
          a (j,m) := by
  obtain ⟨_, _, _, _, hsum⟩ := exists_sLocalFourierCompression_hasSum_primary F S μ ν hν ω hp hW
  obtain ⟨f, _, _, hf⟩ := hsum a ha
  exact ⟨f, hf⟩

include hν in
/-- The primary Fourier jets of an actual test satisfy all the absolute
summability hypotheses of the primary interpolation series. -/
theorem sLocalFourierCompression_primaryJets_summable
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) (W : Finset S) (f : E F S)
    (N : ℕ) :
    let J := SLocalPrimaryEulerJetIndex F S ω p W
    let d := sLocalPrimaryEulerPeriod p
    Summable (fun i : J × ℤ ↦
      ‖iteratedDeriv i.1.2.val (fun z : ℂ ↦ Z F S μ ω⁻¹ (sLocalFourierCompression F S f) (1-z))
        (((i.1.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)‖ * (1 + |(i.2 : ℝ)| * d)^N) := by
  let J := SLocalPrimaryEulerJetIndex F S ω p W
  let d := sLocalPrimaryEulerPeriod p
  have hd : 0 < d := sLocalPrimaryEulerPeriod_pos hp
  let h (i : J × ℤ) := ‖iteratedDeriv i.1.2.val
    (fun z : ℂ ↦ Z F S μ ω⁻¹ (sLocalFourierCompression F S f) (1-z))
      (((i.1.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)‖
  change Summable (fun i : J × ℤ ↦ h i * (1 + |(i.2 : ℝ)| * d)^N)
  apply (summable_prod_of_nonneg (fun _ ↦ by dsimp [h]; positivity)).mpr
  refine ⟨fun j ↦ ?_, Summable.of_finite⟩
  obtain ⟨C, hC, hb⟩ := sLocalOrbitalFourierJets_rapid F S μ ν hν ω⁻¹ f
    j.1.val d hd.ne' (N+2) j.2.val
  have hb' (m : ℤ) : |(m : ℝ)|^(N+2) * h (j,m) ≤ C := by
    simpa only [h] using hb m
  let D := (1 + d)^N
  let u (m : ℤ) := D * C * (1 / |(m : ℝ)| ^ (2 : ℕ))
  let v (m : ℤ) := if m = 0 then h (j,0) else 0
  have hu : Summable u := by
    apply Summable.mul_left
    simpa only [add_zero, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using
      (Real.summable_one_div_int_add_rpow 0 2).mpr (by norm_num)
  have hv : Summable v := by
    apply summable_of_ne_finset_zero (s := ({0} : Finset ℤ))
    intro m hm
    have hm' : m ≠ 0 := fun he ↦ hm (he ▸ Finset.mem_singleton_self _)
    simp [v, hm']
  refine (hu.add hv).of_nonneg_of_le (fun _ ↦ by dsimp [h]; positivity) (fun m ↦ ?_)
  by_cases hm : m = 0
  · subst m
    simp [u, v]
  · have h₁ : 1 ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    have h₂ : 0 < |(m : ℝ)| := zero_lt_one.trans_le h₁
    have hw : 1 + |(m : ℝ)| * d ≤ (1 + d) * |(m : ℝ)| := by
      rw [add_mul, one_mul, mul_comm d]
      exact add_le_add_left h₁ _
    have he : 0 ≤ h (j,m) := norm_nonneg _
    change h (j,m) * (1 + |(m : ℝ)| * d)^N ≤ u m + v m
    rw [show v m = 0 by simp [v, hm], add_zero]
    dsimp only [u]
    rw [mul_one_div, le_div_iff₀ (pow_pos h₂ _)]
    calc
      _ ≤ (h (j,m) * ((1 + d) * |(m : ℝ)|)^N) * |(m : ℝ)|^2 := by gcongr
      _ = D * (|(m : ℝ)|^(N+2) * h (j,m)) := by dsimp [D]; rw [mul_pow, pow_add]; ring
      _ ≤ D * C := mul_le_mul_of_nonneg_left (hb' m) (by dsimp [D]; positivity)

include hν in
/-- The actual pole-derivative labels can be enumerated by the naturals.
When there are no labels the primary principal-value quotient is zero. -/
theorem sLocalPrimaryQuotient_index_enumerable_or_empty
    (ω : PontryaginDual (K F S))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let M := sLocalHomogeneousThetaKernel F S ν ω
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let I := Σ c : ℂ, Fin (sLocalSelectedFinitePoleCount F S ω W c)
    Nonempty (ℕ ≃ I) ∨ (IsEmpty I ∧ Subsingleton ((SLocalHomogeneousThetaQuotient F S ν ω) ⧸ R)) := by
  let M := sLocalHomogeneousThetaKernel F S ν ω
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let X := (SLocalHomogeneousThetaQuotient F S ν ω) ⧸ R
  let J := SLocalPrimaryEulerJetIndex F S ω p W
  let I := Σ c : ℂ, Fin (sLocalSelectedFinitePoleCount F S ω W c)
  let e : J × ℤ ≃ I := sLocalPrimaryEulerJetEquiv F S ω hp hW
  change Nonempty (ℕ ≃ I) ∨ (IsEmpty I ∧ Subsingleton X)
  rcases isEmpty_or_nonempty J with hJ | hJ
  · right
    letI : IsEmpty J := hJ
    have hI : IsEmpty I := Function.isEmpty e.symm
    refine ⟨hI, ⟨fun x y ↦ ?_⟩⟩
    have hz (z : X) : z = 0 := by
      let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
      obtain ⟨f, rfl⟩ := (show Surjective Q from R.mkQ_surjective.comp M.mkQ_surjective) z
      change R.mkQ (M.mkQ f) = 0
      apply (Submodule.Quotient.mk_eq_zero R).mpr
      apply (sLocal_mk_mem_selected_finiteImage_iff_removed_coefficients F S μ ν hν ω W f).mpr
      intro c hc
      exact isEmptyElim (⟨c, ⟨0,hc⟩⟩ : I)
    exact (hz x).trans (hz y).symm
  · left
    obtain ⟨j⟩ := hJ
    obtain ⟨u, hu₁⟩ := Countable.exists_injective_nat (α := J × ℤ)
    let a : ℕ ↪ J × ℤ := ⟨fun n ↦ (j, (n : ℤ)), fun _ _ h ↦ Int.ofNat_inj.mp (congrArg Prod.snd h)⟩
    obtain ⟨b⟩ := a.antisymm ⟨u,hu₁⟩
    exact ⟨b.trans e⟩

include hν in
theorem exists_sLocalStageFourier_hasSum_primary
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) {W : Finset S}
    (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let J := SLocalPrimaryEulerJetIndex F S ω p W
    let M := sLocalHomogeneousThetaKernel F S ν ω
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let Q := R.mkQL.comp M.mkQL
    let jet (f : E F S) (j : J) (m : ℤ) :=
      iteratedDeriv j.2.val (fun z : ℂ ↦ Z F S μ ω⁻¹ (T F S hS f) (1-z))
        (((j.1.val + (m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)
    ∃ b : J × ℤ → E F S,
      (∀ i j m, jet (b i) j m = if i = (j,m) then 1 else 0) ∧
      (∀ (q : Seminorm ℂ ((SLocalHomogeneousThetaQuotient F S ν ω) ⧸ R)), Continuous q →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (Q (b i)) ≤
          C * (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N) ∧
      ∀ a : J × ℤ → ℂ, (∀ N : ℕ, Summable (fun i ↦ ‖a i‖ *
          (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N)) →
        ∃ f : E F S,
          HasSum (fun i ↦ a i • b i) f ∧
          HasSum (fun i ↦ a i • Q (b i)) (Q f) ∧
          ∀ j m, jet f j m = a (j,m) := by
  simp only [T, sLocalStageFourier_eq_compression]
  obtain ⟨b, hc, hq, _, hs⟩ := exists_sLocalFourierCompression_hasSum_primary F S μ ν hν ω hp hW
  exact ⟨b, hc, hq, hs⟩

include hν in
theorem exists_sLocalStageFourier_interpolate_primary
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) {W : Finset S}
    (hW : W ⊆ sLocalPrimaryPlaces F S p)
    (a : SLocalPrimaryEulerJetIndex F S ω p W × ℤ → ℂ)
    (ha : ∀ N : ℕ, Summable (fun i ↦ ‖a i‖ *
      (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N)) :
    ∃ f : E F S, ∀ (j : SLocalPrimaryEulerJetIndex F S ω p W) (m : ℤ),
      iteratedDeriv j.2.val (fun z : ℂ ↦ Z F S μ ω⁻¹ (T F S hS f) (1-z))
        (((j.1.val + (m : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I) =
          a (j,m) := by
  simp only [T, sLocalStageFourier_eq_compression]
  exact exists_sLocalFourierCompression_interpolate_primary F S μ ν hν ω hp hW a ha

include hν in
theorem sLocalStageFourier_primaryJets_summable
    (ω : PontryaginDual (K F S)) {p : ℕ} (hp : p.Prime) (W : Finset S) (f : E F S)
    (N : ℕ) :
    let J := SLocalPrimaryEulerJetIndex F S ω p W
    let d := sLocalPrimaryEulerPeriod p
    Summable (fun i : J × ℤ ↦
      ‖iteratedDeriv i.1.2.val (fun z : ℂ ↦ Z F S μ ω⁻¹ (T F S hS f) (1-z))
        (((i.1.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)‖ * (1 + |(i.2 : ℝ)| * d)^N) := by
  simp only [T, sLocalStageFourier_eq_compression]
  exact sLocalFourierCompression_primaryJets_summable F S μ ν hν ω hp W f N

/-- If the block meets every idele class, every local norm-one character
comes from a global norm-one character unramified at the omitted places. -/
theorem exists_unramified_globalNormOne_for_local (θ : PontryaginDual (K F S))
    (hs : Surjective (sIdeleClassInclusion F S)) :
    ∃ ω : PontryaginDual (normOneIdeleClass F),
      ∃ hu : globalNormOneCharacter F ω ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F))),
      sLocalNormOneCharacterOfGlobal F ω S hs hu = θ := by
  let d : QuasiCharacter (SIdeleQuotient F S) :=
    ⟨(Units.coeHom ℂ).comp (sLocalNormOnePhase F S θ).toMonoidHom,
      Units.continuous_val.comp (sLocalNormOnePhase F S θ).continuous⟩
  obtain ⟨χ, hχ⟩ := sCharacterRestriction_surjective F S d
  let ω : PontryaginDual (normOneIdeleClass F) := θ.comp (globalNormOneToSLocal F S hs)
  have hval (k : normOneIdeleClass F) : χ.val k.val = (ω k : ℂ) := by
    obtain ⟨b, hb⟩ := hs k.val
    have he := sCharacterRestriction_block F S χ b
    rw [hχ, hb, ← globalNormOneToSLocal_val_of_block F S hs k b hb] at he
    exact he.symm.trans (sLocalNormOnePhase_normOne F S θ _)
  have hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))) := by
    apply (mem_sUnramified_iff F S _).mpr
    intro v hv u
    let a := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
    have ha : ‖a.val‖ = 1 := by
      apply (finiteCompletion_norm_eq_one_iff F v a).mpr
      apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      exact ⟨u.val.property, u.inv.property⟩
    let k : normOneIdeleClass F :=
      ⟨ideleClassMap F (singleFiniteIdele F v a), by
        change ideleClassNorm F (ideleClassMap F (singleFiniteIdele F v a)) = 1
        rw [ideleClassNorm_mk, singleFiniteIdele_norm, ha]⟩
    change globalNormOneCharacter F ω k.val = 1
    exact (globalNormOneCharacter_apply F ω k).trans
      ((hval k).symm.trans ((mem_sUnramified_iff F S χ.val).mp χ.property v hv u))
  refine ⟨ω, hu, DFunLike.ext _ _ fun k ↦ ?_⟩
  obtain ⟨b, rfl⟩ := globalNormOneToSLocal_surjective F S hs k
  exact sLocalNormOneCharacterOfGlobal_match F ω S hs hu b

section GlobalPrimary

local instance : MeasurableSpace (Idele F) := borel _
local instance : BorelSpace (Idele F) := ⟨rfl⟩
local instance : MeasurableSpace (normOneIdeleClass F) := borel _
local instance : BorelSpace (normOneIdeleClass F) := ⟨rfl⟩
local instance : MeasurableSpace (IdeleClass F) := borel _
local instance : BorelSpace (IdeleClass F) := ⟨rfl⟩

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μG : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)ˣ)
  [∀ v : HeightOneSpectrum (𝓞 F), (μG v).IsHaarMeasure]
  [∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (μG v)]

variable (η : Measure (Idele F)) [η.IsHaarMeasure]
  (νG : Measure (normOneIdeleClass F)) [νG.IsHaarMeasure]
  (hνG : IsWeilQuotientMeasure (principalIdeles F) η Measure.count (globalClassMeasure F νG))
  (hνS : IsWeilQuotientMeasure (sUnitImage F S)
    (sLocalZetaProductMeasure F S (fun v ↦ μG v.val) (archimedeanMultiplicativeHaar F))
    Measure.count (sLocalClassHaar F S ν))

include hνG hνS in
/-- For a global unramified character restricted to a stage meeting every idele
class, the primary Fourier cardinal series recovers each principal-value class. -/
theorem exists_sLocalPrimaryQuotient_compressedFourier_hasSum
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let J := SLocalPrimaryEulerJetIndex F S A p W
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let Q := R.mkQL.comp M.mkQL
    let jet (f : E F S) (i : J × ℤ) :=
      iteratedDeriv i.1.2.val (fun z : ℂ ↦ Z F S (fun v ↦ μG v.val) A⁻¹ (sLocalFourierCompression F S f) (1-z))
        (((i.1.1.val + (i.2 : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)
    ∃ b : J × ℤ → E F S,
      (∀ i j, jet (b i) j = if i = j then 1 else 0) ∧
      (∀ (q : Seminorm ℂ ((SLocalHomogeneousThetaQuotient F S ν A) ⧸ R)), Continuous q →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (Q (b i)) ≤
          C * (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N) ∧
      ∀ f : E F S, HasSum (fun i ↦ jet f i • Q (b i)) (Q f) ∧
        ∀ (q : Seminorm ℂ ((SLocalHomogeneousThetaQuotient F S ν A) ⧸ R)), Continuous q →
          Summable (fun i ↦ q (jet f i • Q (b i))) := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let J := SLocalPrimaryEulerJetIndex F S A p W
  let M := sLocalHomogeneousThetaKernel F S ν A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let Q := R.mkQL.comp M.mkQL
  let jet (f : E F S) (i : J × ℤ) :=
    iteratedDeriv i.1.2.val (fun z : ℂ ↦ Z F S (fun v ↦ μG v.val) A⁻¹ (sLocalFourierCompression F S f) (1-z))
      (((i.1.1.val + (i.2 : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)
  change ∃ b : J × ℤ → E F S, (∀ i j, jet (b i) j = if i = j then 1 else 0) ∧ _ ∧
    ∀ f : E F S, HasSum (fun i ↦ jet f i • Q (b i)) (Q f) ∧ _
  obtain ⟨b, hcard, hpoly, _, hsum⟩ := exists_sLocalFourierCompression_hasSum_primary
    F S (fun v ↦ μG v.val) ν hνS A hp hW
  refine ⟨b, fun i j ↦ hcard i j.1 j.2, hpoly, fun f ↦ ?_⟩
  have hrapid (N : ℕ) := sLocalFourierCompression_primaryJets_summable
    F S (fun v ↦ μG v.val) ν hνS A hp W f N
  have habs (q : Seminorm ℂ ((SLocalHomogeneousThetaQuotient F S ν A) ⧸ R))
      (hq : Continuous q) : Summable (fun i ↦ q (jet f i • Q (b i))) := by
    obtain ⟨C, _, N, hC⟩ := hpoly q hq
    refine ((hrapid N).mul_left C).of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) fun i ↦ ?_
    rw [map_smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left (hC i) (norm_nonneg _)).trans_eq (by
      change _ = C * (‖jet f i‖ * _)
      rw [mul_left_comm])
  refine ⟨?_, habs⟩
  obtain ⟨g, _, hq, hg⟩ := hsum (jet f) hrapid
  suffices he : Q g = Q f by
    rw [← he]
    exact hq
  change R.mkQ (M.mkQ g) = R.mkQ (M.mkQ f)
  apply (Submodule.Quotient.eq R).mpr
  rw [← map_sub]
  apply (sLocalOrbitalCompressedJets_ker_eq_principalValue_range
    F S μG η νG hνG ω hs hu ν hνS W (g-f)).mpr
  intro c k hk
  obtain ⟨x, hx, m, hc, hcount⟩ := sLocalPrimaryEulerCell_represents F S A hp hW
    ((Nat.zero_le k).trans_lt hk)
  let j : J := ⟨⟨x,hx⟩, ⟨k,hcount ▸ hk⟩⟩
  obtain ⟨D, hD⟩ := exists_sLocalOrbitalCompressedJet_on_quotient
    F S μG η νG hνG ω hs hu ν hνS W c k hk
  have hvalue (t : E F S) : D (Q t) = jet t (j,m) := by
    dsimp only [jet, j]
    rw [← hc]
    exact hD t
  rw [← hD (g-f)]
  change D (Q (g-f)) = 0
  rw [map_sub, map_sub, hvalue, hvalue]
  exact sub_eq_zero.mpr (hg j m)

include hνG hνS in
/-- On the primary quotient, Fourier jets and their cardinal vectors are
biorthogonal, with absolute expansions in the primal space and unconditional
expansions in the strong dual. -/
theorem exists_sLocalPrimaryQuotient_compressedFourier_bases
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let J := SLocalPrimaryEulerJetIndex F S A p W
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
    ∃ (x : J × ℤ → X) (D : J × ℤ → StrongDual ℂ X),
      (∀ i f, D i (Q f) =
        iteratedDeriv i.1.2.val (fun z : ℂ ↦ Z F S (fun v ↦ μG v.val) A⁻¹ (sLocalFourierCompression F S f) (1-z))
          (((i.1.1.val + (i.2 : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)) ∧
      (∀ i j, D i (x j) = if i = j then 1 else 0) ∧
      (∀ y : X, HasSum (fun i ↦ D i y • x i) y) ∧
      (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
        ∀ y : X, Summable (fun i ↦ q (D i y • x i)) ∧ (∑' i, q (D i y • x i)) ≤ r y) ∧
      (∀ (q : Seminorm ℂ X), Continuous q → ∀ b e : ℝ,
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (i : J × ℤ) (n : ℤ),
          i.1.1.val + (i.2 : ℝ) * sLocalPrimaryEulerPeriod p = b + (n : ℝ) * e →
          q (x i) ≤ C * (1 + |(n : ℝ)|)^N) ∧
      ∀ g : StrongDual ℂ X, HasSum (fun i ↦ g (x i) • D i) g := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let J := SLocalPrimaryEulerJetIndex F S A p W
  let M := sLocalHomogeneousThetaKernel F S ν A
  let Y := SLocalHomogeneousThetaQuotient F S ν A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let X := Y ⧸ R
  let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
  let d := sLocalPrimaryEulerPeriod p
  let c (i : J × ℤ) : ℂ := (((i.1.1.val + (i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I)
  let jet (f : E F S) (i : J × ℤ) :=
    iteratedDeriv i.1.2.val
      (fun z : ℂ ↦ Z F S (fun v ↦ μG v.val) A⁻¹ (sLocalFourierCompression F S f) (1-z)) (c i)
  let w (i : J × ℤ) := 1 + |(i.2 : ℝ)| * d
  have hd : 0 < d := sLocalPrimaryEulerPeriod_pos hp
  have hw (i : J × ℤ) : 1 ≤ w i := le_add_of_nonneg_right (by positivity)
  have hD (i : J × ℤ) : ∃ D : StrongDual ℂ X, ∀ f, D (Q f) = jet f i := by
    have hc := (sLocalPrimaryEulerProduct_periodic F S A hp hW
      ((i.1.1.val : ℂ) * Complex.I) i.2).2
    have hc' : c i = (i.1.1.val : ℂ) * Complex.I + (((i.2 : ℝ) * d : ℝ) : ℂ) * Complex.I := by
      dsimp [c]
      push_cast
      ring
    have hk : i.1.2.val < sLocalSelectedFinitePoleCount F S A W (c i) := by
      rw [hc', hc]
      exact i.1.2.isLt
    exact exists_sLocalOrbitalCompressedJet_on_quotient F S μG η νG hνG ω hs hu ν hνS W (c i) _ hk
  choose D hD using hD
  obtain ⟨b, hcard, hpoly, hsum⟩ :=
    exists_sLocalPrimaryQuotient_compressedFourier_hasSum F S (μG := μG) (η := η)
      (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  let x : J × ℤ → X := fun i ↦ Q (b i)
  have hQ : Surjective Q := R.mkQ_surjective.comp M.mkQ_surjective
  have hsumQ (y : X) : HasSum (fun i ↦ D i y • x i) y := by
    obtain ⟨f, rfl⟩ := hQ y
    simpa only [x, hD] using (hsum f).1
  have hcoef (n : ℕ) (y : X) : Summable (fun i ↦ w i ^ n * ‖D i y‖) := by
    obtain ⟨f, rfl⟩ := hQ y
    refine (sLocalFourierCompression_primaryJets_summable
      F S (fun v ↦ μG v.val) ν hνS A hp W f n).congr fun i ↦ ?_
    rw [hD]
    exact mul_comm _ _
  letI : PolynormableSpace ℂ (E F S) := (sLocalBruhat_nuclear F S).2.1
  letI : PolynormableSpace ℂ Y := polynormableSpace_complex_quotient M
  letI : PolynormableSpace ℂ X := polynormableSpace_complex_quotient R
  letI : BarrelledSpace ℂ Y := (sLocalHomogeneousTheta_barrelled F S ν A).1
  letI : BarrelledSpace ℂ X := quotient_barrelled R
  have hgrowth (q : Seminorm ℂ X) (hq : Continuous q) (b e : ℝ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (i : J × ℤ) (n : ℤ),
        i.1.1.val + (i.2 : ℝ) * d = b + (n : ℝ) * e →
        q (x i) ≤ C * (1 + |(n : ℝ)|)^N := by
    obtain ⟨C, hC, N, hbound⟩ := hpoly q hq
    let M₀ := 1 + d + |b| + |e|
    have h₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
    refine ⟨C * M₀^N, mul_nonneg hC (pow_nonneg h₀ _), N, fun i n hi ↦ ?_⟩
    have hw' : w i ≤ M₀ * (1 + |(n : ℝ)|) :=
      sLocalPrimaryEulerIndex_weight_le_lattice F S A hp W b e i n hi
    calc
      q (x i) ≤ C * (w i)^N := hbound i
      _ ≤ C * (M₀ * (1 + |(n : ℝ)|))^N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (hw i)) hw' _) hC
      _ = _ := by rw [mul_pow, mul_assoc]
  refine ⟨x, D, hD, fun i j ↦ (hD i _).trans (by simpa only [eq_comm] using hcard j i),
    hsumQ, ?_, hgrowth, strongDual_hasSum_of_weighted_coefficients x D w hw
      (summable_primary_inverseSquare hd) hsumQ hcoef hpoly⟩
  intro q hq
  obtain ⟨C, hC, n, hb⟩ := hpoly q hq
  let u (i : J × ℤ) : ℝ≥0 := ⟨w i ^ n, pow_nonneg (zero_le_one.trans (hw i)) _⟩
  obtain ⟨r, hr, hrbound⟩ := exists_continuous_weighted_coefficient_seminorm D u (hcoef n)
  let Cnn : ℝ≥0 := ⟨C, hC⟩
  refine ⟨Cnn • r, hr.const_smul Cnn, fun y ↦ ?_⟩
  have hle (i : J × ℤ) : q (D i y • x i) ≤ C * (w i ^ n * ‖D i y‖) := by
    rw [map_smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)).trans_eq (by ring)
  have hS := (hcoef n y).mul_left C
  have habs := hS.of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) hle
  refine ⟨habs, (habs.tsum_le_tsum hle hS).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hrbound y) hC


include hνG hνS in
/-- The primary principal-value quotient admits a continuous linear lift
to the actual S-local test space. -/
theorem exists_sLocalPrimaryQuotient_testSection
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
    ∃ L : X →L[ℂ] E F S, LeftInverse Q L := by
  let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
  let M := sLocalHomogeneousThetaKernel F S ν A
  let Y := SLocalHomogeneousThetaQuotient F S ν A
  let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
  let X := Y ⧸ R
  let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
  let J := SLocalPrimaryEulerJetIndex F S A p W
  let d := sLocalPrimaryEulerPeriod p
  let w (i : J × ℤ) := 1 + |(i.2 : ℝ)| * d
  have hd : 0 < d := sLocalPrimaryEulerPeriod_pos hp
  have hw (i : J × ℤ) : 0 ≤ w i := by dsimp [w]; positivity
  letI : PolynormableSpace ℂ (E F S) := (sLocalBruhat_nuclear F S).2.1
  letI : BarrelledSpace ℂ Y := (sLocalHomogeneousTheta_barrelled F S ν A).1
  letI : BarrelledSpace ℂ X := quotient_barrelled R
  have hR : IsClosed (R : Set Y) :=
    sLocalFiniteNonzeroTestSubspace_map_isClosed F S (fun v ↦ μG v.val) ν hνS A W
  have hN := nuclearLocallyConvex_quotient (sLocalHomogeneousTheta_primalStructure F S ν A).1 R hR
  letI : T2Space X := hN.1
  have hQ : Surjective Q := R.mkQ_surjective.comp M.mkQ_surjective
  obtain ⟨x, D, hv, _, hsumX, _, _, _⟩ :=
    exists_sLocalPrimaryQuotient_compressedFourier_bases F S (μG := μG) (η := η)
      (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  obtain ⟨b, _, _, hpoly, hseries⟩ :=
    exists_sLocalFourierCompression_hasSum_primary F S (fun v ↦ μG v.val) ν hνS A hp hW
  have hcoef (N : ℕ) (y : X) : Summable (fun i ↦ w i ^ N * ‖D i y‖) := by
    obtain ⟨f, rfl⟩ := hQ y
    refine (sLocalFourierCompression_primaryJets_summable
      F S (fun v ↦ μG v.val) ν hνS A hp W f N).congr (fun i ↦ ?_)
    rw [hv]
    exact mul_comm _ _
  have hlift (y : X) : ∃ g : E F S, HasSum (fun i ↦ D i y • b i) g ∧ Q g = y := by
    obtain ⟨g, hg, _, hj⟩ := hseries (fun i ↦ D i y) (fun N ↦ by
      exact (hcoef N y).congr fun i ↦ mul_comm _ _)
    have he (i : J × ℤ) : D i (Q g) = D i y := (hv i g).trans (hj i.1 i.2)
    exact ⟨g, hg, (hsumX (Q g)).unique (by simpa only [he] using hsumX y)⟩
  obtain ⟨L, hL⟩ := exists_clm_of_weighted_series D b w hw hcoef hpoly
    (fun y ↦ (hlift y).imp fun g h ↦ h.1)
  refine ⟨L, fun y ↦ ?_⟩
  obtain ⟨g, hg, hq⟩ := hlift y
  exact (congrArg Q ((hL y).unique hg)).trans hq

include hνG hνS in
theorem exists_sLocalPrimaryQuotient_fourier_hasSum
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let J := SLocalPrimaryEulerJetIndex F S A p W
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let Q := R.mkQL.comp M.mkQL
    let jet (f : E F S) (i : J × ℤ) :=
      iteratedDeriv i.1.2.val (fun z : ℂ ↦ Z F S (fun v ↦ μG v.val) A⁻¹ (T F S hS f) (1-z))
        (((i.1.1.val + (i.2 : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)
    ∃ b : J × ℤ → E F S,
      (∀ i j, jet (b i) j = if i = j then 1 else 0) ∧
      (∀ (q : Seminorm ℂ ((SLocalHomogeneousThetaQuotient F S ν A) ⧸ R)), Continuous q →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ i, q (Q (b i)) ≤
          C * (1 + |(i.2 : ℝ)| * sLocalPrimaryEulerPeriod p)^N) ∧
      ∀ f : E F S, HasSum (fun i ↦ jet f i • Q (b i)) (Q f) ∧
        ∀ (q : Seminorm ℂ ((SLocalHomogeneousThetaQuotient F S ν A) ⧸ R)), Continuous q →
          Summable (fun i ↦ q (jet f i • Q (b i))) := by
  simp only [T, sLocalStageFourier_eq_compression]
  exact exists_sLocalPrimaryQuotient_compressedFourier_hasSum F S (μG := μG) (η := η) (νG := νG) (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW

include hνG hνS in
theorem exists_sLocalPrimaryQuotient_fourier_bases
    (ω : PontryaginDual (normOneIdeleClass F))
    (hs : Surjective (sIdeleClassInclusion F S))
    (hu : globalNormOneCharacter F ω ∈ (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
    {p : ℕ} (hp : p.Prime) {W : Finset S} (hW : W ⊆ sLocalPrimaryPlaces F S p) :
    let A := sLocalNormOneCharacterOfGlobal F ω S hs hu
    let J := SLocalPrimaryEulerJetIndex F S A p W
    let M := sLocalHomogeneousThetaKernel F S ν A
    let R := (sLocalFiniteNonzeroTestSubspace F S W).map M.mkQ
    let X := (SLocalHomogeneousThetaQuotient F S ν A) ⧸ R
    let Q : E F S →L[ℂ] X := R.mkQL.comp M.mkQL
    ∃ (x : J × ℤ → X) (D : J × ℤ → StrongDual ℂ X),
      (∀ i f, D i (Q f) =
        iteratedDeriv i.1.2.val (fun z : ℂ ↦ Z F S (fun v ↦ μG v.val) A⁻¹ (T F S hS f) (1-z))
          (((i.1.1.val + (i.2 : ℝ) * sLocalPrimaryEulerPeriod p : ℝ) : ℂ) * Complex.I)) ∧
      (∀ i j, D i (x j) = if i = j then 1 else 0) ∧
      (∀ y : X, HasSum (fun i ↦ D i y • x i) y) ∧
      (∀ q : Seminorm ℂ X, Continuous q → ∃ r : Seminorm ℂ X, Continuous r ∧
        ∀ y : X, Summable (fun i ↦ q (D i y • x i)) ∧ (∑' i, q (D i y • x i)) ≤ r y) ∧
      ∀ g : StrongDual ℂ X, HasSum (fun i ↦ g (x i) • D i) g := by
  simp only [T, sLocalStageFourier_eq_compression]
  obtain ⟨x, D, hD, horth, hsum, habs, _, hdual⟩ :=
    exists_sLocalPrimaryQuotient_compressedFourier_bases F S (μG := μG) (η := η) (νG := νG)
      (ν := ν) (hνG := hνG) (hνS := hνS) ω hs hu hp hW
  exact ⟨x, D, hD, horth, hsum, habs, hdual⟩


end GlobalPrimary


end

end Masullo
