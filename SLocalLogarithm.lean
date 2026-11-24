import SLocalFundamentalDomain

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
abbrev SLogIndex (S : Finset (Place F)) := InfinitePlace F ⊕ S

private theorem archCoordinate_ne_zero (a : Idele F) (v : InfinitePlace F) : a.val.1 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrArg (fun x : Adeles F => x.1 v) a.val_inv)

private theorem finiteCoordinate_ne_zero (a : Idele F) (v : Place F) : a.val.2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrArg (fun x : Adeles F => x.2 v) a.val_inv)

def sLogVector (S : Finset (Place F)) (a : Idele F) : SLogIndex F S → ℝ :=
  Sum.elim (fun v => (v.mult : ℝ) * Real.log ‖a.val.1 v‖)
    (fun v => Real.log ‖a.val.2 v.val‖)

theorem sLogVector_mul (S : Finset (Place F)) (a b : Idele F) :
    sLogVector F S (a * b) = sLogVector F S a + sLogVector F S b := by
  funext v
  cases v with
  | inl v =>
    change (v.mult : ℝ) * Real.log ‖a.val.1 v * b.val.1 v‖ =
      (v.mult : ℝ) * Real.log ‖a.val.1 v‖ + (v.mult : ℝ) * Real.log ‖b.val.1 v‖
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (archCoordinate_ne_zero F a v))
      (norm_ne_zero_iff.mpr (archCoordinate_ne_zero F b v)), mul_add]
  | inr v =>
    change Real.log ‖a.val.2 v * b.val.2 v‖ = Real.log ‖a.val.2 v‖ + Real.log ‖b.val.2 v‖
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (finiteCoordinate_ne_zero F a v))
      (norm_ne_zero_iff.mpr (finiteCoordinate_ne_zero F b v))]

theorem sLogVector_continuous (S : Finset (Place F)) : Continuous (sLogVector F S) := by
  apply continuous_pi
  intro v
  cases v with
  | inl v =>
    have h : Continuous (fun a : Idele F => a.val.1 v) :=
      (continuous_apply v).comp (continuous_fst.comp Units.continuous_val)
    exact continuous_const.mul (h.norm.log fun a => norm_ne_zero_iff.mpr (archCoordinate_ne_zero F a v))
  | inr v =>
    have h : Continuous (fun a : Idele F => a.val.2 v) :=
      (RestrictedProduct.continuous_eval v.val).comp (continuous_snd.comp Units.continuous_val)
    exact h.norm.log fun a => norm_ne_zero_iff.mpr (finiteCoordinate_ne_zero F a v)

theorem sLogVector_sum (S : Finset (Place F)) (a : Idele F) (ha : a ∈ sIdeleBlock F S) :
    ∑ v, sLogVector F S a v = Real.log (ideleNorm F a) := by
  have hs : (Function.mulSupport (fun v : Place F => ‖a.val.2 v‖)) ⊆ (S : Set (Place F)) := by
    intro v hv
    by_contra he
    have h := (sIdeleBlock_mem_iff F S a).mp ha v he
    have hv' : ‖a.val.2 v‖ = 1 := by
      rw [FinitePlace.norm_def, (ideleOrder_eq_zero_iff F a v).mp h]
      simp
    exact hv hv'
  have harch : (∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (archCoordinate_ne_zero F a v))
  have hfin : (∏ v ∈ S, ‖a.val.2 v‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => norm_ne_zero_iff.mpr (finiteCoordinate_ne_zero F a v)
  rw [Fintype.sum_sum_type]
  change (∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log ‖a.val.1 v‖) +
    (∑ v : S, Real.log ‖a.val.2 v‖) =
    Real.log ((∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) * ∏ᶠ v : Place F, ‖a.val.2 v‖)
  rw [finprod_eq_prod_of_mulSupport_subset _ hs, Real.log_mul harch hfin,
    Real.log_prod (fun v _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (archCoordinate_ne_zero F a v))),
    Real.log_prod (fun v _ => norm_ne_zero_iff.mpr (finiteCoordinate_ne_zero F a v))]
  simp only [Real.log_pow]
  rw [Finset.univ_eq_attach]
  exact congrArg (fun z : ℝ => (∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log ‖a.val.1 v‖) + z)
    (Finset.sum_attach S (fun v => Real.log ‖a.val.2 v‖))

theorem sLogVector_section (S : Finset (Place F)) (w : InfinitePlace F → ℝ) (t : ℝ) :
    sLogVector F S (archimedeanExpSection F w (Multiplicative.ofAdd t)) =
      t • (Sum.elim (fun v : InfinitePlace F => (v.mult : ℝ) * w v)
        (fun _ : S => 0) : SLogIndex F S → ℝ) := by
  funext v
  cases v with
  | inl v =>
    change (v.mult : ℝ) * Real.log ‖(archimedeanExpSection F w (Multiplicative.ofAdd t)).val.1 v‖ =
      t * ((v.mult : ℝ) * w v)
    rw [archimedeanExpSection_arch_norm, Real.log_exp]
    change (v.mult : ℝ) * (t * w v) = t * ((v.mult : ℝ) * w v)
    exact mul_left_comm _ _ _
  | inr v =>
    change Real.log ‖(archimedeanExpSection F w (Multiplicative.ofAdd t)).val.2 v‖ = t * 0
    rw [(archimedeanExpSection_components F w (Multiplicative.ofAdd t)).2]
    rw [show (1 : FiniteAdeleRing (𝓞 F) F) v.val = (1 : v.val.adicCompletion F) from rfl,
      norm_one, Real.log_one, mul_zero]

/-- A translated negative orthant cut by the zero-sum hyperplane lies
within a box of radius controlled by the translation and its sum. -/
theorem logSimplex_coordinate_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι → ℝ}
    (hx : ∑ i, x i = 0) (hxy : ∀ i, x i + y i ≤ 0) (i : ι) :
    |x i| ≤ |y i| + |∑ j, y j| := by
  have hz (j : ι) : 0 ≤ -(x j + y j) := neg_nonneg.mpr (hxy j)
  have hb : -(x i + y i) ≤ ∑ j, -(x j + y j) :=
    Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, hx, zero_add] at hb
  calc
    |x i| = |(x i + y i) - y i| := by rw [add_sub_cancel_right]
    _ ≤ |x i + y i| + |y i| := abs_sub _ _
    _ ≤ |∑ j, y j| + |y i| := by
      rw [abs_of_nonpos (hxy i)]
      exact add_le_add (hb.trans (neg_le_abs _)) le_rfl
    _ = _ := add_comm _ _

/-- The compact norm-one component gives a uniform logarithmic radius
for the simplex implementing A.4.1.2. -/
theorem sLogSimplex_bound (S : Finset (Place F)) (w : InfinitePlace F → ℝ)
    (hw : ∑ v, w v * (v.mult : ℝ) = 1) {K : Set (Idele F)} (hK : IsCompact K)
    (hK₀ : K ⊆ (ideleNorm F).ker) :
    ∃ C : ℝ, C > 0 ∧ ∀ g₀ ∈ K, ∀ t : ℝ, t < -1 →
      ∀ x : SLogIndex F S → ℝ, (∑ v, x v = 0) →
      (∀ v, x v + sLogVector F S (archimedeanExpSection F w (Multiplicative.ofAdd t) * g₀) v ≤ 0) →
      (archimedeanExpSection F w (Multiplicative.ofAdd t) * g₀) ∈ sIdeleBlock F S →
      ∀ v, |x v| ≤ C * |Real.log (ideleNorm F (archimedeanExpSection F w (Multiplicative.ofAdd t) * g₀))| := by
  let z : SLogIndex F S → ℝ := Sum.elim
    (fun v : InfinitePlace F => (v.mult : ℝ) * w v) (fun _ : S => 0)
  obtain ⟨B, hB⟩ := (hK.bddAbove_image (sLogVector_continuous F S).norm.continuousOn)
  refine ⟨max B 0 + ‖z‖ + 1, by positivity, ?_⟩
  intro g₀ hg₀ t ht x hx hxy hg v
  let g := archimedeanExpSection F w (Multiplicative.ofAdd t) * g₀
  have hng : Real.log (ideleNorm F g) = t := by
    change Real.log (ideleNorm F (archimedeanExpSection F w (Multiplicative.ofAdd t) * g₀)) = t
    rw [map_mul, ideleNorm_archimedeanExpSection, hw,
      show ideleNorm F g₀ = 1 from hK₀ hg₀, mul_one, mul_one, Real.log_exp]
    rfl
  have hy : sLogVector F S g = t • z + sLogVector F S g₀ := by
    rw [show g = archimedeanExpSection F w (Multiplicative.ofAdd t) * g₀ from rfl,
      sLogVector_mul, sLogVector_section]
  have hy' : ‖sLogVector F S g‖ ≤ |t| * ‖z‖ + max B 0 := by
    rw [hy]
    exact (norm_add_le _ _).trans (by
      rw [norm_smul, Real.norm_eq_abs]
      have hb : ‖sLogVector F S g₀‖ ≤ B :=
        hB (mem_image_of_mem (fun a => ‖sLogVector F S a‖) hg₀)
      exact add_le_add le_rfl (hb.trans (le_max_left _ _)))
  rw [hng]
  calc
    |x v| ≤ |sLogVector F S g v| + |∑ j, sLogVector F S g j| :=
      logSimplex_coordinate_bound hx hxy v
    _ ≤ |t| * ‖z‖ + max B 0 + |t| := by
      rw [sLogVector_sum F S g hg, hng]
      have hcoord : |sLogVector F S g v| ≤ ‖sLogVector F S g‖ :=
        norm_le_pi_norm (sLogVector F S g) v
      exact add_le_add (hcoord.trans hy') le_rfl
    _ ≤ (max B 0 + ‖z‖ + 1) * |t| := by
      have h₁ : 1 ≤ |t| := (show 1 ≤ -t by linarith).trans (neg_le_abs _)
      nlinarith [mul_le_mul_of_nonneg_left h₁ (le_max_right B 0)]

private theorem logSimplex_euclidean_of_coordinate {ι : Type*} [Fintype ι]
    (x : ι → ℝ) {B : ℝ} (hB : 0 ≤ B) (hx : ∀ i, |x i| ≤ B) :
    Real.sqrt (∑ i, (x i) ^ 2) ≤ Real.sqrt (Fintype.card ι) * B := by
  have h : ∑ i, (x i) ^ 2 ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _ : ι, B ^ 2 := Finset.sum_le_sum fun i _ => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) (hx i) 2
      _ = _ := by simp
  exact (Real.sqrt_le_sqrt h).trans_eq (by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hB])

/-- Claim A.4.1.2, with the manuscript's diagonal section and the
Euclidean norm, uniformly on a compact norm-one region. -/
theorem sIdelicLogSimplex_euclidean_bound (S : Finset (Place F)) {K : Set (Idele F)}
    (hK : IsCompact K) (hK₀ : K ⊆ (ideleNorm F).ker) :
    ∃ C : ℝ, C > 0 ∧ ∀ g₀ ∈ K, ∀ t : ℝ,
      let g := diagonalExpSection F (Multiplicative.ofAdd t) * g₀
      ideleNorm F g < Real.exp (-1) → g ∈ sIdeleBlock F S →
      ∀ x : SLogIndex F S → ℝ, (∑ v, x v = 0) →
        (∀ v, x v + sLogVector F S g v ≤ 0) →
        Real.sqrt (∑ v, (x v) ^ 2) ≤ C * |Real.log (ideleNorm F g)| := by
  let w (v : InfinitePlace F) : ℝ := ((v.mult : ℝ) * Fintype.card (InfinitePlace F))⁻¹
  have hw : ∑ v, w v * (v.mult : ℝ) = 1 := by
    have h := ideleNorm_diagonalExpSection F (Multiplicative.ofAdd 1)
    change ideleNorm F (archimedeanExpSection F w (Multiplicative.ofAdd 1)) = Real.exp 1 at h
    rw [ideleNorm_archimedeanExpSection] at h
    have h' := Real.exp_injective h
    change (1 : ℝ) * ∑ v, w v * (v.mult : ℝ) = 1 at h'
    rwa [one_mul] at h'
  obtain ⟨C, hC, h⟩ := sLogSimplex_bound F S w hw hK hK₀
  have hcard : 0 < Real.sqrt (Fintype.card (SLogIndex F S)) := by
    haveI : Nonempty (SLogIndex F S) := ⟨Sum.inl (Classical.choice inferInstance)⟩
    exact Real.sqrt_pos_of_pos (Nat.cast_pos.mpr Fintype.card_pos)
  refine ⟨Real.sqrt (Fintype.card (SLogIndex F S)) * C, mul_pos hcard hC, ?_⟩
  intro g₀ hg₀ t g hg hgB x hx hxy
  have he : ideleNorm F g = Real.exp t := by
    change ideleNorm F (diagonalExpSection F (Multiplicative.ofAdd t) * g₀) = _
    rw [map_mul, ideleNorm_diagonalExpSection, show ideleNorm F g₀ = 1 from hK₀ hg₀, mul_one]
    rfl
  have ht : t < -1 := Real.exp_lt_exp.mp (he ▸ hg)
  have hcoord := h g₀ hg₀ t ht x hx hxy hgB
  exact (logSimplex_euclidean_of_coordinate x
    (mul_nonneg hC.le (abs_nonneg (Real.log (ideleNorm F g)))) hcoord).trans_eq
    (mul_assoc _ _ _).symm

theorem sIdelicBasicLogSimplex_bound {ι : Type*} [Finite ι]
    (S : Finset (Place F)) (v : InfinitePlace F) (c : ι → NormOneIdeles F) :
    ∃ C : ℝ, C > 0 ∧ ∀ i (b : NormOneIdeles F), b ∈ ideleFundamentalCell F v →
      ∀ t : ℝ, let g := diagonalExpSection F (Multiplicative.ofAdd t) * (c i * b).val
      ideleNorm F g < Real.exp (-1) → g ∈ sIdeleBlock F S →
      ∀ x : SLogIndex F S → ℝ, (∑ v, x v = 0) →
        (∀ v, x v + sLogVector F S g v ≤ 0) →
        Real.sqrt (∑ v, (x v) ^ 2) ≤ C * |Real.log (ideleNorm F g)| := by
  obtain ⟨K, hK, hb⟩ := ideleFundamentalCell_containedCompact F v
  let T := ⋃ i, (Homeomorph.mulLeft (c i)) '' K
  let val : NormOneIdeles F → Idele F := Subtype.val
  have ht : IsCompact T := isCompact_iUnion fun i => hK.image (Homeomorph.mulLeft (c i)).continuous
  have hN : val '' T ⊆ (ideleNorm F).ker := by rintro _ ⟨b, _, rfl⟩; exact b.property
  obtain ⟨C, hC, hh⟩ := sIdelicLogSimplex_euclidean_bound F S
    (ht.image (f := val) continuous_subtype_val) hN
  exact ⟨C, hC, fun i b h => hh (c i * b).val
    ⟨c i * b, mem_iUnion.mpr ⟨i, b, hb h, rfl⟩, rfl⟩⟩

theorem sLogVector_finite_order (S : Finset (Place F)) (a : Idele F) (v : S) :
    sLogVector F S a (Sum.inr v) =
      -(ideleOrder F a v : ℝ) * Real.log (Ideal.absNorm v.val.asIdeal) := by
  have hvalue : (Valued.v (a.val.2 v.val) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (finiteCoordinate_ne_zero F a v.val)
  change Real.log ‖a.val.2 v.val‖ = _
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hvalue, NNReal.coe_zpow,
    Real.log_zpow]
  have he : (WithZero.unzero hvalue).toAdd =
      WithZero.log (Valued.v (a.val.2 v.val)) := by
    conv_rhs => rw [← WithZero.coe_unzero hvalue]
    rfl
  rw [he, ideleOrder, Int.cast_neg, neg_neg, NNReal.coe_natCast]

end

end Masullo
