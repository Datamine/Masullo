/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
Sources and license are recorded in External/PROVENANCE.md.
-/
import PontryaginSeparation
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProductSpace Pointwise

namespace Masullo

noncomputable section

section ProductIntegrals

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem norm_integral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {u : α → E} (hu : MemLp u 2 μ) :
    ‖∫ a, u a ∂μ‖ ^ 2 ≤ μ.real univ * ∫ a, ‖u a‖ ^ 2 ∂μ := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := fun a ↦ ‖u a‖) (g := fun _ ↦ (1 : ℝ))
    Real.HolderConjugate.two_two (by simpa using hu.norm) (memLp_const _)
  have hle : ‖∫ a, u a ∂μ‖ ≤ Real.sqrt (∫ a, ‖u a‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa [Real.sqrt_eq_rpow] using hcs
  calc
    _ ≤ (Real.sqrt (∫ a, ‖u a‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
        Real.sq_sqrt (measureReal_nonneg)]
      exact mul_comm _ _

omit [NormedSpace ℝ E] in
/-- A square-integrable function on a product is square integrable on almost every fiber. -/
theorem memLp_two_prod_left_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [SFinite μ] {ν : Measure β} [SFinite ν] {u : α × β → E}
    (h₂ : MemLp u 2 (μ.prod ν)) : ∀ᵐ b ∂ν, MemLp (fun a ↦ u (a, b)) 2 μ := by
  filter_upwards [h₂.norm.integrable_sq.prod_left_ae, h₂.aestronglyMeasurable.prodMk_right]
    with b hb hmeas
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 hb

/-- Integrating a square-integrable function over a finite-measure factor gives a
square-integrable function on the other factor. -/
theorem memLp_two_integral_prod_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure β} [SFinite ν] {u : α × β → E}
    (h₂ : MemLp u 2 (μ.prod ν)) : MemLp (fun b ↦ ∫ a, u (a, b) ∂μ) 2 ν := by
  have hsq := h₂.norm.integrable_sq
  have hmeas : AEStronglyMeasurable (fun b ↦ ∫ a, u (a, b) ∂μ) ν :=
    h₂.aestronglyMeasurable.prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  apply (hsq.integral_prod_right.const_mul (μ.real univ)).mono'
  · exact hmeas.norm.pow 2
  · filter_upwards [memLp_two_prod_left_ae h₂] with b hb
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact norm_integral_sq_le hb

end ProductIntegrals

/-- Restricted characters separate points of the subgroup, so their complex linear span is dense. -/
theorem dense_span_restrictedCharacters {H K : Type*}
    [CommGroup H] [TopologicalSpace H] [CompactSpace H]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (i : H →ₜ* K) (hi : Function.Injective i)
    (r : PontryaginDual K →* C(H, ℂ)) (hr : ∀ ψ x, r ψ x = (ψ (i x) : ℂ)) :
    (Submodule.span ℂ (range r)).topologicalClosure = ⊤ := by
  let S := MonoidHom.mrange r
  let A := StarAlgebra.adjoin ℂ (S : Set C(H, ℂ))
  have hstar : star (S : Set C(H, ℂ)) ⊆ S := by
    rw [Set.star_subset]
    rintro _ ⟨ψ, rfl⟩
    refine ⟨ψ⁻¹, ContinuousMap.ext fun x ↦ ?_⟩
    change r ψ⁻¹ x = star (r ψ x)
    rw [hr, hr]
    exact Circle.coe_inv_eq_conj (ψ (i x))
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr (hi.ne hxy))
    refine ⟨_, ⟨r ψ, StarAlgebra.subset_adjoin ℂ (S : Set C(H, ℂ)) ⟨ψ, rfl⟩, rfl⟩, ?_⟩
    change r ψ x ≠ r ψ y
    rw [hr, hr, Ne, Circle.coe_inj]
    exact fun he ↦ hψ ((map_div ψ _ _).trans (div_eq_one.mpr he))
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span ℂ (range r) := by
    rw [StarAlgebra.adjoin_eq_span, Set.union_eq_left.mpr hstar, S.closure_eq]
    rfl
  rw [← hspan]
  exact congrArg (fun S : StarSubalgebra ℂ C(H, ℂ) ↦ S.toSubalgebra.toSubmodule)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep)

/-- The complex linear span of the characters of a compact Hausdorff abelian group
is dense in its continuous functions. -/
theorem dense_span_pontryaginDual {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (r : PontryaginDual K →* C(K, ℂ)) (hr : ∀ χ x, r χ x = (χ x : ℂ)) :
    (Submodule.span ℂ (range r)).topologicalClosure = ⊤ :=
  dense_span_restrictedCharacters (ContinuousMonoidHom.id K) Function.injective_id r hr

variable {K : Type*} [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [NeZero μ]

/-- Squaring the L² norm recovers the integral of the squared pointwise norm. -/
theorem norm_sq_toLp_two {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {u : α → ℂ} (hu : MemLp u 2 ν) :
    ‖hu.toLp u‖ ^ 2 = ∫ a, ‖u a‖ ^ 2 ∂ν := by
  rw [← @real_inner_self_eq_norm_sq (Lp ℂ 2 ν), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with a ha
  rw [ha, real_inner_self_eq_norm_sq]

omit [CompactSpace K] [IsFiniteMeasure μ] [NeZero μ] in
private theorem integral_character_pair_zero {χ ψ : PontryaginDual K} (hne : χ ≠ ψ) :
    ∫ a, star (χ a : ℂ) * (ψ a : ℂ) ∂μ = 0 := by
  obtain ⟨b, hb⟩ : ∃ b : K, χ b ≠ ψ b := by
    by_contra! h
    exact hne (DFunLike.ext _ _ h)
  let F := fun a : K ↦ star (χ a : ℂ) * (ψ a : ℂ)
  have hF (a : K) : F (b * a) = F b * F a := by
    simp only [F, map_mul, Circle.coe_mul, star_mul']
    ring
  have hne' : F b ≠ 1 := by
    intro he
    apply hb
    apply Subtype.ext
    have hh := congrArg (fun z : ℂ ↦ (χ b : ℂ) * z) he
    simpa [F, ← mul_assoc, ← Circle.coe_inv_eq_conj] using hh.symm
  have h : F b * (∫ a, F a ∂μ) = 1 * (∫ a, F a ∂μ) := by
    rw [one_mul, ← integral_const_mul, ← integral_mul_left_eq_self (μ := μ) F b]
    exact integral_congr_ae (ae_of_all _ fun a ↦ (hF a).symm)
  exact (mul_eq_mul_right_iff.mp h).resolve_left hne'

omit [CompactSpace K] [IsFiniteMeasure μ] [NeZero μ] in
/-- The Haar integral of the product of two characters, with the first conjugated,
is zero off the diagonal and the full Haar mass on the diagonal. -/
theorem integral_character_pair [DecidableEq (PontryaginDual K)] (χ ψ : PontryaginDual K) :
    ∫ a, star (χ a : ℂ) * (ψ a : ℂ) ∂μ = if χ = ψ then (μ.real univ : ℂ) else 0 := by
  by_cases h : χ = ψ
  · subst ψ
    simp [← Circle.coe_inv_eq_conj, Complex.real_smul]
  · simpa [h] using integral_character_pair_zero μ h

omit [μ.IsMulLeftInvariant] [NeZero μ] in
/-- A square-integrable function on a compact Hausdorff abelian group vanishes
almost everywhere if all its character coefficients vanish. -/
theorem ae_eq_zero_of_character_integral_eq_zero [T2Space K] [μ.WeaklyRegular]
    {u : K → ℂ} (hu : MemLp u 2 μ)
    (h : ∀ χ : PontryaginDual K, ∫ a, star (χ a : ℂ) * u a ∂μ = 0) :
    u =ᵐ[μ] 0 := by
  let v (χ : PontryaginDual K) : C(K, ℂ) :=
    ⟨fun a ↦ χ a, continuous_subtype_val.comp χ.continuous⟩
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let L := (innerSL ℂ (hu.toLp u)).comp T
  have hspan : Submodule.span ℂ (range v) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨χ, rfl⟩
    change ⟪hu.toLp u, T (v χ)⟫_ℂ = 0
    rw [inner_eq_zero_symm, L2.inner_def, ← h χ]
    apply integral_congr_ae
    filter_upwards [(v χ).coeFn_toLp (p := 2) (𝕜 := ℂ) μ, hu.coeFn_toLp] with a ha hb
    rw [ha, hb]
    simp [v, mul_comm]
  have htop := (Submodule.span ℂ (range v)).topologicalClosure_minimal hspan L.isClosed_ker
  let r : PontryaginDual K →* C(K, ℂ) :=
    { toFun := v, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
  rw [show (Submodule.span ℂ (range v)).topologicalClosure = ⊤ from
    dense_span_pontryaginDual r (fun _ _ ↦ rfl)] at htop
  have hzero : hu.toLp u = 0 := by
    have hd : DenseRange T := ContinuousMap.toLp_denseRange ℂ μ ℂ (p := 2) (by simp)
    exact hd.eq_of_inner_left ℂ fun f ↦ by
      rw [inner_zero_left]
      exact htop (Submodule.mem_top (x := f))
  exact hu.coeFn_toLp.symm.trans (hzero ▸ Lp.coeFn_zero ℂ 2 μ)

omit [NeZero μ] in
/-- On a compact abelian group of Haar mass one, a continuous function with
absolutely summable Fourier coefficients equals its Fourier series pointwise. -/
theorem compact_fourier_eq_tsum [T2Space K] [μ.WeaklyRegular] [μ.IsOpenPosMeasure]
    [Countable (PontryaginDual K)] {u : K → ℂ} (hu : Continuous u) (hμ : μ univ = 1)
    (hs : Summable (fun χ : PontryaginDual K => ‖∫ x, star (χ x : ℂ) * u x ∂μ‖)) :
    ∀ x : K, u x = ∑' χ : PontryaginDual K, (∫ y, star (χ y : ℂ) * u y ∂μ) * (χ x : ℂ) := by
  classical
  let a (χ : PontryaginDual K) := ∫ x, star (χ x : ℂ) * u x ∂μ
  let w (χ : PontryaginDual K) (x : K) := a χ * (χ x : ℂ)
  let v (x : K) := ∑' χ, w χ x
  have hχ (χ : PontryaginDual K) : Continuous (fun x : K => (χ x : ℂ)) :=
    continuous_subtype_val.comp χ.continuous
  have hw (χ : PontryaginDual K) : Continuous (w χ) := continuous_const.mul (hχ χ)
  have hv : Continuous v := by
    have h := HasSumUniformlyOn.of_norm_le_summable (s := (univ : Set K)) (f := w) hs
      (fun χ x _ => by change ‖w χ x‖ ≤ ‖a χ‖; simp [w, Circle.norm_coe])
    rw [← continuousOn_univ]
    exact (hasSumUniformlyOn_iff_tendstoUniformlyOn.mp h).continuousOn
      (.of_forall fun s => (continuous_finsetSum s fun χ _ => hw χ).continuousOn)
  have hcoef (ψ : PontryaginDual K) : (∫ x, star (ψ x : ℂ) * v x ∂μ) = a ψ := by
    let z (χ : PontryaginDual K) (x : K) := star (ψ x : ℂ) * w χ x
    have hz (χ : PontryaginDual K) : Integrable (z χ) μ :=
      ((hχ ψ).star.mul (hw χ)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hz_norm (χ : PontryaginDual K) : (∫ x, ‖z χ x‖ ∂μ) = ‖a χ‖ := by
      simp [z, w, Circle.norm_coe, measureReal_def, hμ]
    have hs' : Summable (fun χ => ∫ x, ‖z χ x‖ ∂μ) := hs.congr fun χ => (hz_norm χ).symm
    have h := (hasSum_integral_of_summable_integral_norm hz hs').tsum_eq
    have hiz (χ : PontryaginDual K) :
        (∫ x, z χ x ∂μ) = if ψ = χ then a ψ else 0 := by
      have he (x : K) : z χ x = a χ * (star (ψ x : ℂ) * (χ x : ℂ)) := by
        dsimp [z, w]
        ring
      simp_rw [he]
      rw [integral_const_mul, integral_character_pair μ]
      by_cases h : ψ = χ <;> simp [h, measureReal_def, hμ]
    simp_rw [hiz] at h
    rw [tsum_eq_single ψ (fun χ hχ => ite_eq_right (Ne.symm hχ)), ite_eq_left rfl] at h
    rw [h]
    apply integral_congr_ae
    exact .of_forall fun x => by
      change star (ψ x : ℂ) * (∑' χ, w χ x) = ∑' χ, star (ψ x : ℂ) * w χ x
      exact tsum_mul_left.symm
  have hL2 : MemLp (u - v) 2 μ :=
    (hu.sub hv).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero := ae_eq_zero_of_character_integral_eq_zero μ hL2 (fun χ => by
    change (∫ x, star (χ x : ℂ) * (u x - v x) ∂μ) = 0
    simp_rw [mul_sub]
    have h1 : Integrable (fun x => star (χ x : ℂ) * u x) μ :=
      ((hχ χ).star.mul hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h2 : Integrable (fun x => star (χ x : ℂ) * v x) μ :=
      ((hχ χ).star.mul hv).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_sub h1 h2, hcoef]
    exact sub_self _)
  have he := Measure.eq_of_ae_eq hzero (hu.sub hv) continuous_const
  intro x
  exact sub_eq_zero.mp (congrFun he x)

/-- Bessel's inequality for continuous characters on a compact abelian group with
finite nonzero invariant measure, including its total-mass factor. -/
theorem sum_sq_character_integral_le {u : K → ℂ} (hu : MemLp u 2 μ)
    (s : Finset (PontryaginDual K)) :
    ∑ χ ∈ s, ‖∫ a, star (χ a : ℂ) * u a ∂μ‖ ^ 2 ≤
      μ.real univ * ∫ a, ‖u a‖ ^ 2 ∂μ := by
  let v (χ : PontryaginDual K) : C(K, ℂ) := ⟨fun a ↦ χ a, by fun_prop⟩
  let V (χ : PontryaginDual K) := ContinuousMap.toLp 2 μ ℂ (v χ)
  let r := Real.sqrt (μ.real univ)
  have hr : 0 < r := Real.sqrt_pos.2 measureReal_univ_pos
  have hr2 : r ^ 2 = μ.real univ := Real.sq_sqrt measureReal_nonneg
  have hv (χ : PontryaginDual K) : ‖V χ‖ ^ 2 = μ.real univ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc
      _ = ∫ _ : K, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [(v χ).coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with a ha
        rw [ha, real_inner_self_eq_norm_sq]
        change ‖(χ a : ℂ)‖ ^ 2 = 1
        rw [Circle.norm_coe, one_pow]
      _ = _ := by simp
  let W (χ : PontryaginDual K) := ((r⁻¹ : ℝ) : ℂ) • V χ
  have hW : Orthonormal ℂ W := by
    constructor
    · intro χ
      have he : ‖V χ‖ = r := by nlinarith [hv χ, norm_nonneg (V χ)]
      simp [W, norm_smul, Real.norm_eq_abs, abs_of_pos hr, he, hr.ne']
    · intro χ ψ hne
      have he : ⟪V χ, V ψ⟫_ℂ = 0 := by
        rw [ContinuousMap.inner_toLp]
        simpa [v, mul_comm] using integral_character_pair_zero μ hne
      change ⟪((r⁻¹ : ℝ) : ℂ) • V χ, ((r⁻¹ : ℝ) : ℂ) • V ψ⟫_ℂ = 0
      simp [inner_smul_left, inner_smul_right, he]
  have hi (χ : PontryaginDual K) :
      ⟪V χ, hu.toLp u⟫_ℂ = ∫ a, star (χ a : ℂ) * u a ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(v χ).coeFn_toLp (p := 2) (𝕜 := ℂ) μ, hu.coeFn_toLp] with a ha hb
    rw [ha, hb]
    simp [v, mul_comm]
  have hrestore (χ : PontryaginDual K) : (r : ℂ) • W χ = V χ := by simp [W, smul_smul, hr.ne']
  calc
    _ = ∑ χ ∈ s, r ^ 2 * ‖⟪W χ, hu.toLp u⟫_ℂ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [← hi, ← hrestore χ, inner_smul_left]
      simp [mul_pow, Real.norm_eq_abs, abs_of_pos hr]
    _ = r ^ 2 * ∑ χ ∈ s, ‖⟪W χ, hu.toLp u⟫_ℂ‖ ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ r ^ 2 * ‖hu.toLp u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (hW.sum_inner_products_le _) (sq_nonneg _)
    _ = _ := by rw [hr2, norm_sq_toLp_two hu]

/-- Bessel's inequality on the first factor of a product, integrated over the second factor. -/
theorem sum_sq_character_integral_prod_le {β : Type*} [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {u : K × β → ℂ} (hu : MemLp u 2 (μ.prod ν))
    (v : PontryaginDual K → Lp ℂ 2 ν)
    (hv : ∀ χ, (v χ : β → ℂ) =ᵐ[ν] fun b ↦ ∫ a, star (χ a : ℂ) * u (a, b) ∂μ)
    (s : Finset (PontryaginDual K)) :
    ∑ χ ∈ s, ‖v χ‖ ^ 2 ≤ μ.real univ * ∫ p, ‖u p‖ ^ 2 ∂μ.prod ν := by
  have hsq := hu.norm.integrable_sq
  have hvint (χ : PontryaginDual K) := (Lp.memLp (v χ)).norm.integrable_sq
  have hn (χ : PontryaginDual K) : ‖v χ‖ ^ 2 = ∫ b, ‖v χ b‖ ^ 2 ∂ν := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp (v χ))
  calc
    _ = ∫ b, ∑ χ ∈ s, ‖v χ b‖ ^ 2 ∂ν := by
      simp_rw [hn]
      exact (integral_finsetSum _ fun i _ ↦ hvint i).symm
    _ ≤ ∫ b, μ.real univ * ∫ a, ‖u (a, b)‖ ^ 2 ∂μ ∂ν := by
      apply integral_mono_ae (integrable_finsetSum _ fun i _ ↦ hvint i)
        (hsq.integral_prod_right.const_mul _)
      have ha := (eventually_all_finset s).2 fun χ _ ↦ hv χ
      filter_upwards [memLp_two_prod_left_ae hu, ha] with b hb hb'
      simpa only [Finset.sum_congr rfl fun χ hχ ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) (hb' χ hχ)]
        using sum_sq_character_integral_le μ hb s
    _ = _ := by rw [integral_const_mul, integral_prod_symm _ hsq]

section Parseval

variable [T2Space K] [μ.WeaklyRegular]

/-- The normalized characters form a Hilbert basis whose coordinates are the
character integrals divided by the square root of the Haar mass. -/
private theorem exists_character_hilbertBasis :
    ∃ b : HilbertBasis (PontryaginDual K) ℂ (Lp ℂ 2 μ),
      ∀ {u : K → ℂ} (hu : MemLp u 2 μ) (χ : PontryaginDual K),
        (∫ a, star (χ a : ℂ) * u a ∂μ) =
          (Real.sqrt (μ.real univ) : ℂ) * b.repr (hu.toLp u) χ := by
  classical
  let v : PontryaginDual K →* C(K, ℂ) :=
    { toFun := fun χ ↦ ⟨fun a ↦ χ a, by fun_prop⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let V := T ∘ v
  let r := Real.sqrt (μ.real univ)
  have hr : 0 < r := Real.sqrt_pos.2 measureReal_univ_pos
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr2 : r ^ 2 = μ.real univ := Real.sq_sqrt measureReal_nonneg
  let W (χ : PontryaginDual K) := ((r : ℂ)⁻¹) • V χ
  have hW : Orthonormal ℂ W := by
    rw [orthonormal_iff_ite]
    intro χ ψ
    have h : ⟪V χ, V ψ⟫_ℂ = if χ = ψ then (μ.real univ : ℂ) else 0 := by
      change ⟪T (v χ), T (v ψ)⟫_ℂ = _
      rw [ContinuousMap.inner_toLp]
      change (∫ a, (ψ a : ℂ) * star (χ a : ℂ) ∂μ) = _
      simp_rw [mul_comm (ψ _ : ℂ)]
      exact integral_character_pair μ χ ψ
    simp only [W, inner_smul_left, inner_smul_right, h]
    split_ifs
    · have hconj : starRingEnd ℂ (r : ℂ)⁻¹ = (r : ℂ)⁻¹ := by
        rw [← Complex.ofReal_inv, Complex.conj_ofReal]
      rw [hconj, ← hr2, Complex.ofReal_pow]
      field_simp
    · simp
  have hspan : (Submodule.span ℂ (range V)).topologicalClosure = ⊤ := by
    have hdense := ContinuousMap.toLp_denseRange ℂ μ ℂ (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    have h := hdense.topologicalClosure_map_submodule (dense_span_pontryaginDual v (fun _ _ ↦ rfl))
    rwa [Submodule.map_span, ← range_comp] at h
  have hspanW : (Submodule.span ℂ (range W)).topologicalClosure = ⊤ := by
    rw [show range W = (r : ℂ)⁻¹ • range V from Set.range_smul _ V,
      Submodule.span_smul_eq_of_isUnit _ _ (isUnit_iff_ne_zero.mpr (inv_ne_zero hr')), hspan]
  let b := HilbertBasis.mk hW hspanW.ge
  refine ⟨b, fun {u} hu χ ↦ ?_⟩
  have hi : ⟪V χ, hu.toLp u⟫_ℂ = ∫ a, star (χ a : ℂ) * u a ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(v χ).coeFn_toLp (p := 2) (𝕜 := ℂ) μ, hu.coeFn_toLp] with a ha hb
    change ⟪T (v χ) a, hu.toLp u a⟫_ℂ = _
    rw [ha, hb]
    exact mul_comm _ _
  have hrestore : (r : ℂ) • W χ = V χ := by simp [W, smul_smul, hr']
  rw [← hi, ← hrestore, inner_smul_left, b.repr_apply_apply]
  simp [b, r]

/-- For probability Haar measure, the compact angular Plancherel map
has the usual Fourier coefficients on the dual with counting measure. -/
theorem exists_compactCharacterPlancherel [IsProbabilityMeasure μ] :
    ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] lp (fun _ : PontryaginDual K => ℂ) 2,
      ∀ (f : Lp ℂ 2 μ) (χ : PontryaginDual K),
        U f χ = ∫ k, star (χ k : ℂ) * f k ∂μ := by
  obtain ⟨b, hb⟩ := exists_character_hilbertBasis μ
  refine ⟨b.repr, fun f χ => ?_⟩
  have h := hb (Lp.memLp f) χ
  rw [Lp.toLp_coeFn] at h
  simpa [Measure.real] using h.symm

/-- Parseval's identity on the first factor of a product, integrated over the second factor.
The coefficients are unnormalized, so the identity includes the mass of the first factor. -/
theorem tsum_sq_character_integral_prod [SecondCountableTopology K]
    {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
    {u : K × β → ℂ} (hu : MemLp u 2 (μ.prod ν))
    (v : PontryaginDual K → Lp ℂ 2 ν)
    (hv : ∀ χ, (v χ : β → ℂ) =ᵐ[ν] fun t ↦ ∫ a, star (χ a : ℂ) * u (a, t) ∂μ) :
    ∑' χ, ‖v χ‖ ^ 2 = μ.real univ * ∫ p, ‖u p‖ ^ 2 ∂μ.prod ν := by
  obtain ⟨b, hb⟩ := exists_character_hilbertBasis μ
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have hd : Pairwise (fun χ ψ ↦ Disjoint (Metric.ball (b χ) (1 / 2))
      (Metric.ball (b ψ) (1 / 2))) := by
    intro χ ψ hne
    apply Metric.ball_disjoint_ball
    have hsq : dist (b χ) (b ψ) ^ 2 = 2 := by
      rw [dist_eq_norm, @norm_sub_sq ℂ, b.orthonormal.2 hne,
        b.orthonormal.1 χ, b.orthonormal.1 ψ]
      norm_num
    nlinarith [dist_nonneg (x := b χ) (y := b ψ)]
  have : Countable (PontryaginDual K) :=
    hd.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
      (fun _ ↦ Metric.nonempty_ball.mpr (by norm_num))
  have hn (χ : PontryaginDual K) : ‖v χ‖ ^ 2 = ∫ t, ‖v χ t‖ ^ 2 ∂ν := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp (v χ))
  have hi (χ : PontryaginDual K) := (Lp.memLp (v χ)).norm.integrable_sq
  have hs : Summable (fun χ ↦ ‖v χ‖ ^ 2) :=
    summable_of_sum_le (fun _ ↦ sq_nonneg _) (sum_sq_character_integral_prod_le μ hu v hv)
  calc
    _ = ∫ t, ∑' χ, ‖v χ t‖ ^ 2 ∂ν := by
      simp_rw [hn]
      apply integral_tsum_of_summable_integral_norm hi
      simpa only [Real.norm_of_nonneg (sq_nonneg (_ : ℝ)), ← hn] using hs
    _ = ∫ t, μ.real univ * ∫ a, ‖u (a, t)‖ ^ 2 ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [memLp_two_prod_left_ae hu, (ae_all_iff.2 hv)] with t ht hvt
      simp_rw [hvt, hb ht, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt measureReal_nonneg]
      rw [tsum_mul_left, ← norm_sq_toLp_two ht]
      congr 1
      simpa using (lp.hasSum_norm (by norm_num) (b.repr (ht.toLp (fun a ↦ u (a, t))))).tsum_eq
    _ = _ := by rw [integral_const_mul, integral_prod_symm _ hu.norm.integrable_sq]

end Parseval

end
end Masullo
