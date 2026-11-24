/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
Sources and license are recorded in External/PROVENANCE.md.
-/
import CompactCharacterCompleteness
import LeftRegularRepresentation
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal InnerProductSpace NNReal

namespace Masullo

noncomputable section

/-- A pairwise orthogonal family of vectors in a Hilbert space is summable
if and only if its squared norms are summable. -/
theorem summable_iff_summable_sq_norm_of_orthogonal {𝕜 ι E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] {v : ι → E}
    (hv : Pairwise fun i j ↦ ⟪v i, v j⟫_𝕜 = 0) :
    Summable v ↔ Summable fun i ↦ ‖v i‖ ^ 2 := by
  let S (i : ι) := Submodule.span 𝕜 {v i}
  have hS : OrthogonalFamily 𝕜 (fun i ↦ S i) (fun i ↦ (S i).subtypeₗᵢ) := by
    intro i j hij u w
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp u.property
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp w.property
    change ⟪(u : E), (w : E)⟫_𝕜 = 0
    rw [← ha, ← hb, inner_smul_left, inner_smul_right, hv hij, mul_zero, mul_zero]
  exact hS.summable_iff_norm_sq_summable fun i ↦
    (⟨v i, Submodule.mem_span_singleton_self _⟩ : S i)

variable {G A : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]
  (m : G →ₜ* A) (hm : IsProperMap m)
  (ν : Measure G) [hν : ν.IsHaarMeasure]
  (ν₁ : Measure m.toMonoidHom.ker) [hν₁ : ν₁.IsHaarMeasure]
  (ν₀ : Measure A) [hν₀ : ν₀.IsHaarMeasure]
  (τ : A →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] in
include hm in
private theorem modulus_compactKernel : IsCompact (K : Set G) :=
  hm.isCompact_preimage (isCompact_singleton (x := 1))

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup A] [T2Space A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] in
include hτ in
private theorem exists_regularIsotypic_sectionEquiv :
    ∃ j : (K × A) ≃ₜ* G, ∀ p, j p = (p.1 : G)⁻¹ * τ p.2 := by
  let k (g : G) : K := ⟨τ (m g) * g⁻¹, by
    change m (τ (m g) * g⁻¹) = 1
    rw [map_mul, map_inv, hτ, mul_inv_cancel]⟩
  refine ⟨{ toFun := fun p => (p.1 : G)⁻¹ * τ p.2
            invFun := fun g => (k g, m g)
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_
            continuous_toFun := by fun_prop
            continuous_invFun := ?_ }, fun _ => rfl⟩
  · intro p
    have hmp : m ((p.1 : G)⁻¹ * τ p.2) = p.2 := by
      have hh : m (p.1 : G) = 1 := p.1.property
      rw [map_mul, map_inv, hh, inv_one, one_mul, hτ]
    refine Prod.ext (Subtype.ext ?_) hmp
    simp [k, hmp, mul_inv_rev]
  · intro g
    simp [k, mul_inv_rev]
  · intro p q
    change ((p.1 : G) * (q.1 : G))⁻¹ * τ (p.2 * q.2) = _
    simp [mul_inv_rev, mul_comm, mul_left_comm]
    exact mul_assoc _ _ _
  · exact ((τ.continuous.comp m.continuous).mul continuous_inv).subtype_mk _ |>.prodMk
      m.continuous

include hm hν hν₁ hν₀ hτ

/-- Paper: (4.3.2.4), p. 178. Integration on the fibers parametrized by a
section is defined almost everywhere and gives an L² function for `dt/t`.
Deviation: We use fiber integration of a representative to define the
operator, since the restriction of an arbitrary L² class to the section
is undefined. -/
theorem regularIsotypicComponent_memLp (ω : PontryaginDual K) (f : HaarL2 ν) :
    (∀ᵐ t ∂ν₀,
      Integrable (fun k : K ↦ star (ω k : ℂ) * f ((k : G)⁻¹ * τ t)) ν₁) ∧
    MemLp (fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁)
      2 ν₀ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := 1)))
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m τ hτ
  let η := ν₁.prod ν₀
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  -- Both Haar measures on G differ by a finite positive scalar.
  have hmem : MemLp (f : G → ℂ) 2 (η.map j) := by
    rw [Measure.isMulLeftInvariant_eq_smul (η.map j) ν]
    exact (Lp.memLp f).smul_measure ENNReal.coe_ne_top
  have hcomp := hmem.comp_of_map j.continuous.measurable.aemeasurable
  have hweighted : MemLp (fun p : K × A ↦ star (ω p.1 : ℂ) * f (j p)) 2 η := by
    apply hcomp.of_le
    · have hc : Continuous (fun p : K × A ↦ star (ω p.1 : ℂ)) := by fun_prop
      exact hc.aestronglyMeasurable.mul hcomp.aestronglyMeasurable
    · exact ae_of_all _ (fun p ↦ by
        simp only [norm_mul, norm_star, Circle.norm_coe, one_mul, Function.comp_apply, le_rfl])
  constructor
  · simpa only [hj] using
      (memLp_two_prod_left_ae hweighted).mono fun t ht ↦ ht.integrable (by norm_num)
  · simpa only [hj] using memLp_two_integral_prod_left hweighted

/-- Paper: (4.3.2.4), p. 178. The section gives the `dt/t` L² coordinate
of the unnormalized character average.
Deviation: The fiber integral is formed before passing to the L² class. -/
def regularIsotypicComponent (ω : PontryaginDual K) (f : HaarL2 ν) :
    HaarL2 ν₀ :=
  (regularIsotypicComponent_memLp m hm ν ν₁ ν₀ τ hτ ω f).2.toLp
    (fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁)

set_option maxHeartbeats 600000 in
/-- Almost-everywhere equality on the group pulls back to almost-everywhere equality
on almost every section fiber. -/
private theorem regularIsotypic_section_ae {u v : G → ℂ} (huv : u =ᵐ[ν] v) :
    ∀ᵐ t ∂ν₀, ∀ᵐ a : K ∂ν₁, u ((a : G)⁻¹ * τ t) = v ((a : G)⁻¹ * τ t) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := 1)))
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m τ hτ
  let η := ν₁.prod ν₀
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  have hmap : Measure.QuasiMeasurePreserving j η ν :=
    ⟨j.continuous.measurable, Measure.absolutelyContinuous_isHaarMeasure _ _⟩
  have hprod : ∀ᵐ p ∂η, u (j p) = v (j p) := hmap.ae_eq_comp huv
  have hswap : MeasurePreserving (Prod.swap : A × K → K × A) (ν₀.prod ν₁) η :=
    Measure.measurePreserving_swap
  have hp : ∀ᵐ t ∂ν₀, ∀ᵐ a : K ∂ν₁, u (j (a, t)) = v (j (a, t)) :=
    Measure.ae_ae_of_ae_prod (hswap.quasiMeasurePreserving.ae_eq_comp hprod)
  simpa only [hj] using hp

/-- One constant bounds all the finite sums of squared coordinate norms.
It records the total mass of the kernel and the change of Haar normalization. -/
private theorem exists_regularIsotypicComponent_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : HaarL2 ν) (s : Finset (PontryaginDual K)),
      ∑ ω ∈ s, ‖regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ ω f‖ ^ 2 ≤ C * ‖f‖ ^ 2 := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := 1)))
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m τ hτ
  let η := ν₁.prod ν₀
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  let c := Measure.haarScalarFactor (η.map j) ν
  have hμ : η.map j = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  refine ⟨ν₁.real univ * (c : ℝ), mul_nonneg measureReal_nonneg c.coe_nonneg, fun f s ↦ ?_⟩
  have hmem : MemLp (f : G → ℂ) 2 (η.map j) := hμ ▸ (Lp.memLp f).smul_measure ENNReal.coe_ne_top
  have hcomp := hmem.comp_of_map j.continuous.measurable.aemeasurable
  have hb := sum_sq_character_integral_prod_le ν₁ hcomp
    (fun ω ↦ regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ ω f) (fun ω ↦ by
      simpa only [regularIsotypicComponent, Function.comp_apply, hj] using (regularIsotypicComponent_memLp m hm ν ν₁ ν₀ τ hτ ω f).2.coeFn_toLp) s
  have hn : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp f)
  have heq : ∫ x, ‖f x‖ ^ 2 ∂η.map j = ∫ p, ‖f (j p)‖ ^ 2 ∂η :=
    integral_map j.continuous.measurable.aemeasurable (hmem.aestronglyMeasurable.norm.pow 2)
  calc
    _ ≤ ν₁.real univ * ∫ p, ‖f (j p)‖ ^ 2 ∂η := hb
    _ = _ := by
      rw [← heq, hμ, integral_smul_nnreal_measure, hn, mul_assoc]
      rfl

/-- Paper: (4.3.2.7), p. 178. The family of all coordinates belongs to the
Hilbert direct sum. -/
theorem regularIsotypicTransform_memℓp (f : HaarL2 ν) :
    Memℓp (fun ω : PontryaginDual K ↦ regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ ω f) 2 := by
  obtain ⟨C, _, hC⟩ := exists_regularIsotypicComponent_bound m hm ν ν₁ ν₀ τ hτ
  apply memℓp_gen' (C := C * ‖f‖ ^ 2)
  intro s
  simpa using hC f s

/-- Paper: (4.3.2.7), p. 178. The transform takes all the character
coordinates together in the Hilbert direct sum. -/
def regularIsotypicTransform (f : HaarL2 ν) :
    lp (fun _ : PontryaginDual K ↦ HaarL2 ν₀) 2 :=
  ⟨fun ω ↦ regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ ω f,
    regularIsotypicTransform_memℓp m hm ν ν₁ ν₀ τ hτ f⟩

/-- Paper: (4.3.2.7), p. 178. The coordinate indexed by a character is the
almost-everywhere integral with that character's conjugate. -/
theorem regularIsotypicTransform_ae_eq (ω : PontryaginDual K) (f : HaarL2 ν) :
    (regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ f ω : A → ℂ) =ᵐ[ν₀]
      fun t ↦ ∫ k : K, star (ω k : ℂ) * f ((k : G)⁻¹ * τ t) ∂ν₁ := by
  exact (regularIsotypicComponent_memLp m hm ν ν₁ ν₀ τ hτ ω f).2.coeFn_toLp

/-- Paper: (4.3.2.7), p. 178. The transform is linear and continuous
for the Hilbert direct sum topology. -/
theorem regularIsotypicTransform_continuousLinear :
    ∃ T : HaarL2 ν →L[ℂ] lp (fun _ : PontryaginDual K ↦ HaarL2 ν₀) 2,
      ∀ f : HaarL2 ν, T f = regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ f := by
  let T := regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ
  let C := regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ
  have hC (ω : PontryaginDual K) (f : HaarL2 ν) : (C ω f : A → ℂ) =ᵐ[ν₀]
      fun t ↦ ∫ a : K, star (ω a : ℂ) * f ((a : G)⁻¹ * τ t) ∂ν₁ :=
    (regularIsotypicComponent_memLp m hm ν ν₁ ν₀ τ hτ ω f).2.coeFn_toLp
  let L : HaarL2 ν →ₗ[ℂ] lp (fun _ : PontryaginDual K ↦ HaarL2 ν₀) 2 :=
    { toFun := T
      map_add' := by
        intro f g
        apply lp.ext
        funext ω
        change C ω (f + g) = C ω f + C ω g
        apply Lp.ext
        have ha := regularIsotypic_section_ae m hm ν ν₁ ν₀ τ hτ (Lp.coeFn_add f g)
        filter_upwards [hC ω (f + g), hC ω f, hC ω g, Lp.coeFn_add (C ω f) (C ω g),
          (regularIsotypicComponent_memLp m hm ν ν₁ ν₀ τ hτ ω f).1,
          (regularIsotypicComponent_memLp m hm ν ν₁ ν₀ τ hτ ω g).1, ha]
          with t hfg hf hg hs hi hj ht
        rw [hfg, hs, Pi.add_apply, hf, hg, ← integral_add hi hj]
        apply integral_congr_ae
        filter_upwards [ht] with a ha
        simp only [ha, Pi.add_apply, mul_add]
      map_smul' := by
        intro z f
        apply lp.ext
        funext ω
        change C ω (z • f) = z • C ω f
        apply Lp.ext
        have ha := regularIsotypic_section_ae m hm ν ν₁ ν₀ τ hτ (Lp.coeFn_smul z f)
        filter_upwards [hC ω (z • f), hC ω f, Lp.coeFn_smul z (C ω f), ha]
          with t hzf hf hs ht
        rw [hzf, hs, Pi.smul_apply, smul_eq_mul, hf, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [ht] with a ha
        simp only [ha, Pi.smul_apply, smul_eq_mul, mul_left_comm z] }
  obtain ⟨B, hB, hbound⟩ := exists_regularIsotypicComponent_bound m hm ν ν₁ ν₀ τ hτ
  refine ⟨L.mkContinuous (Real.sqrt B) (fun f ↦ ?_), fun _ ↦ rfl⟩
  apply lp.norm_le_of_forall_sum_le (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  intro s
  change (∑ ω ∈ s, ‖C ω f‖ ^ (2 : ℝ)) ≤ (Real.sqrt B * ‖f‖) ^ (2 : ℝ)
  have hpow (r : ℝ) : r ^ (2 : ℝ) = r ^ (2 : ℕ) := by exact_mod_cast Real.rpow_natCast r 2
  simpa only [hpow, mul_pow, Real.sq_sqrt hB] using hbound f s

/-- Lift each prescribed coefficient along the section and multiply by its character.
The lifts are orthogonal, have a common squared-norm scale, and have the expected
character integrals. -/
private theorem exists_regularIsotypic_synthesisFamily
    (y : lp (fun _ : PontryaginDual K ↦ HaarL2 ν₀) 2) :
    ∃ (B : ℝ) (v : PontryaginDual K → HaarL2 ν),
      (∀ ω, ‖v ω‖ ^ 2 = B * ‖y ω‖ ^ 2) ∧
      (Pairwise fun χ ψ ↦ ⟪v χ, v ψ⟫_ℂ = 0) ∧
      ∀ χ ω, regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ χ (v ω) =
        (∫ a, star (χ a : ℂ) * (ω a : ℂ) ∂ν₁) • y ω := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := 1)))
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m τ hτ
  have : SecondCountableTopology (K × A) := j.toHomeomorph.isEmbedding.secondCountableTopology
  let η := ν₁.prod ν₀
  have : (ν.map j.symm).IsHaarMeasure := j.symm.isHaarMeasure_map ν
  let c := Measure.haarScalarFactor (ν.map j.symm) η
  have hμ : ν.map j.symm = c • η := Measure.isMulLeftInvariant_eq_smul _ _
  have hint {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : K × A → E) :
      ∫ x, F (j.symm x) ∂ν = c • ∫ p, F p ∂η := by
    have he := integral_map_equiv (μ := ν) j.symm.toHomeomorph.toMeasurableEquiv F
    change ∫ p, F p ∂ν.map j.symm = ∫ x, F (j.symm x) ∂ν at he
    rw [← he, hμ, integral_smul_nnreal_measure]
  let coefficientLift (ω : PontryaginDual K) (p : K × A) : ℂ := (ω p.1 : ℂ) * y ω p.2
  have hA (ω : PontryaginDual K) : MemLp (coefficientLift ω) 2 η := by
    have hy := (Lp.memLp (y ω)).comp_snd ν₁
    apply hy.of_le
    · have hc : Continuous (fun p : K × A ↦ (ω p.1 : ℂ)) := by fun_prop
      exact hc.aestronglyMeasurable.mul hy.aestronglyMeasurable
    · exact ae_of_all _ fun p ↦ by simp [coefficientLift, Circle.norm_coe]
  have hv (ω : PontryaginDual K) : MemLp (coefficientLift ω ∘ j.symm) 2 ν :=
    (show MemLp (coefficientLift ω) 2 (ν.map j.symm) from hμ ▸ (hA ω).smul_measure ENNReal.coe_ne_top).comp_of_map
      j.symm.continuous.measurable.aemeasurable
  let v (ω : PontryaginDual K) := (hv ω).toLp (coefficientLift ω ∘ j.symm)
  refine ⟨(c : ℝ) * ν₁.real univ, v, fun ω ↦ ?_, fun χ ψ hχψ ↦ ?_, fun χ ω ↦ ?_⟩
  · have hy : ‖y ω‖ ^ 2 = ∫ t, ‖y ω t‖ ^ 2 ∂ν₀ := by
      simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp (y ω))
    rw [norm_sq_toLp_two (hv ω), hy]
    have he := hint (fun p ↦ ‖coefficientLift ω p‖ ^ 2)
    change ∫ x, ‖coefficientLift ω (j.symm x)‖ ^ 2 ∂ν = _ at he ⊢
    rw [he]
    have he' := integral_fun_snd (μ := ν₁) (ν := ν₀) (fun t ↦ ‖y ω t‖ ^ 2)
    simp only [coefficientLift, norm_mul, Circle.norm_coe, one_mul]
    rw [he', mul_assoc]
    rfl
  · change ⟪v χ, v ψ⟫_ℂ = 0
    rw [L2.inner_def]
    let F (p : K × A) := (star (χ p.1 : ℂ) * (ψ p.1 : ℂ)) *
      (star (y χ p.2) * y ψ p.2)
    calc
      _ = ∫ x, F (j.symm x) ∂ν := by
        apply integral_congr_ae
        filter_upwards [(hv χ).coeFn_toLp, (hv ψ).coeFn_toLp] with x hx hy
        change ⟪v χ x, v ψ x⟫_ℂ = _
        rw [show v χ x = _ from hx, show v ψ x = _ from hy]
        simp only [RCLike.inner_apply, Function.comp_apply, F, coefficientLift, starRingEnd_apply, star_mul']
        ring
      _ = 0 := by
        rw [hint, show (∫ p, F p ∂η) = _ from integral_prod_mul
          (fun a ↦ star (χ a : ℂ) * (ψ a : ℂ)) (fun t ↦ star (y χ t) * y ψ t)]
        rw [integral_character_pair ν₁ χ ψ, if_neg hχψ, zero_mul, smul_zero]
  · let d := ∫ a, star (χ a : ℂ) * (ω a : ℂ) ∂ν₁
    apply Lp.ext
    have hC := (regularIsotypicComponent_memLp m hm ν ν₁ ν₀ τ hτ χ (v ω)).2.coeFn_toLp
    have ha := regularIsotypic_section_ae m hm ν ν₁ ν₀ τ hτ (hv ω).coeFn_toLp
    filter_upwards [hC, Lp.coeFn_smul d (y ω), ha] with t ht hs hrep
    change regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ χ (v ω) t = (d • y ω) t
    rw [show regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ χ (v ω) t = _ from ht, hs]
    change _ = d * y ω t
    rw [show d * y ω t = _ from (integral_mul_const (y ω t) _).symm]
    apply integral_congr_ae
    filter_upwards [hrep] with a ha
    rw [show v ω ((a : G)⁻¹ * τ t) = _ from ha]
    simp only [Function.comp_apply, ← hj (a, t), j.symm_apply_apply, coefficientLift, mul_assoc]

/-- Paper: Lemma 4.3.2.2, p. 179. Every square-summable family of L²
coordinates is in the range of the transform. -/
theorem regularIsotypicTransform_surjective :
    Surjective (regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ) := by
  classical
  intro y
  obtain ⟨T, hT⟩ := regularIsotypicTransform_continuousLinear m hm ν ν₁ ν₀ τ hτ
  obtain ⟨B, v, hn, ho, hcoord⟩ := exists_regularIsotypic_synthesisFamily m hm ν ν₁ ν₀ τ hτ y
  have hy : Summable (fun ω ↦ ‖y ω‖ ^ 2) := by
    simpa using (lp.memℓp y).summable (by norm_num)
  have hs : Summable v := (summable_iff_summable_sq_norm_of_orthogonal ho).2
    (by simpa only [hn] using hy.mul_left B)
  let d : ℂ := ν₁.real univ
  have hd : d ≠ 0 := by
    have : CompactSpace K := isCompact_iff_compactSpace.mp
      (hm.isCompact_preimage (isCompact_singleton (x := 1)))
    dsimp [d]
    exact_mod_cast (measureReal_univ_pos (μ := ν₁)).ne'
  have hsingle (ω : PontryaginDual K) : T (v ω) = d • lp.single 2 ω (y ω) := by
    apply lp.ext
    funext χ
    rw [hT]
    change regularIsotypicComponent m hm ν ν₁ ν₀ τ hτ χ (v ω) = _
    rw [hcoord, integral_character_pair, lp.coeFn_smul, Pi.smul_apply]
    by_cases h : χ = ω
    · subst χ
      rw [if_pos rfl, lp.single_apply_self]
    · rw [if_neg h, lp.single_apply_ne _ _ _ h, zero_smul, smul_zero]
  have hsum : HasSum (fun ω ↦ d • lp.single 2 ω (y ω)) (T (∑' ω, v ω)) :=
    (hs.hasSum.map T T.continuous).congr_fun fun ω ↦ (hsingle ω).symm
  have he := hsum.unique ((lp.hasSum_single (by simp) y).const_smul d)
  refine ⟨d⁻¹ • ∑' ω, v ω, ?_⟩
  rw [← hT, map_smul, he, smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- Paper: Lemma 4.3.2.2, p. 179. The Hilbert sum of the isotypic coordinates
determines the original L² class.
Deviation: Injectivity holds for arbitrary Haar normalizations. -/
theorem regularIsotypicTransform_injective :
    Injective (regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ) := by
  obtain ⟨T, hT⟩ := regularIsotypicTransform_continuousLinear m hm ν ν₁ ν₀ τ hτ
  rw [← funext hT]
  apply (LinearMap.ker_eq_bot.mp _ : Injective T.toLinearMap)
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hf0 : regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ f = 0 := (hT f).symm.trans hf
  have : CompactSpace K := isCompact_iff_compactSpace.mp (modulus_compactKernel m hm)
  have : LocallyCompactSpace K := (modulus_compactKernel m hm).isClosed.locallyCompactSpace
  have : SecondCountableTopology K := Subtype.secondCountableTopology (K : Set G)
  have : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  have : SecondCountableTopology (PontryaginDual K) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  have : Countable (PontryaginDual K) := countable_of_Lindelof_of_discrete
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m τ hτ
  let η := ν₁.prod ν₀
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  have hmem : MemLp (f : G → ℂ) 2 (η.map j) := by
    rw [Measure.isMulLeftInvariant_eq_smul (η.map j) ν]
    exact (Lp.memLp f).smul_measure ENNReal.coe_ne_top
  have hjm := j.continuous.measurable
  have hcoeff (χ : PontryaginDual K) :
      (fun t ↦ ∫ k : K, star (χ k : ℂ) * f (j (k, t)) ∂ν₁) =ᵐ[ν₀] 0 := by
    have h := regularIsotypicTransform_ae_eq m hm ν ν₁ ν₀ τ hτ χ f
    rw [hf0, lp.coeFn_zero, Pi.zero_apply] at h
    simpa only [hj] using h.symm.trans (Lp.coeFn_zero ℂ 2 ν₀)
  -- A common full-measure set of fibers works for all characters.
  have hfiber : ∀ᵐ t ∂ν₀, ∀ᵐ k ∂ν₁, f (j (k, t)) = 0 := by
    filter_upwards [memLp_two_prod_left_ae (hmem.comp_of_map hjm.aemeasurable),
      ae_all_iff.mpr hcoeff] with t ht hc
    exact ae_eq_zero_of_character_integral_eq_zero ν₁ ht hc
  have hmeas : MeasurableSet {x : G | f x = 0} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable f).measurable measurable_const
  have hmeasProd : MeasurableSet {p : K × A | f (j (p.1, p.2)) = 0} :=
    hjm hmeas
  have hprod : ∀ᵐ p ∂η, f (j p) = 0 :=
    (Measure.ae_prod_iff_ae_ae hmeasProd).2
      ((Measure.ae_ae_comm (p := fun k t => f (j (k, t)) = 0) hmeasProd).2 hfiber)
  have hzero : ∀ᵐ x ∂η.map j, f x = 0 := (ae_map_iff hjm.aemeasurable hmeas).2 hprod
  have hae : (f : G → ℂ) =ᵐ[ν] 0 :=
    (Measure.absolutelyContinuous_isHaarMeasure ν (η.map j)).ae_le hzero
  exact Lp.ext (hae.trans (Lp.coeFn_zero ℂ 2 ν).symm)

/-- Paper: Lemma 4.3.2.2, p. 179. The squared norm of the isotypic transform
scales by the mass of the norm-one subgroup times the product Haar measure ratio.
Deviation: The scaling factor accounts for the arbitrary Haar normalizations (ERRATA I73). -/
theorem regularIsotypicTransform_norm_sq (c : ℝ≥0∞)
    (hc : (ν₁.prod ν₀).map (fun z : K × A ↦ (z.1 : G) * τ z.2) = c • ν)
    (f : HaarL2 ν) :
    ‖regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ f‖ ^ 2 = ν₁.real univ * c.toReal * ‖f‖ ^ 2 := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp (modulus_compactKernel m hm)
  have : SecondCountableTopology K := Subtype.secondCountableTopology (K : Set G)
  obtain ⟨j, hj⟩ := exists_regularIsotypic_sectionEquiv m τ hτ
  let η := ν₁.prod ν₀
  have : (η.map j).IsHaarMeasure := j.isHaarMeasure_map η
  have hmem : MemLp (f : G → ℂ) 2 (η.map j) := by
    rw [Measure.isMulLeftInvariant_eq_smul (η.map j) ν]
    exact (Lp.memLp f).smul_measure ENNReal.coe_ne_top
  have hcomp := hmem.comp_of_map j.continuous.measurable.aemeasurable
  have hmap : η.map j = c • ν := by
    let q (z : K × A) : G := (z.1 : G) * τ z.2
    have hq : Measurable q :=
      (continuous_subtype_val.comp continuous_fst).measurable.mul
        (τ.continuous.measurable.comp measurable_snd)
    have hinv : MeasurePreserving (Prod.map (Inv.inv : K → K) id) η η :=
      (Measure.measurePreserving_inv ν₁).prod (MeasurePreserving.id ν₀)
    rw [show (j : K × A → G) = q ∘ Prod.map Inv.inv id from funext hj,
      ← Measure.map_map hq hinv.measurable, hinv.map_eq]
    exact hc
  let y := regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ f
  have hy : HasSum (fun χ ↦ ‖y χ‖ ^ 2) (‖y‖ ^ 2) := by
    simpa using lp.hasSum_norm (by norm_num) y
  have hn : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
    simpa only [Lp.toLp_coeFn] using norm_sq_toLp_two (Lp.memLp f)
  calc
    ‖y‖ ^ 2 = ∑' χ, ‖y χ‖ ^ 2 := hy.tsum_eq.symm
    _ = ν₁.real univ * ∫ p, ‖f (j p)‖ ^ 2 ∂η := by
      refine tsum_sq_character_integral_prod ν₁ hcomp y (fun χ ↦ ?_)
      simpa only [Function.comp_apply, hj] using
        regularIsotypicTransform_ae_eq m hm ν ν₁ ν₀ τ hτ χ f
    _ = _ := by
      have heq : ∫ x, ‖f x‖ ^ 2 ∂η.map j = ∫ p, ‖f (j p)‖ ^ 2 ∂η :=
        integral_map j.continuous.measurable.aemeasurable (hmem.aestronglyMeasurable.norm.pow 2)
      rw [← heq, hmap, integral_smul_measure, hn, mul_assoc]
      rfl


/-- A surjective character transform preserves the norm exactly when the
Haar normalization factor is one, as long as the source is nonzero. -/
theorem regularIsotypicTransform_isometry_iff (c : ℝ≥0∞)
    (hc : (ν₁.prod ν₀).map (fun z : K × A ↦ (z.1 : G) * τ z.2) = c • ν)
    (f : HaarL2 ν) (hf : f ≠ 0) :
    Isometry (regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ) ↔
      ν₁.real univ * c.toReal = 1 := by
  obtain ⟨T, hT⟩ := regularIsotypicTransform_continuousLinear m hm ν ν₁ ν₀ τ hτ
  rw [← funext hT, AddMonoidHomClass.isometry_iff_norm]
  constructor
  · intro h
    have he := regularIsotypicTransform_norm_sq m hm ν ν₁ ν₀ τ hτ c hc f
    rw [← hT f, h f] at he
    have he' : 1 * ‖f‖ ^ 2 = (ν₁.real univ * c.toReal) * ‖f‖ ^ 2 := by
      simpa only [one_mul] using he
    exact (mul_right_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hf)) he').symm
  · intro h g
    have he := regularIsotypicTransform_norm_sq m hm ν ν₁ ν₀ τ hτ c hc g
    rw [← hT g, h, one_mul] at he
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

theorem regularIsotypicTransform_surjective_isometry (c : ℝ≥0∞)
    (hc : (ν₁.prod ν₀).map (fun z : K × A ↦ (z.1 : G) * τ z.2) = c • ν)
    (hnormalized : ν₁.real univ * c.toReal = 1) :
    Surjective (regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ) ∧
      Isometry (regularIsotypicTransform m hm ν ν₁ ν₀ τ hτ) := by
  refine ⟨regularIsotypicTransform_surjective m hm ν ν₁ ν₀ τ hτ, ?_⟩
  obtain ⟨T, hT⟩ := regularIsotypicTransform_continuousLinear m hm ν ν₁ ν₀ τ hτ
  rw [← funext hT]
  apply AddMonoidHomClass.isometry_of_norm
  intro f
  have he := regularIsotypicTransform_norm_sq m hm ν ν₁ ν₀ τ hτ c hc f
  rw [← hT f, hnormalized, one_mul] at he
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

end
end Masullo
