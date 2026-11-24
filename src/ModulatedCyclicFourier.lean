import BruhatSchwartz
import LCAFourierIntegral
import ModulatedCharacters
import ModulatedJumpPoisson
import WeilQuotientIntegral
import FilteredQuotientIndentation
import BruhatCompactSupport
import BruhatDirectionalDerivatives
import CompactCharacterCompleteness
import CompactBruhatCharacterBounds
import IntegerBruhatMultipliers

open MeasureTheory Set

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Fourier coefficients on the cyclic quotient use its volume-normalized measure
and the conjugate of the exponential basis function. -/
def modulatedCyclicFourierCoeff
    (μ : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (μ γ))
    [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
    [MeasurableSpace (G ⧸ Subgroup.zpowers γ)] [BorelSpace (G ⧸ Subgroup.zpowers γ)]
    (ν : Measure (G ⧸ Subgroup.zpowers γ)) (χ : CircleCharacter G) (n : ℤ)
    (f : BruhatSchwartz (G ⧸ Subgroup.zpowers γ)) : ℂ :=
  lcaFourier ((ν univ)⁻¹ • ν) f.val (modulatedCyclicCharacter μ γ hγ χ n)⁻¹

/-- The coefficient in (4.4.2.6) exists on the actual Schwartz–Bruhat space
of the cyclic quotient. With the manuscript's Weil Haar measure of mass
L times the norm-one volume, the denominator is that product.
Adapted from mccorvie/riemann-masullo, commit 2207861 (Apache-2.0). -/
theorem modulatedCyclicFourierCoeff_apply
    (μ : G →ₜ* Multiplicative ℝ) (hproper : IsProperMap μ)
    (γ : G) (hγ : 0 < Multiplicative.toAdd (μ γ))
    [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
    [MeasurableSpace (G ⧸ Subgroup.zpowers γ)] [BorelSpace (G ⧸ Subgroup.zpowers γ)]
    (ν : Measure (G ⧸ Subgroup.zpowers γ)) [IsFiniteMeasureOnCompacts ν]
    (χ : CircleCharacter G) (n : ℤ) (f : BruhatSchwartz (G ⧸ Subgroup.zpowers γ)) :
    let ψ : PontryaginDual (G ⧸ Subgroup.zpowers γ) := modulatedCyclicCharacter μ γ hγ χ n
    Integrable (fun q ↦ f.val q * (ψ q : ℂ)) ν ∧
      modulatedCyclicFourierCoeff μ γ hγ ν χ n f =
        (ν.real univ)⁻¹ * ∫ q, f.val q * (ψ q : ℂ) ∂ν := by
  intro ψ
  letI := modulatedCyclicQuotient_compact μ hproper γ hγ
  have hf : Continuous f.val := by
    obtain ⟨p, u, hu⟩ := f.property
    rw [← hu]
    exact (p.realize_smooth u 0).continuous
  have hψ : Continuous (fun q ↦ (ψ q : ℂ)) := continuous_subtype_val.comp ψ.continuous
  refine ⟨(hf.mul hψ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  unfold modulatedCyclicFourierCoeff lcaFourier
  rw [integral_smul_measure]
  change (ν univ)⁻¹.toReal • (∫ q, f.val q * star (ψ⁻¹ q : ℂ) ∂ν) = _
  have heq : (fun q ↦ f.val q * star (ψ⁻¹ q : ℂ)) = fun q ↦ f.val q * (ψ q : ℂ) := by
    funext q
    change f.val q * star (((ψ q)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  rw [heq]
  simp only [ENNReal.toReal_inv, Complex.real_smul, measureReal_def]

section QuotientHaar

open Function Topology
open scoped ENNReal NNReal

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
private theorem modulatedLog_mul_zpow (m : G →ₜ* Multiplicative ℝ) (γ x : G) (n : ℤ) :
    modulatedLog m (x * γ ^ n) = modulatedLog m x + n • modulatedLog m γ := by
  simp only [modulatedLog, map_mul, map_zpow, toAdd_mul, toAdd_zpow]

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
/-- A cyclic subgroup with nonzero log period is discrete. -/
theorem modulatedCyclicSubgroup_discrete (m : G →ₜ* Multiplicative ℝ) (γ : G)
    (hγ : 0 < modulatedLog m γ) : DiscreteTopology (Subgroup.zpowers γ) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  let f : (Subgroup.zpowers γ) → ℝ := fun x ↦ modulatedLog m x.val
  have hf : Continuous f := (continuous_toAdd.comp m.continuous).comp continuous_subtype_val
  have he : f ⁻¹' Ioo (-modulatedLog m γ) (modulatedLog m γ) = {1} := by
    ext x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
    have hfx : f x = (n : ℝ) * modulatedLog m γ := by
      change modulatedLog m x.val = _
      rw [← hn, ← one_mul (γ ^ n), modulatedLog_mul_zpow]
      simp [modulatedLog, zsmul_eq_mul]
    rw [mem_preimage, mem_Ioo, hfx, mem_singleton_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      have hlow : (-1 : ℝ) < n :=
        lt_of_mul_lt_mul_right (by simpa using h₁) hγ.le
      have hhigh : (n : ℝ) < 1 :=
        lt_of_mul_lt_mul_right (by simpa using h₂) hγ.le
      have hn₁ : -1 < n := by exact_mod_cast hlow
      have hn₂ : n < 1 := by exact_mod_cast hhigh
      have hn₀ : n = 0 := by omega
      apply Subtype.ext
      simpa [hn₀] using hn.symm
    · intro hx
      have hfx₀ : f x = 0 := hx ▸ (by simp [f, modulatedLog])
      rw [← hfx, hfx₀]
      exact ⟨neg_lt_zero.mpr hγ, hγ⟩
  exact he ▸ isOpen_Ioo.preimage hf

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in
/-- Every coset meets the half-open log strip of width one period in exactly one point. -/
theorem modulatedCyclicStrip_unique (m : G →ₜ* Multiplicative ℝ) (γ : G)
    (hγ : 0 < modulatedLog m γ) (x : G) :
    ∃! h : (Subgroup.zpowers γ), modulatedLog m (x * h.val) ∈ Ico 0 (modulatedLog m γ) := by
  let n := toIcoDiv hγ 0 (modulatedLog m x)
  refine ⟨⟨γ ^ (-n), Subgroup.zpow_mem_zpowers γ _⟩, ?_, ?_⟩
  · change modulatedLog m (x * γ ^ (-n)) ∈ _
    rw [modulatedLog_mul_zpow, neg_zsmul, ← sub_eq_add_neg]
    simpa only [zero_add] using (sub_toIcoDiv_zsmul_mem_Ico hγ 0 (modulatedLog m x))
  · intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.property
    change modulatedLog m (x * h.val) ∈ _ at hh
    rw [← hk, modulatedLog_mul_zpow] at hh
    have hk' : n = -k := toIcoDiv_eq_of_sub_zsmul_mem_Ico hγ (by
      simpa only [neg_zsmul, sub_neg_eq_add, zero_add] using hh)
    apply Subtype.ext
    simpa only [hk', neg_neg] using hk.symm

/-- The cyclic Weil quotient has total mass equal to the log period
times the Haar mass of the norm-one group. The half-open strip argument
is adapted from RiemannMasullo commit e87e7f0 (Apache-2.0). -/
theorem modulatedCyclicQuotient_measure_univ (m : G →ₜ* Multiplicative ℝ)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (γ : G) (hγ : 0 < modulatedLog m γ)
    (ρ : Measure m.toMonoidHom.ker) [ρ.IsHaarMeasure] [IsFiniteMeasure ρ]
    (ν : @Measure (G ⧸ (Subgroup.zpowers γ)) (borel _))
    (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) (modulatedLogMeasure m τ hτ ρ) Measure.count ν) :
    ν univ = ENNReal.ofReal (modulatedLog m γ) * ρ univ := by
  let Γ := Subgroup.zpowers γ
  letI : DiscreteTopology Γ := modulatedCyclicSubgroup_discrete m γ hγ
  letI : (Measure.count : Measure Γ).IsHaarMeasure := subgroup_count_isHaarMeasure Γ
  letI : (Measure.count : Measure Γ).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  let μ := modulatedLogMeasure m τ hτ ρ
  letI : μ.IsHaarMeasure := modulatedLogMeasure_isHaar m τ hτ ρ
  letI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  letI : MeasurableSpace (G ⧸ Γ) := borel _
  let Δ : Set G := {x | modulatedLog m x ∈ Ico 0 (modulatedLog m γ)}
  have hlog : Continuous (modulatedLog m) := continuous_toAdd.comp m.continuous
  have hΔ : MeasurableSet Δ := hlog.measurable measurableSet_Ico
  let κ (q : G ⧸ Γ) : Measure G :=
    (Measure.count : Measure Γ).map (fun h : Γ ↦ q.out * h.val)
  obtain ⟨hκ, hbind⟩ := weilMeasure_eq_bind Γ Γ.isClosed_of_discrete μ
    (Measure.count : Measure Γ) ν hν
  have hc (q : G ⧸ Γ) : κ q Δ = 1 := by
    let T (h : Γ) := q.out * h.val
    have hT : Measurable T := (continuous_const.mul continuous_subtype_val).measurable
    obtain ⟨h, hh, huniq⟩ := modulatedCyclicStrip_unique m γ hγ q.out
    have he : T ⁻¹' Δ = {h} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨hh, fun x hx ↦ huniq x hx⟩
    change Measure.count.map T Δ = _
    rw [Measure.map_apply hT hΔ, he, Measure.count_singleton]
  have hmass : μ Δ = ν univ := by
    rw [← hbind, Measure.bind_apply hΔ hκ.aemeasurable]
    change (∫⁻ q, κ q Δ ∂ν) = ν univ
    simp only [hc, lintegral_const, one_mul]
  rw [← hmass]
  change Measure.map (modulatedLogSplit m τ hτ) (volume.prod ρ) Δ = _
  rw [Measure.map_apply (modulatedLogSplit m τ hτ).continuous.measurable hΔ]
  have hpre : modulatedLogSplit m τ hτ ⁻¹' Δ =
      Ico 0 (modulatedLog m γ) ×ˢ (univ : Set m.toMonoidHom.ker) := by
    ext p
    have he : modulatedLog m (modulatedLogSplit m τ hτ p) = p.1 := by
      change Multiplicative.toAdd (m (τ (Multiplicative.ofAdd p.1) * p.2.val)) = p.1
      rw [map_mul, hτ, show m p.2.val = 1 from p.2.property, mul_one, toAdd_ofAdd]
    change modulatedLog m (modulatedLogSplit m τ hτ p) ∈ Ico 0 (modulatedLog m γ) ↔
      p ∈ Ico 0 (modulatedLog m γ) ×ˢ (univ : Set m.toMonoidHom.ker)
    rw [he]
    simp only [mem_prod, mem_univ, and_true]
  rw [hpre, Measure.prod_prod, Real.volume_Ico, sub_zero]

/-- Substituting the actual Weil quotient mass gives the normalization
of the coefficient in (4.4.2.6). -/
theorem modulatedCyclicFourierCoeff_weil_apply
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)
    (γ : G) (hγ : 0 < modulatedLog m γ)
    [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
    (ρ : Measure m.toMonoidHom.ker) [ρ.IsHaarMeasure] [IsFiniteMeasure ρ]
    (ν : @Measure (G ⧸ Subgroup.zpowers γ) (borel _))
    (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) (modulatedLogMeasure m τ hτ ρ)
      Measure.count ν)
    (χ : CircleCharacter G) (n : ℤ) (f : BruhatSchwartz (G ⧸ Subgroup.zpowers γ)) :
    letI : MeasurableSpace (G ⧸ Subgroup.zpowers γ) := borel _
    letI : BorelSpace (G ⧸ Subgroup.zpowers γ) := ⟨rfl⟩
    let ψ := modulatedCyclicCharacter m γ hγ χ n
    Integrable (fun q ↦ f.val q * (ψ q : ℂ)) ν ∧
      modulatedCyclicFourierCoeff m γ hγ ν χ n f =
        (modulatedLog m γ * ρ.real univ)⁻¹ * ∫ q, f.val q * (ψ q : ℂ) ∂ν := by
  dsimp only
  letI : MeasurableSpace (G ⧸ Subgroup.zpowers γ) := borel _
  letI : BorelSpace (G ⧸ Subgroup.zpowers γ) := ⟨rfl⟩
  letI : ν.IsHaarMeasure := hν.1
  have hmass : ν.real univ = modulatedLog m γ * ρ.real univ := by
    simp only [measureReal_def, modulatedCyclicQuotient_measure_univ m τ hτ γ hγ ρ ν hν,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ.le]
  rw [← hmass]
  exact modulatedCyclicFourierCoeff_apply m hm γ hγ ν χ n f

end QuotientHaar


section CompactFourier

variable {Q : Type*} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [T2Space Q] [LocallyCompactSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]

open Function Topology
open scoped ENNReal NNReal

private def compactBruhatFourierCoeffLinear (ν : Measure Q) [IsFiniteMeasure ν]
    (ψ : PontryaginDual Q) : BruhatSchwartz Q →ₗ[ℂ] ℂ := by
  let w (q : Q) := (ψ q : ℂ)
  have hw : Continuous w := continuous_subtype_val.comp ψ.continuous
  have hi (f : BruhatSchwartz Q) : Integrable (fun q ↦ f.val q * w q) ν :=
    ((bruhatSchwartz_continuous f).mul hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact
    { toFun := fun f ↦ (ν.real univ : ℂ)⁻¹ * ∫ q, f.val q * w q ∂ν
      map_add' := fun f g ↦ by
        change _ * (∫ q, (f.val q + g.val q) * w q ∂ν) = _
        simp_rw [add_mul]
        rw [integral_add (hi f) (hi g), mul_add]
      map_smul' := fun c f ↦ by
        change _ * (∫ q, (c * f.val q) * w q ∂ν) =
          c * (_ * ∫ q, f.val q * w q ∂ν)
        simp_rw [mul_assoc c]
        rw [integral_const_mul, mul_left_comm] }
set_option maxHeartbeats 4000000 in
private theorem compactBruhatFourierCoeffContinuous (ν : Measure Q) [IsFiniteMeasure ν]
    (ψ : PontryaginDual Q) : Continuous (compactBruhatFourierCoeffLinear ν ψ) := by
  let a := compactBruhatFourierCoeffLinear ν ψ
  apply (locallyConvexFinal_continuous_iff (fun p : BruhatSchwartzStage Q ↦ p.inclusion) a).mpr
  intro p
  change Continuous (a.comp p.inclusion)
  apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp
  intro i
  let s : Seminorm ℂ p.Space := elementarySchwartzSeminorm (m := p.2.realDim) (n := p.2.torusDim)
    (r := p.2.latticeRank) (F := p.2.finiteFactor) (0, 0, 0, 0)
  let C : ℝ≥0 := ⟨‖(ν.real univ : ℂ)⁻¹‖ * ν.real univ, by positivity⟩
  have hs : Continuous (fun u : p.Space ↦ s u) :=
    elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
  have hsC : Continuous (fun u : p.Space ↦ (C • s) u) := hs.const_smul C
  refine Seminorm.continuous_of_le (q := C • s) hsC fun u ↦ ?_
  change ‖(ν.real univ : ℂ)⁻¹ * ∫ q, p.realize u q * (ψ q : ℂ) ∂ν‖ ≤ C.val * s u
  rw [norm_mul, show C.val = ‖(ν.real univ : ℂ)⁻¹‖ * ν.real univ from rfl, mul_assoc,
    mul_comm (ν.real univ)]
  refine mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const
    (ae_of_all _ fun q ↦ ?_)) (norm_nonneg _)
  rw [norm_mul, Circle.norm_coe, mul_one]
  by_cases hq : q ∈ p.1.upper.val
  · let q' : p.1.upper.val := ⟨q, hq⟩
    let z := (p.1.stageCoordinates p.2 q').toAdd
    change ‖p.1.realizeSchwartz p.2 u q‖ ≤ s u
    rw [p.1.realizeSchwartz_apply_of_mem p.2 u q']
    have hb : (‖u z‖₊ : ENNReal) ≤ elementarySchwartzBound u.val (0, 0, 0, 0) := by
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun v ↦ (‖u v‖₊ : ENNReal)) z
    exact ENNReal.toReal_mono (u.property.2 (0, 0, 0, 0)).ne hb
  · change ‖p.1.realizeSchwartz p.2 u q‖ ≤ s u
    rw [p.1.realizeSchwartz_apply_of_not_mem p.2 u q hq, norm_zero]
    exact apply_nonneg s u

/-- The Fourier functional at a character on a compact group, divided by
the total mass of the given measure. -/
def compactBruhatFourierCoeff (ν : Measure Q) [IsFiniteMeasure ν]
    (ψ : PontryaginDual Q) : BruhatSchwartz Q →L[ℂ] ℂ :=
  ⟨compactBruhatFourierCoeffLinear ν ψ, compactBruhatFourierCoeffContinuous ν ψ⟩

@[simp] theorem compactBruhatFourierCoeff_apply (ν : Measure Q) [IsFiniteMeasure ν]
    (ψ : PontryaginDual Q) (f : BruhatSchwartz Q) :
    compactBruhatFourierCoeff ν ψ f =
      (ν.real univ : ℂ)⁻¹ * ∫ q, f.val q * (ψ q : ℂ) ∂ν := rfl

/-- A unitary character is a Schwartz–Bruhat test on a compact group. -/
def compactBruhatCharacter (ψ : PontryaginDual Q) : BruhatSchwartz Q := by
  refine ⟨fun q ↦ (ψ q : ℂ), ?_⟩
  exact bruhatSchwartz_mem_of_smooth_compactSupport
    (pontryaginDual_mem_bruhatSmooth ψ) (HasCompactSupport.of_compactSpace _)

/-- The normalized coefficient functionals and the inverse characters give
the biorthogonal system in the proof of Lemma 4.4.2.6. -/
theorem compactBruhatFourierCoeff_character (ν : Measure Q) [ν.IsHaarMeasure]
    [DecidableEq (PontryaginDual Q)] (ψ ξ : PontryaginDual Q) :
    compactBruhatFourierCoeff ν ψ (compactBruhatCharacter ξ⁻¹) =
      if ξ = ψ then 1 else 0 := by
  rw [compactBruhatFourierCoeff_apply]
  change (ν.real univ : ℂ)⁻¹ * (∫ q, ((ξ q)⁻¹ : Circle) * (ψ q : ℂ) ∂ν) = _
  simp_rw [Circle.coe_inv_eq_conj, ← Complex.star_def, integral_character_pair ν]
  have hν : (ν.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero
  by_cases h : ξ = ψ <;> simp [h, hν]

/-- The compact Fourier coordinates determine a Schwartz–Bruhat test. -/
theorem compactBruhatFourierCoeff_separate (ν : Measure Q) [ν.IsHaarMeasure]
    [ν.WeaklyRegular] (f : BruhatSchwartz Q)
    (hf : ∀ ψ, compactBruhatFourierCoeff ν ψ f = 0) : f = 0 := by
  have hfc := bruhatSchwartz_continuous f
  let g : C(Q, ℂ) := ⟨f.val, hfc⟩
  have hmem : MemLp f.val 2 ν := g.memLp (p := 2) ν ℂ
  apply Subtype.ext
  exact Measure.eq_of_ae_eq (ae_eq_zero_of_character_integral_eq_zero ν hmem fun χ ↦ by
    have h := hf χ⁻¹
    rw [compactBruhatFourierCoeff_apply] at h
    have hm : ((ν.real univ : ℂ)⁻¹) ≠ 0 :=
      inv_ne_zero (Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero)
    have h0 := (mul_eq_zero.mp h).resolve_left hm
    convert h0 using 1
    congr 1
    funext q
    change star (χ q : ℂ) * f.val q = f.val q * ((χ q)⁻¹ : Circle)
    rw [mul_comm, Circle.coe_inv_eq_conj, ← Complex.star_def])
    hfc continuous_const

end CompactFourier

/-- The cyclic coefficient in the basis problem is a continuous linear
functional, with the sign convention of the manuscript's conjugate exponential. -/
theorem modulatedCyclicFourierCoeff_eq_compact
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (m γ))
    [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
    [CompactSpace (G ⧸ Subgroup.zpowers γ)]
    [MeasurableSpace (G ⧸ Subgroup.zpowers γ)] [BorelSpace (G ⧸ Subgroup.zpowers γ)]
    (ν : Measure (G ⧸ Subgroup.zpowers γ)) [IsFiniteMeasure ν]
    (χ : CircleCharacter G) (n : ℤ) (f : BruhatSchwartz (G ⧸ Subgroup.zpowers γ)) :
    modulatedCyclicFourierCoeff m γ hγ ν χ n f =
      compactBruhatFourierCoeff ν (modulatedCyclicCharacter m γ hγ χ n) f := by
  refine Eq.trans ?_ (compactBruhatFourierCoeff_apply ν
    (modulatedCyclicCharacter m γ hγ χ n) f).symm
  unfold modulatedCyclicFourierCoeff lcaFourier
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_inv, measureReal_def, Complex.real_smul, Complex.ofReal_inv]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro q
  change _ * star (((modulatedCyclicCharacter m γ hγ χ n q)⁻¹ : Circle) : ℂ) = _
  rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  rfl




open Classical in
/-- Evaluation of the cyclic coefficient on an inverse quotient character. -/
theorem modulatedCyclicFourierCoeff_character
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (m γ))
    [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
    [CompactSpace (G ⧸ Subgroup.zpowers γ)]
    [MeasurableSpace (G ⧸ Subgroup.zpowers γ)] [BorelSpace (G ⧸ Subgroup.zpowers γ)]
    (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
    (χ : CircleCharacter G) (n : ℤ) (ξ : PontryaginDual (G ⧸ Subgroup.zpowers γ)) :
    modulatedCyclicFourierCoeff m γ hγ ν χ n (compactBruhatCharacter ξ⁻¹) =
      if ξ = modulatedCyclicCharacter m γ hγ χ n then 1 else 0 := by
  rw [modulatedCyclicFourierCoeff_eq_compact]
  exact compactBruhatFourierCoeff_character ν (modulatedCyclicCharacter m γ hγ χ n) ξ

/-- At a fixed norm-one character, every continuous Schwartz–Bruhat seminorm
of the cyclic exponential is bounded by a polynomial in the frequency. -/
theorem modulatedCyclicExponential_seminorm_polynomial
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (m γ))
    [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
    [CompactSpace (G ⧸ Subgroup.zpowers γ)]
    (χ : CircleCharacter G)
    (q : Seminorm ℂ (BruhatSchwartz (G ⧸ Subgroup.zpowers γ))) (hq : Continuous q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ,
      q (compactBruhatCharacter (modulatedCyclicCharacter m γ hγ χ n)⁻¹) ≤
        C * (1 + |(n : ℝ)|) ^ d := by
  let ξ (n : ℤ) : PontryaginDual (G ⧸ Subgroup.zpowers γ) :=
    modulatedCyclicCharacter m γ hγ χ n
  let a := (ξ 0)⁻¹
  let b := ((ξ 0)⁻¹ * ξ 1)⁻¹
  apply compactBruhatCharacter_line_polynomial a b q hq (fun n ↦ compactBruhatCharacter (ξ n)⁻¹)
  intro n x
  have h : ξ n = ξ 0 * ((ξ 0)⁻¹ * ξ 1) ^ n :=
    modulatedCyclicCharacter_line m γ hγ χ n
  have he : (ξ n)⁻¹ = a * b ^ n := by
    rw [h, mul_inv, ← inv_zpow]
  exact congrArg (fun c : PontryaginDual (G ⧸ Subgroup.zpowers γ) ↦ (c x : ℂ)) he

/-- Lemma 4.4.2.6(2b). At any fixed compact character, the values of a
continuous seminorm on the cyclic exponentials multiply integer
Schwartz–Bruhat tests into integer Schwartz–Bruhat tests. -/
theorem modulatedCyclicExponential_seminorm_multiplier
    (m : G →ₜ* Multiplicative ℝ) (γ : G) (hγ : 0 < Multiplicative.toAdd (m γ))
    [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
    [CompactSpace (G ⧸ Subgroup.zpowers γ)]
    (χ : CircleCharacter G)
    (q : Seminorm ℂ (BruhatSchwartz (G ⧸ Subgroup.zpowers γ))) (hq : Continuous q) :
    let u : ℤ → ℂ := fun n ↦
      (q (compactBruhatCharacter (modulatedCyclicCharacter m γ hγ χ n)⁻¹) : ℂ)
    Continuous u ∧ ∀ v : BruhatSchwartz (Multiplicative ℤ),
      (fun n : Multiplicative ℤ ↦ u n.toAdd * v.val n) ∈ bruhatSchwartzSubmodule := by
  dsimp only
  obtain ⟨C, hC, d, hd⟩ := modulatedCyclicExponential_seminorm_polynomial m γ hγ χ q hq
  refine ⟨continuous_of_discreteTopology, fun v ↦
    integerBruhat_mem_mul_of_polynomial
      (fun n ↦ (q (compactBruhatCharacter (modulatedCyclicCharacter m γ hγ χ n)⁻¹) : ℂ))
      hC (d := d) (fun n ↦ ?_) v⟩
  simpa only [Complex.norm_real, Real.norm_of_nonneg (apply_nonneg q _)] using hd n

end

end Masullo
