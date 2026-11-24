import BruhatSupportedWindow
import BruhatCyclicFactorization
import CyclicFourierWeilPairing
import CyclicQuotientBasisTransport

open Function Set Topology MeasureTheory

namespace Masullo

noncomputable section

set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 8

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
variable (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "Q" => G ⧸ Subgroup.zpowers γ
local notation "E" => ModulatedExponentialInductive m univ
local notation "K" => m.toMonoidHom.ker

variable [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]
  [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
variable (ρ : Measure m.toMonoidHom.ker) [ρ.IsHaarMeasure]
  (ω : PontryaginDual m.toMonoidHom.ker)
variable (T : ModulatedExponentialInductive m univ →L[ℂ] bruhatCyclicQuotientIsotype m γ ω)
variable (hT : ∀ f x, HasSum (fun n : ℤ ↦ ∫ a : m.toMonoidHom.ker, (ω a : ℂ) *
    f.val (a.val * (γ ^ n * x)) ∂ρ) ((T f).val.val (QuotientGroup.mk x)))

include hT in
/-- On an isotypic source, the homogeneous orbit formula is ordinary
periodization multiplied by the kernel Haar mass. -/
theorem bruhatHomogeneousPeriodization_apply_of_isotype
    (f : E) (hf : f ∈ modulatedDecayIsotype m ω univ) :
    (T f).val = (ρ.real univ : ℂ) • bruhatCyclicPeriodization m hm γ hγ hms
      (modulatedDecay_zeroInclusion m univ (mem_univ 0) f) := by
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  let A := modulatedDecay_kernelAverage m ρ ω univ hm hms ⟨0, mem_univ 0⟩
  have hAf : A f = (ρ.real univ : ℂ) • f :=
    ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext (funext fun x ↦ by
      change modulatedKernelAverage m ρ ω f.val x = (ρ.real univ : ℂ) * f.val x
      unfold modulatedKernelAverage
      calc
        _ = ∫ _ : K, f.val x ∂ρ := by
          apply integral_congr_ae
          refine .of_forall fun a ↦ ?_
          change (((ω a)⁻¹ : Circle) : ℂ) * f.val (a.val⁻¹ * x) = f.val x
          rw [hf a x, ← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]
        _ = _ := by rw [integral_const, Complex.real_smul]))
  have he := cyclicFourier_homogeneous_eq_periodize_average m hm hms γ hγ ρ ω T hT f
  change (T f).val = bruhatCyclicPeriodization m hm γ hγ hms (J (A f)) at he
  rw [he, hAf, map_smul, map_smul]

include hm hms hγ hT in
/-- A logarithmic cutoff gives a continuous supported section of
homogeneous periodization. Every lifted test is invariant under a norm-one
subgroup on which the character is trivial. -/
theorem exists_bruhatSupportedHomogeneous_section
    (W : Set ℝ) (hW : IsCompact W)
    (hcov : ∀ x : ℝ, ∃ j : ℤ, x + (m γ).toAdd * (j : ℝ) ∈ interior W)
    (L : Subgroup G) (hL : L ≤ K)
    (hω : ∀ l : L, ω ⟨l.val, hL l.property⟩ = 1) :
    let U := bruhatSupportedInvariant m L ((fun x ↦ (m x).toAdd) ⁻¹' W)
    ∃ S : bruhatCyclicQuotientIsotype m γ ω →L[ℂ] U,
      RightInverse S (T.comp U.subtypeL) := by
  dsimp only
  let U := bruhatSupportedInvariant m L ((fun x ↦ (m x).toAdd) ⁻¹' W)
  let V := bruhatCyclicQuotientIsotype m γ ω
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  let B := bruhatCyclicPeriodization m hm γ hγ hms
  obtain ⟨c, hc, hs, hS⟩ := exists_weightedCyclicPeriodization_cutoffSection_of_cover
    m hm hms γ hγ B (bruhatCyclicPeriodization_apply m hm γ hγ hms) W hW hcov univ (mem_univ 0)
  let R := bruhatCyclicDecayCutoffLift m hm hms γ hγ univ c hc W hW hs
  have hval (v : V) (x : G) : (R v.val).val x = c (m x).toAdd * v.val.val (QuotientGroup.mk x) :=
    bruhatCyclicCutoffLift_apply m hm hms γ hγ c hc W hW hs v.val x
  have hiso (v : V) : R v.val ∈ modulatedDecayIsotype m ω univ := by
    intro k x
    have hk : m k.val = 1 := k.property
    have hlog : (m (k.val⁻¹ * x)).toAdd = (m x).toAdd := by rw [map_mul, map_inv, hk, inv_one, one_mul]
    rw [hval, hval, hlog, QuotientGroup.mk_mul, v.property k (QuotientGroup.mk x), mul_left_comm]
  have hU (v : V) : R v.val ∈ U := by
    refine ⟨fun x hx ↦ ?_, fun k x ↦ ?_⟩
    · by_contra h
      have hz : c (m x).toAdd = 0 := notMem_support.mp fun hc' ↦ h (hs hc')
      exact hx ((hval v x).trans (by rw [hz, zero_mul]))
    · have he := hiso v ⟨k.val, hL k.property⟩ x
      simpa only [hω k, Circle.coe_one, one_mul] using he
  let R₀ := (R.comp V.subtypeL).codRestrict U hU
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  let d : ℂ := ρ.real univ
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_ne_zero
  refine ⟨d⁻¹ • R₀, fun v ↦ ?_⟩
  have hTval : (T (R v.val)).val = d • v.val :=
    (bruhatHomogeneousPeriodization_apply_of_isotype m hm hms γ hγ ρ ω T hT _ (hiso v)).trans
      (congrArg (d • ·) (hS v.val))
  apply Subtype.ext
  change (T (d⁻¹ • R v.val)).val = v.val
  rw [map_smul]
  change d⁻¹ • (T (R v.val)).val = v.val
  rw [hTval, smul_smul, inv_mul_cancel₀ hd, one_smul]

include hT in
/-- Homogeneous periodization annihilates all subgroup-invariant tests
if the character is nontrivial on that subgroup. -/
theorem bruhatHomogeneousPeriodization_eq_zero_of_invariant
    (L : Subgroup G) (hL : L ≤ K)
    (l : L) (hl : ω ⟨l.val, hL l.property⟩ ≠ 1)
    (f : E) (hf : ∀ (k : L) x, f.val (k.val⁻¹ * x) = f.val x) : T f = 0 := by
  let k : K := ⟨l.val, hL l.property⟩
  have hχ : (ω k : ℂ) ≠ 1 :=
    fun he ↦ hl (Subtype.ext (he.trans Circle.coe_one.symm))
  have hleft (x : G) : f.val (l.val * x) = f.val x := by
    simpa only [Subgroup.coe_inv, inv_inv] using hf l⁻¹ x
  have hI (y : G) : ∫ a : K, (ω a : ℂ) * f.val (a.val * y) ∂ρ = 0 := by
    let F (a : K) := (ω a : ℂ) * f.val (a.val * y)
    have hp (a : K) : F (k * a) = (ω k : ℂ) * F a := by
      change (ω (k * a) : ℂ) * f.val ((l.val * a.val) * y) = _
      rw [map_mul, Circle.coe_mul]
      have hval : f.val ((l.val * a.val) * y) = f.val (a.val * y) :=
        (congrArg f.val (mul_assoc l.val a.val y)).trans (hleft (a.val * y))
      exact (congrArg ((ω k : ℂ) * (ω a : ℂ) * ·) hval).trans (mul_assoc _ _ _)
    have he : ∫ a : K, F a ∂ρ = (ω k : ℂ) * ∫ a : K, F a ∂ρ := by
      calc
        _ = ∫ a : K, F (k * a) ∂ρ := (integral_mul_left_eq_self (μ := ρ) F k).symm
        _ = ∫ a : K, (ω k : ℂ) * F a ∂ρ := integral_congr_ae (.of_forall hp)
        _ = _ := integral_const_mul _ _
    have hz : (1 - (ω k : ℂ)) * ∫ a : K, F a ∂ρ = 0 := by
      rw [sub_mul, one_mul, ← he, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχ.symm)
  apply Subtype.ext
  apply Subtype.ext
  funext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have ht : HasSum (fun _ : ℤ ↦ (0 : ℂ)) ((T f).val.val (QuotientGroup.mk x)) :=
    (hT f x).congr_fun fun n ↦ (hI (γ ^ n * x)).symm
  exact ht.unique hasSum_zero

include hm hms hγ hT in
/-- The support cutoff comparison commutes with restriction to invariant
tests. For a nontrivial restriction of the character, both kernel
quotients consist of zero alone. -/
theorem bruhatSupportedHomogeneous_invariantQuotient
    (W : Set ℝ) (hW : IsCompact W)
    (hcov : ∀ x : ℝ, ∃ j : ℤ, x + (m γ).toAdd * (j : ℝ) ∈ interior W)
    (L : Subgroup G) (hL : L ≤ K) :
    let U := bruhatSupportedInvariant m L ((fun x ↦ (m x).toAdd) ⁻¹' W)
    let F := bruhatSupportedInvariant m L univ
    let T₀ := T.comp U.subtypeL
    let T₁ := T.comp F.subtypeL
    ∃ e : (U ⧸ T₀.ker) ≃L[ℂ] (F ⧸ T₁.ker),
      ∀ u : U, e (T₀.ker.mkQ u) = T₁.ker.mkQ ⟨u.val, subset_univ _, u.property.2⟩ := by
  classical
  dsimp only
  let U := bruhatSupportedInvariant m L ((fun x ↦ (m x).toAdd) ⁻¹' W)
  let F := bruhatSupportedInvariant m L univ
  let V := bruhatCyclicQuotientIsotype m γ ω
  let T₀ : U →L[ℂ] V := T.comp U.subtypeL
  let T₁ : F →L[ℂ] V := T.comp F.subtypeL
  let i : U →L[ℂ] F :=
    ⟨Submodule.inclusion (fun _ hu ↦ ⟨subset_univ _, hu.2⟩),
      continuous_subtype_val.subtype_mk _⟩
  by_cases hχ : ∀ l : L, ω ⟨l.val, hL l.property⟩ = 1
  · letI : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
    letI : ContinuousSMul ℂ (BruhatSchwartz Q) :=
      (PolynormableSpace.withSeminorms ℂ (BruhatSchwartz Q)).continuousSMul
    obtain ⟨S, hS⟩ := exists_bruhatSupportedHomogeneous_section m hm hms γ hγ
      ρ ω T hT W hW hcov L hL hχ
    have hiS : RightInverse (i.comp S) T₁ := hS
    obtain ⟨e₀, he₀⟩ := splitQuotientEquiv_scaled (X := ↥U) (Y := ↥V) T₀ S hS 1 one_ne_zero
    obtain ⟨e₁, he₁⟩ := splitQuotientEquiv_scaled (X := ↥F) (Y := ↥V) T₁ (i.comp S)
      hiS 1 one_ne_zero
    refine ⟨e₀.trans e₁.symm, fun u ↦ e₁.injective ?_⟩
    change e₁ (e₁.symm (e₀ (T₀.ker.mkQ u))) = e₁ (T₁.ker.mkQ (i u))
    exact (e₁.apply_symm_apply _).trans ((he₀ u).trans (he₁ (i u)).symm)
  · obtain ⟨l, hl⟩ := not_forall.mp hχ
    have hzero (f : E) (hf : ∀ (k : L) x, f.val (k.val⁻¹ * x) = f.val x) : T f = 0 :=
      bruhatHomogeneousPeriodization_eq_zero_of_invariant m γ ρ ω T hT L hL l hl f hf
    have h₀ : T₀.ker = ⊤ := top_unique fun u _ ↦ hzero u.val u.property.2
    have h₁ : T₁.ker = ⊤ := top_unique fun u _ ↦ hzero u.val u.property.2
    letI : Subsingleton (U ⧸ T₀.ker) := Submodule.Quotient.subsingleton_iff.mpr h₀
    letI : Subsingleton (F ⧸ T₁.ker) := Submodule.Quotient.subsingleton_iff.mpr h₁
    let e : (U ⧸ T₀.ker) ≃ₗ[ℂ] (F ⧸ T₁.ker) := LinearEquiv.ofSubsingleton _ _
    have he : Continuous e :=
      (continuous_const (y := (0 : F ⧸ T₁.ker))).congr fun _ ↦ Subsingleton.elim _ _
    have he' : Continuous e.symm :=
      (continuous_const (y := (0 : U ⧸ T₀.ker))).congr fun _ ↦ Subsingleton.elim _ _
    exact ⟨⟨e, he, he'⟩, fun _ ↦ Subsingleton.elim _ _⟩

end

end Masullo
