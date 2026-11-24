import BruhatCyclicPeriodizationCorollary
import ModulatedDecayIsotypes

open Function Set Topology MeasureTheory

namespace Masullo

noncomputable section

set_option maxHeartbeats 700000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "H" => G ⧸ Subgroup.zpowers γ
local notation "K" => m.toMonoidHom.ker

section QuotientInstances

variable [hT : T2Space (G ⧸ Subgroup.zpowers γ)]
  [hLC : LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]

/-- The norm-one isotype on the actual cyclic quotient. -/
def bruhatCyclicQuotientIsotype (ω : PontryaginDual K) : Submodule ℂ (BruhatSchwartz H) where
  carrier := {g | ∀ (a : K) y, g.val (QuotientGroup.mk (a.val⁻¹) * y) = (ω a : ℂ) * g.val y}
  zero_mem' := by intro a y; change (0 : ℂ) = (ω a : ℂ) * 0; rw [mul_zero]
  add_mem' {f g} hf hg a y := by
    change f.val _ + g.val _ = (ω a : ℂ) * (f.val y + g.val y)
    rw [hf, hg, mul_add]
  smul_mem' c f hf a y := by
    change c * f.val _ = (ω a : ℂ) * (c * f.val y)
    rw [hf, mul_left_comm]

omit [T2Space G] [LocallyCompactSpace G] in
theorem bruhatCyclicQuotientIsotype_isClosed (ω : PontryaginDual K) :
    IsClosed (bruhatCyclicQuotientIsotype m γ ω : Set (BruhatSchwartz H)) := by
  change IsClosed {g : BruhatSchwartz H | ∀ (a : K) y,
    g.val (QuotientGroup.mk (a.val⁻¹) * y) = (ω a : ℂ) * g.val y}
  rw [Set.ofPred_forall]
  refine isClosed_iInter fun a ↦ ?_
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun y ↦ isClosed_eq (bruhatSchwartz_continuous_eval _)
    (continuous_const.mul (bruhatSchwartz_continuous_eval y))

include hm hms hT hLC in
/-- A fixed cutoff section maps a quotient character isotype back to the
same isotype in the weighted decay space. -/
theorem exists_bruhatCyclic_weighted_isotypeSection
    (ω : PontryaginDual K) (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ S : bruhatCyclicQuotientIsotype m γ ω →L[ℂ] modulatedDecayIsotype m ω I,
      ∀ g, bruhatCyclicPeriodization m hm γ hγ hms
        (modulatedDecay_zeroInclusion m I h0 (S g).val) = g.val := by
  let P := bruhatCyclicPeriodization m hm γ hγ hms
  obtain ⟨b, hb, C, hC, hs, hS⟩ := exists_weightedCyclicPeriodization_cutoffSection m hm hms γ hγ
    P (bruhatCyclicPeriodization_apply m hm γ hγ hms) I h0
  let T := bruhatCyclicDecayCutoffLift m hm hms γ hγ I b hb C hC hs
  have hTval (g : BruhatSchwartz H) (x : G) : (T g).val x = b (m x).toAdd * g.val (QuotientGroup.mk x) :=
    bruhatCyclicCutoffLift_apply m hm hms γ hγ b hb C hC hs g x
  have hpres (g : bruhatCyclicQuotientIsotype m γ ω) : T g.val ∈ modulatedDecayIsotype m ω I := by
    intro a x
    have hma : m a.val = 1 := a.property
    have hlog : (m (a.val⁻¹ * x)).toAdd = (m x).toAdd := by rw [map_mul, map_inv, hma, inv_one, one_mul]
    rw [hTval, hTval, hlog, QuotientGroup.mk_mul, g.property a (QuotientGroup.mk x), mul_left_comm]
  exact ⟨(T.comp (bruhatCyclicQuotientIsotype m γ ω).subtypeL).codRestrict _ hpres, fun g ↦ hS g.val⟩

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (μ : Measure m.toMonoidHom.ker) [μ.IsHaarMeasure]
  (ω : PontryaginDual m.toMonoidHom.ker)

include hm in
omit [LocallyCompactSpace G] in
private theorem cyclicKernelAverage_eq_direct (f : G → ℂ) (x : G) :
    modulatedKernelAverage m μ ω f x = ∫ a : K, (ω a : ℂ) * f (a.val * x) ∂μ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (hm.isCompact_preimage
    (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  unfold modulatedKernelAverage
  have h := integral_inv_eq_self (fun a : K ↦ (ω a : ℂ) * f (a.val * x)) μ
  simpa only [map_inv, Subgroup.coe_inv] using h

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [BorelSpace m.toMonoidHom.ker] [μ.IsHaarMeasure] in
private theorem cyclicKernelAverage_isotype (f : G → ℂ)
    (hf : ∀ (a : K) x, f (a.val⁻¹ * x) = (ω a : ℂ) * f x) (x : G) :
    modulatedKernelAverage m μ ω f x = (μ.real univ : ℂ) * f x := by
  unfold modulatedKernelAverage
  calc
    _ = ∫ _ : K, f x ∂μ := by
      apply integral_congr_ae
      refine .of_forall fun a ↦ ?_
      change (((ω a)⁻¹ : Circle) : ℂ) * f (a.val⁻¹ * x) = f x
      rw [hf, ← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]
    _ = _ := by rw [integral_const, Complex.real_smul]

include hm in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [BorelSpace m.toMonoidHom.ker] in
private theorem cyclicKernel_haar_mass_ne_zero : (μ.real univ : ℂ) ≠ 0 := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (hm.isCompact_preimage
    (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  exact_mod_cast (ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 (NeZero.ne μ))
    (measure_ne_top μ univ)).ne'

include hm hms hT hLC in
/-- The Haar-character-averaged periodization is an open surjection onto
the closed character isotype of the cyclic quotient. On the source
isotype it is ordinary periodization times the mass of the kernel Haar. -/
theorem exists_bruhatCyclic_homogeneousPeriodization (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ T : ModulatedExponentialInductive m I →L[ℂ] bruhatCyclicQuotientIsotype m γ ω,
      IsOpenMap T ∧ Surjective T ∧
      (∀ f x, HasSum (fun n : ℤ ↦ ∫ a : K, (ω a : ℂ) * f.val (a.val * (γ ^ n * x)) ∂μ)
        ((T f).val.val (QuotientGroup.mk x))) ∧
      ∀ f ∈ modulatedDecayIsotype m ω I,
        (T f).val = (μ.real univ : ℂ) • bruhatCyclicPeriodization m hm γ hγ hms
          (modulatedDecay_zeroInclusion m I h0 f) := by
  let E := ModulatedExponentialInductive m I
  let V := bruhatCyclicQuotientIsotype m γ ω
  let J := modulatedDecay_zeroInclusion m I h0
  let P := bruhatCyclicPeriodization m hm γ hγ hms
  let A := modulatedDecay_kernelAverage m μ ω I hm hms ⟨0, h0⟩
  let F := P.comp (J.comp A)
  have hP := bruhatCyclicPeriodization_apply m hm γ hγ hms
  have hpres (f : E) : F f ∈ V :=
    bruhatCyclicPeriodization_isotypic m γ hγ P hP ω (J (A f))
      (modulatedKernelAverage_eigen m μ ω f.val)
  let T : E →L[ℂ] V := F.codRestrict V hpres
  have hiso (f : E) (hf : f ∈ modulatedDecayIsotype m ω I) :
      (T f).val = (μ.real univ : ℂ) • P (J f) := by
    have hAf : A f = (μ.real univ : ℂ) • f :=
      ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext (funext fun x ↦ by
        change modulatedKernelAverage m μ ω f.val x = _
        exact cyclicKernelAverage_isotype m μ ω f.val hf x))
    change P (J (A f)) = _
    rw [hAf, map_smul, map_smul]
  obtain ⟨S, hS⟩ := exists_bruhatCyclic_weighted_isotypeSection m hm hms γ hγ ω I h0
  let S₀ : V →L[ℂ] E := (μ.real univ : ℂ)⁻¹ • ((modulatedDecayIsotype m ω I).subtypeL.comp S)
  have hn := cyclicKernel_haar_mass_ne_zero m hm μ
  have hright (g : V) : T (S₀ g) = g := by
    apply Subtype.ext
    change (T ((μ.real univ : ℂ)⁻¹ • (S g).val)).val = g.val
    rw [map_smul]
    change (μ.real univ : ℂ)⁻¹ • (T (S g).val).val = g.val
    rw [hiso _ (S g).property, hS g, smul_smul, inv_mul_cancel₀ hn, one_smul]
  letI : IsTopologicalAddGroup E :=
    (PolynormableSpace.withSeminorms ℂ _).topologicalAddGroup
  letI : IsTopologicalAddGroup (BruhatSchwartz H) :=
    (PolynormableSpace.withSeminorms ℂ _).topologicalAddGroup
  have hopen : IsOpenMap T := by
    apply IsOpenMap.of_sections
    intro y
    let q (g : V) : V := ⟨g.val - (T y).val, V.sub_mem g.property (T y).property⟩
    have hq : Continuous q :=
      (continuous_subtype_val.sub continuous_const).subtype_mk _
    have hqy : q (T y) = 0 := Subtype.ext (sub_self _)
    let U (g : V) := y + S₀ (q g)
    refine ⟨U, (continuous_const.add (S₀.continuous.comp hq)).continuousAt, ?_, ?_⟩
    · change y + S₀ (q (T y)) = y
      rw [hqy, map_zero, add_zero]
    · intro g
      change T (y + S₀ (q g)) = g
      rw [map_add, hright]
      apply Subtype.ext
      change (T y).val + (g.val - (T y).val) = g.val
      abel
  refine ⟨T, hopen, fun g ↦ ⟨S₀ g, hright g⟩, ?_, hiso⟩
  intro f x
  have he := hP (J (A f)) x
  have hf := (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ (J (A f)) x).of_norm.hasSum
  have hEq (n : ℤ) : (J (A f)).val (γ ^ n * x) =
      ∫ a : K, (ω a : ℂ) * f.val (a.val * (γ ^ n * x)) ∂μ :=
    cyclicKernelAverage_eq_direct m hm μ ω f.val _
  change HasSum _ ((P (J (A f))).val (QuotientGroup.mk x))
  rw [he, bruhatSchwartz_cyclicOrbitSum_apply]
  simpa only [hEq] using hf

omit [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker] in
private theorem modulatedDecayIsotype_isClosed_zeroWeight
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    IsClosed (modulatedDecayIsotype m ω I : Set (ModulatedExponentialInductive m I)) := by
  change IsClosed {f : ModulatedExponentialInductive m I | ∀ (a : K) x,
    f.val (a.val⁻¹ * x) = (ω a : ℂ) * f.val x}
  let J := modulatedDecay_zeroInclusion m I h0
  rw [Set.ofPred_forall]
  refine isClosed_iInter fun a ↦ ?_
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_eq
    ((bruhatSchwartz_continuous_eval (a.val⁻¹ * x)).comp J.continuous)
    (continuous_const.mul ((bruhatSchwartz_continuous_eval x).comp J.continuous))

end QuotientInstances

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (μ : Measure m.toMonoidHom.ker) [μ.IsHaarMeasure]
  (ω : PontryaginDual m.toMonoidHom.ker)

include hm hms in
/-- Proposition 4.5.1.1, pp. 197–198, in logarithmic modulus coordinates.
The homogeneous map uses the prescribed Haar measure, with its mass
retained in the relation to ordinary periodization. -/
theorem bruhatCyclicPeriodization_proposition :
    letI : IsClosed ((Subgroup.zpowers γ : Subgroup G) : Set G) := modulatedCyclicSubgroup_isClosed m γ hγ
    let V := bruhatCyclicQuotientIsotype m γ ω
    let U := modulatedDecayIsotype m ω univ
    let Δ := modulatedDecay_cyclicDifference m hm hms γ univ (mem_univ 0)
    ∃ (E : ModulatedExponentialInductive m univ →L[ℂ] BruhatSchwartz H)
      (T : ModulatedExponentialInductive m univ →L[ℂ] V),
      Surjective E ∧ IsOpenMap T ∧ Surjective T ∧
      IsClosed (U : Set (ModulatedExponentialInductive m univ)) ∧
      E '' (U : Set (ModulatedExponentialInductive m univ)) = (V : Set (BruhatSchwartz H)) ∧
      IsClosed (V : Set (BruhatSchwartz H)) ∧
      (∀ f x, HasSum (fun n : ℤ ↦ f.val (γ ^ n * x)) ((E f).val (QuotientGroup.mk x))) ∧
      (∀ f x, HasSum (fun n : ℤ ↦ ∫ a : K, (ω a : ℂ) * f.val (a.val * (γ ^ n * x)) ∂μ)
        ((T f).val.val (QuotientGroup.mk x))) ∧
      E.ker = Δ.range ∧ IsClosed (Δ.range : Set (ModulatedExponentialInductive m univ)) ∧
      (∀ f ∈ U, T f = 0 ↔ ∃ v ∈ U, Δ v = f) := by
  letI : IsClosed ((Subgroup.zpowers γ : Subgroup G) : Set G) := modulatedCyclicSubgroup_isClosed m γ hγ
  intro V U Δ
  let P := bruhatCyclicPeriodization m hm γ hγ hms
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  let E := P.comp J
  have hP := bruhatCyclicPeriodization_apply m hm γ hγ hms
  have hE (f : ModulatedExponentialInductive m univ) (x : G) :
      (E f).val (QuotientGroup.mk x) = bruhatSchwartz_cyclicOrbitSum m γ hγ x (J f) := hP (J f) x
  obtain ⟨R, hR⟩ := exists_weightedCyclicPeriodization_section m hm hms γ hγ P hP univ (mem_univ 0)
  obtain ⟨S, hS⟩ := exists_bruhatCyclic_weighted_isotypeSection m hm hms γ hγ ω univ (mem_univ 0)
  obtain ⟨T, hTo, hTs, hT, hTiso⟩ :=
    exists_bruhatCyclic_homogeneousPeriodization m hm hms γ hγ μ ω univ (mem_univ 0)
  have hker : E.ker = Δ.range := modulatedDecay_periodization_ker m hm hms γ hγ univ (mem_univ 0) E hE
  have hEiso : E '' (U : Set (ModulatedExponentialInductive m univ)) = (V : Set (BruhatSchwartz H)) := by
    apply subset_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      exact bruhatCyclicPeriodization_isotypic m γ hγ P hP ω (J f) hf
    · intro g hg
      exact ⟨(S ⟨g, hg⟩).val, (S ⟨g, hg⟩).property, hS ⟨g, hg⟩⟩
  refine ⟨E, T, fun g ↦ ⟨R g, hR g⟩, hTo, hTs, modulatedDecayIsotype_isClosed_zeroWeight m ω univ
    (mem_univ 0), hEiso, bruhatCyclicQuotientIsotype_isClosed m γ ω, ?_, hT, hker, ?_, ?_⟩
  · intro f x
    rw [hE, bruhatSchwartz_cyclicOrbitSum_apply]
    exact (bruhatSchwartz_cyclicOrbit_summable_norm m γ hγ (J f) x).of_norm.hasSum
  · letI : T2Space (BruhatSchwartz H) := bruhatSchwartz_t2
    rw [← hker]
    exact E.isClosed_ker
  · intro f hf
    have he : T f = 0 ↔ E f = 0 := by
      constructor
      · intro h
        have hh : (T f).val = 0 := congrArg Subtype.val h
        rw [hTiso f hf] at hh
        exact (smul_eq_zero.mp hh).resolve_left (cyclicKernel_haar_mass_ne_zero m hm μ)
      · intro h
        apply Subtype.ext
        change (T f).val = 0
        rw [hTiso f hf]
        change (μ.real univ : ℂ) • E f = 0
        rw [h, smul_zero]
    exact he.trans ((modulatedDecay_periodization_isotypic_ker m hm hms γ hγ univ
      (mem_univ 0) E hE ω f hf).trans (by
        constructor
        · rintro ⟨v, hv, hvi⟩
          exact ⟨v, hvi, hv⟩
        · rintro ⟨v, hvi, hv⟩
          exact ⟨v, hv, hvi⟩))

end

end Masullo
