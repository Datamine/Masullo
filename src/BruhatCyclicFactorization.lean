import BruhatCyclicPeriodizationLift
import BruhatDecayRestriction

open Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section

set_option maxHeartbeats 1500000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "H" => G ⧸ Subgroup.zpowers γ

variable [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]

variable (P : BruhatSchwartz G →L[ℂ] BruhatSchwartz (G ⧸ Subgroup.zpowers γ))
variable (hP : ∀ (f : BruhatSchwartz G) (x : G), (P f).val (QuotientGroup.mk x) = bruhatSchwartz_cyclicOrbitSum m γ hγ x f)

include hm hms hP in
/-- If the ordinary orbit sums define a continuous map into the cyclic
quotient, its interval-weighted extension is continuous and surjective. -/
theorem exists_weightedCyclicPeriodization (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ T : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz H,
      Surjective T ∧ ∀ f, T f = P (modulatedDecay_zeroInclusion m I h0 f) := by
  let T := P.comp (modulatedDecay_zeroInclusion m I h0)
  refine ⟨T, ?_, fun _ ↦ rfl⟩
  intro g
  obtain ⟨f, _, hf⟩ := exists_bruhatCyclic_entireDecay_periodization_lift m hm hms γ hγ g
  let f' := modulatedDecay_restrict m (subset_univ I) f
  have hf' : modulatedDecay_zeroInclusion m I h0 f' = modulatedDecay_zeroInclusion m univ (mem_univ 0) f :=
    Subtype.ext (modulatedDecay_restrict_apply m (subset_univ I) f)
  have he (x : G) : (P (modulatedDecay_zeroInclusion m I h0 f')).val (QuotientGroup.mk x) =
      g.val (QuotientGroup.mk x) :=
    (hP _ x).trans ((congrArg (bruhatSchwartz_cyclicOrbitSum m γ hγ x) hf').trans (hf x))
  exact ⟨f', Subtype.ext (funext fun y ↦ QuotientGroup.induction_on y he)⟩

include hm hms hP in
/-- The weighted periodization uniquely extends the entire-decay periodization
along the canonical restriction of abscissae. -/
theorem exists_weightedCyclicPeriodization_factorization (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ (T : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz H)
      (E : ModulatedExponentialInductive m univ →L[ℂ] BruhatSchwartz H),
      Surjective T ∧ Surjective E ∧
      (∀ f, T f = P (modulatedDecay_zeroInclusion m I h0 f)) ∧
      (∀ f, E f = P (modulatedDecay_zeroInclusion m univ (mem_univ 0) f)) ∧
      (∀ f, T (modulatedDecay_restrict m (subset_univ I) f) = E f) ∧
      ∀ T' : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz H,
        (∀ f, T' (modulatedDecay_restrict m (subset_univ I) f) = E f) → T' = T := by
  obtain ⟨T, hTs, hT⟩ := exists_weightedCyclicPeriodization m hm hms γ hγ P hP I h0
  obtain ⟨E, hEs, hE⟩ := exists_weightedCyclicPeriodization m hm hms γ hγ P hP univ (mem_univ 0)
  have he (f : ModulatedExponentialInductive m (univ : Set ℝ)) :
      T (modulatedDecay_restrict m (subset_univ I) f) = E f := by
    have hEq : modulatedDecay_zeroInclusion m I h0 (modulatedDecay_restrict m (subset_univ I) f) =
        modulatedDecay_zeroInclusion m univ (mem_univ 0) f :=
      Subtype.ext (modulatedDecay_restrict_apply m (subset_univ I) f)
    exact (hT _).trans ((congrArg P hEq).trans (hE f).symm)
  refine ⟨T, E, hTs, hEs, hT, hE, he, fun T' hT' ↦ ?_⟩
  letI : T2Space (BruhatSchwartz H) := bruhatSchwartz_t2
  apply DFunLike.coe_injective
  exact modulatedDecay_continuous_eq_of_entireDecay m hm hms I ⟨0, h0⟩ T'.continuous T.continuous
    (fun f ↦ (hT' f).trans (he f).symm)

include hm hms hP in
/-- A compact logarithmic window supports a continuous cutoff section when
its interior meets every orbit of the logarithmic period. -/
theorem exists_weightedCyclicPeriodization_cutoffSection_of_cover
    (K : Set ℝ) (hK : IsCompact K)
    (hcov : ∀ x : ℝ, ∃ n : ℤ, x + (m γ).toAdd * (n : ℝ) ∈ interior K)
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hbs : support b ⊆ K),
      RightInverse
        (bruhatCyclicDecayCutoffLift m hm hms γ hγ I b hb K hK hbs)
        (P.comp (modulatedDecay_zeroInclusion m I h0)) := by
  let d := (m γ).toAdd
  obtain ⟨b, hb, hbs, hper⟩ := integerPeriodization_extends_periodic hK hγ hcov
  let S := bruhatCyclicDecayCutoffLift m hm hms γ hγ I b hb K hK hbs
  refine ⟨b, hb, hbs, fun g ↦ Subtype.ext (funext fun y ↦ QuotientGroup.induction_on y fun x ↦ ?_)⟩
  let f := modulatedDecay_zeroInclusion m I h0 (S g)
  have hcut (z : G) : f.val z = b (m z).toAdd * g.val (QuotientGroup.mk z) :=
    bruhatCyclicCutoffLift_apply m hm hms γ hγ b hb K hK hbs g z
  have hlog (n : ℤ) : (m (γ ^ n * x)).toAdd = (m x).toAdd + d * (n : ℝ) := by
    simp only [map_mul, map_zpow, toAdd_mul, toAdd_zpow, zsmul_eq_mul, d]
    ring
  have hq (n : ℤ) : (QuotientGroup.mk (γ ^ n * x) : H) = QuotientGroup.mk x := by
    rw [QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 (Subgroup.zpow_mem_zpowers γ n), one_mul]
  change (P f).val (QuotientGroup.mk x) = _
  calc
    _ = bruhatSchwartz_cyclicOrbitSum m γ hγ x f := hP f x
    _ = ∑' n : ℤ, f.val (γ ^ n * x) := bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x f
    _ = ∑' n : ℤ, b ((m x).toAdd + d * (n : ℝ)) * g.val (QuotientGroup.mk x) :=
      tsum_congr fun n ↦ (hcut _).trans (congrArg₂ (· * ·) (congrArg b (hlog n))
        (congrArg g.val (hq n)))
    _ = _ := congrFun (hper (fun _ : ℝ ↦ g.val (QuotientGroup.mk x)) (fun _ ↦ rfl)) (m x).toAdd

include hm hms hP in
/-- A logarithmic window wider than one period supports a continuous
cutoff section of the weighted periodization. -/
theorem exists_weightedCyclicPeriodization_cutoffSection_on_window
    (a z : ℝ) (hwidth : a + (m γ).toAdd < z) (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hbs : support b ⊆ Icc a z),
      RightInverse
        (bruhatCyclicDecayCutoffLift m hm hms γ hγ I b hb (Icc a z) isCompact_Icc hbs)
        (P.comp (modulatedDecay_zeroInclusion m I h0)) := by
  apply exists_weightedCyclicPeriodization_cutoffSection_of_cover m hm hms γ hγ P hP
    (Icc a z) isCompact_Icc _ I h0
  intro x
  rw [interior_Icc]
  exact openInterval_covers_integerTranslations hγ hwidth x

include hm hms hP in
/-- The weighted periodization admits a continuous right inverse in every
interval containing zero, and in the entire-decay topology. -/
theorem exists_weightedCyclicPeriodization_cutoffSection (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (K : Set ℝ) (hK : IsCompact K) (hbs : support b ⊆ K),
      RightInverse (bruhatCyclicDecayCutoffLift m hm hms γ hγ I b hb K hK hbs)
        (P.comp (modulatedDecay_zeroInclusion m I h0)) := by
  obtain ⟨b, hb, hs, hS⟩ := exists_weightedCyclicPeriodization_cutoffSection_on_window
    m hm hms γ hγ P hP 0 (2 * (m γ).toAdd) (by linarith) I h0
  exact ⟨b, hb, _, isCompact_Icc, hs, hS⟩

include hm hms hP in
/-- Weighted periodization has a continuous linear section. -/
theorem exists_weightedCyclicPeriodization_section (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ∃ S : BruhatSchwartz H →L[ℂ] ModulatedExponentialInductive m I,
      RightInverse S (P.comp (modulatedDecay_zeroInclusion m I h0)) := by
  obtain ⟨b, hb, K, hK, hbs, hS⟩ :=
    exists_weightedCyclicPeriodization_cutoffSection m hm hms γ hγ P hP I h0
  exact ⟨bruhatCyclicDecayCutoffLift m hm hms γ hγ I b hb K hK hbs, hS⟩

/-- The support and invariance conditions of Proposition 4.5.2.1(1) are
closed in the full inductive topology of the entire-decay space. -/
theorem bruhatCyclicInvariantCompact_isClosed
    (K : Subgroup G) (W : Set ℝ) :
    IsClosed {f : ModulatedExponentialInductive m univ |
      support f.val ⊆ (fun x ↦ (m x).toAdd) ⁻¹' W ∧
      ∀ (k : K) x, f.val (k.val⁻¹ * x) = f.val x} := by
  let E := ModulatedExponentialInductive m univ
  let X := (fun x : G ↦ (m x).toAdd) ⁻¹' W
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  have hc (x : G) : Continuous (fun f : E ↦ f.val x) :=
    (bruhatSchwartz_continuous_eval x).comp J.continuous
  have hs : {f : E | support f.val ⊆ X} =
      ⋂ x ∈ Xᶜ, {f : E | f.val x = 0} := by
    ext f
    simp only [Set.mem_ofPred_eq, mem_iInter, mem_compl_iff]
    exact ⟨fun h x hx ↦ notMem_support.mp (fun hx' ↦ hx (h hx')),
      fun h x hx ↦ by_contra fun hn ↦ hx (h x hn)⟩
  change IsClosed ({f : E | support f.val ⊆ X} ∩
    {f : E | ∀ (k : K) x, f.val (k.val⁻¹ * x) = f.val x})
  apply IsClosed.inter
  · rw [hs]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦ isClosed_eq (hc x) continuous_const
  · rw [Set.ofPred_forall]
    refine isClosed_iInter fun k ↦ ?_
    rw [Set.ofPred_forall]
    exact isClosed_iInter fun x ↦ isClosed_eq (hc (k.val⁻¹ * x)) (hc x)


end

end Masullo
