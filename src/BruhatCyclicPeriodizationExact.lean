import BruhatCyclicFactorization

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1600000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
  (γ : G) (hγ : 0 < (m γ).toAdd)
local notation "H" => G ⧸ Subgroup.zpowers γ
variable [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]

omit [T2Space G] [LocallyCompactSpace G] in
/-- A quotient test vanishes exactly when it vanishes at all representatives. -/
private theorem quotient_test_zero_iff (g : BruhatSchwartz H) :
    g = 0 ↔ ∀ x : G, g.val (QuotientGroup.mk x) = 0 := by
  constructor
  · rintro rfl x
    rfl
  · intro h
    exact Subtype.ext (funext fun y ↦ QuotientGroup.induction_on y h)

include hm hms in
theorem bruhatCyclicPeriodization_ker
    (P : BruhatSchwartz G →L[ℂ] BruhatSchwartz H)
    (hP : ∀ f x, (P f).val (QuotientGroup.mk x) = bruhatSchwartz_cyclicOrbitSum m γ hγ x f) :
    P.ker = (bruhatSchwartzDifference γ).range := by
  ext f
  change P f = 0 ↔ f ∈ ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G))
  rw [bruhatSchwartzDifference_range_eq_commonKernel m hm hms γ hγ]
  rw [quotient_test_zero_iff γ (P f), mem_iInter]
  constructor
  · intro hf x
    exact (hP f x).symm.trans (hf x)
  · intro hf x
    exact (hP f x).trans (hf x)

/-- The cyclic difference as an endomorphism of the full decay space. -/
def modulatedDecay_cyclicDifference (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ModulatedExponentialInductive m I →L[ℂ] ModulatedExponentialInductive m I := by
  let E := ModulatedExponentialInductive m I
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  let A : E →L[ℂ] E := ⟨ModulatedExponentialInductive.translate m I γ⁻¹,
    (ModulatedExponentialInductive.continuous_translate m I hm hms ⟨0, h0⟩).comp
      (continuous_const.prodMk continuous_id)⟩
  exact ContinuousLinearMap.id ℂ E - A

omit [T2Space (G ⧸ Subgroup.zpowers γ)] [LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)] in
theorem modulatedDecay_cyclicDifference_apply (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (f : ModulatedExponentialInductive m I) (x : G) :
    (modulatedDecay_cyclicDifference m hm hms γ I h0 f).val x = f.val x - f.val (γ * x) := by
  change f.val x - f.val (γ⁻¹⁻¹ * x) = _
  rw [inv_inv]

theorem modulatedDecay_periodization_ker (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (T : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz H)
    (hT : ∀ f x, (T f).val (QuotientGroup.mk x) =
      bruhatSchwartz_cyclicOrbitSum m γ hγ x (modulatedDecay_zeroInclusion m I h0 f)) :
    T.ker = (modulatedDecay_cyclicDifference m hm hms γ I h0).range := by
  ext f
  change T f = 0 ↔ f ∈ (modulatedDecay_cyclicDifference m hm hms γ I h0).range
  rw [quotient_test_zero_iff γ (T f)]
  constructor
  · intro h
    have hz (x : G) : bruhatSchwartz_cyclicOrbitSum m γ hγ x (modulatedDecay_zeroInclusion m I h0 f) = 0 :=
      (hT f x).symm.trans (h x)
    obtain ⟨v, hv, _⟩ := (modulatedDecay_cyclicDifference_exists_iff m hm hms I h0 γ hγ f).1 hz
    refine ⟨v, ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext (funext fun x ↦ ?_))⟩
    exact (modulatedDecay_cyclicDifference_apply m hm hms γ I h0 v x).trans (hv x)
  · rintro ⟨v, hv⟩
    have h (x : G) : v.val x - v.val (γ * x) = f.val x :=
      (modulatedDecay_cyclicDifference_apply m hm hms γ I h0 v x).symm.trans
        (congrArg (fun u : ModulatedExponentialInductive m I ↦ u.val x) hv)
    have hz : ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x (modulatedDecay_zeroInclusion m I h0 f) = 0 := by
      let A := modulatedDecay_zeroInclusion m I h0 f
      let B := modulatedDecay_zeroInclusion m I h0 v
      have he (x : G) : (bruhatSchwartzDifference γ B).val x = A.val x := by
        rw [bruhatSchwartzDifference_apply]
        exact h x
      have hr : A ∈ ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) :=
        ⟨B, Subtype.ext (funext he)⟩
      rw [bruhatSchwartzDifference_range_eq_commonKernel m hm hms γ hγ] at hr
      exact fun x ↦ mem_iInter.mp hr x
    exact fun x ↦ (hT f x).trans (hz x)

/-- The ordinary periodization intertwines quotient translation on every
character isotype, including the norm-one characters in the manuscript. -/
theorem bruhatCyclicPeriodization_isotypic
    (P : BruhatSchwartz G →L[ℂ] BruhatSchwartz H)
    (hP : ∀ f x, (P f).val (QuotientGroup.mk x) = bruhatSchwartz_cyclicOrbitSum m γ hγ x f)
    {K : Subgroup G} (χ : PontryaginDual K) (f : BruhatSchwartz G)
    (hf : ∀ (a : K) x, f.val (a.val⁻¹ * x) = (χ a : ℂ) * f.val x) :
    ∀ (a : K) y, (P f).val (QuotientGroup.mk (a.val⁻¹) * y) = (χ a : ℂ) * (P f).val y := by
  intro a y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, hP, hP, bruhatSchwartz_cyclicOrbitSum_apply,
    bruhatSchwartz_cyclicOrbitSum_apply]
  have he (n : ℤ) : f.val (γ ^ n * (a.val⁻¹ * x)) = (χ a : ℂ) * f.val (γ ^ n * x) := by
    rw [mul_left_comm, hf]
  simp_rw [he]
  rw [tsum_mul_left]

include hm hms in
/-- The ordinary kernel on an isotype is the image of the same isotype
under the cyclic difference. -/
theorem bruhatCyclicPeriodization_isotypic_ker
    (P : BruhatSchwartz G →L[ℂ] BruhatSchwartz H)
    (hP : ∀ f x, (P f).val (QuotientGroup.mk x) = bruhatSchwartz_cyclicOrbitSum m γ hγ x f)
    {K : Subgroup G} (χ : PontryaginDual K) (f : BruhatSchwartz G)
    (hf : ∀ (a : K) x, f.val (a.val⁻¹ * x) = (χ a : ℂ) * f.val x) :
    P f = 0 ↔ ∃ v : BruhatSchwartz G, bruhatSchwartzDifference γ v = f ∧
      ∀ (a : K) x, v.val (a.val⁻¹ * x) = (χ a : ℂ) * v.val x := by
  constructor
  · intro h
    have hz (x : G) := (hP f x).symm.trans ((quotient_test_zero_iff γ (P f)).mp h x)
    exact bruhatSchwartzDifference_eq_of_isotypic_orbitSum_zero m hm hms γ hγ f hz χ hf
  · rintro ⟨v, hv, _⟩
    have h : f ∈ (bruhatSchwartzDifference γ).range := ⟨v, hv⟩
    rw [← bruhatCyclicPeriodization_ker m hm hms γ hγ P hP] at h
    exact h

/-- The weighted kernel on an isotype is the image of the same isotype
under the weighted cyclic difference. -/
theorem modulatedDecay_periodization_isotypic_ker (I : Set ℝ) (h0 : (0 : ℝ) ∈ I)
    (T : ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz H)
    (hT : ∀ f x, (T f).val (QuotientGroup.mk x) =
      bruhatSchwartz_cyclicOrbitSum m γ hγ x (modulatedDecay_zeroInclusion m I h0 f))
    {K : Subgroup G} (χ : PontryaginDual K) (f : ModulatedExponentialInductive m I)
    (hf : ∀ (a : K) x, f.val (a.val⁻¹ * x) = (χ a : ℂ) * f.val x) :
    T f = 0 ↔ ∃ v : ModulatedExponentialInductive m I,
      modulatedDecay_cyclicDifference m hm hms γ I h0 v = f ∧
      ∀ (a : K) x, v.val (a.val⁻¹ * x) = (χ a : ℂ) * v.val x := by
  constructor
  · intro h
    have hz (x : G) := (hT f x).symm.trans ((quotient_test_zero_iff γ (T f)).mp h x)
    obtain ⟨v, hv, hvχ⟩ := modulatedDecay_cyclicDifference_exists_isotypic
      m hm hms I h0 γ hγ f hz χ hf
    refine ⟨v, ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext (funext fun x ↦ ?_)),
      hvχ⟩
    exact (modulatedDecay_cyclicDifference_apply m hm hms γ I h0 v x).trans (hv x)
  · rintro ⟨v, hv, _⟩
    have h : f ∈ (modulatedDecay_cyclicDifference m hm hms γ I h0).range := ⟨v, hv⟩
    rw [← modulatedDecay_periodization_ker m hm hms γ hγ I h0 T hT] at h
    exact h

end

end Masullo
