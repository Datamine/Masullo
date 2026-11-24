import BruhatCyclicPeriodizationStages
import BruhatCyclicPeriodizationLift
import BruhatCyclicPeriodizationExact

open Function Set

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)

/-- A cyclic difference preserves compact support. -/
theorem bruhatSchwartzDifference_hasCompactSupport (γ : G)
    (f : BruhatSchwartz G) (hf : HasCompactSupport f.val) :
    HasCompactSupport (bruhatSchwartzDifference γ f).val := by
  have he : (bruhatSchwartzDifference γ f).val =
      f.val - f.val ∘ Homeomorph.mulLeft γ :=
    funext (bruhatSchwartzDifference_apply γ f)
  rw [he]
  exact hf.sub (hf.comp_homeomorph (Homeomorph.mulLeft γ))

include hm hms in
/-- Every ordinary quotient class for a finite list of positive-period
differences has a compactly supported Schwartz–Bruhat representative.
This is the representative clause of Corollary 4.6.3.1. -/
theorem exists_bruhatCyclicProduct_compact_representative (gs : List G)
    (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd) (f : BruhatSchwartz G) :
    ∃ u v : BruhatSchwartz G, HasCompactSupport u.val ∧
      f = u + bruhatSchwartzDifferenceProduct gs v := by
  induction gs generalizing f with
  | nil =>
    exact ⟨0, f, HasCompactSupport.zero, (zero_add f).symm⟩
  | cons γ gs ih =>
    have hγ := hgs γ List.mem_cons_self
    let Γ := Subgroup.zpowers γ
    letI : DiscreteTopology Γ := modulatedCyclicSubgroup_discrete m γ hγ
    letI : IsClosed (Γ : Set G) := Γ.isClosed_of_discrete
    obtain ⟨p, u, hu⟩ := f.property
    obtain ⟨P, hp⟩ := exists_wholeBruhatStage_refinement m hm hms p
    let u' := p.transition P.val hp u
    have hu' : P.val.inclusion u' = f :=
      (p.inclusion_transition P.val hp u).trans (Subtype.ext hu)
    have hStage := exists_bruhatCyclicPeriodization_stage m hm γ hγ P
    let Q := hStage.choose
    have hQ := hStage.choose_spec u'
    let g := Q.val.inclusion hQ.choose
    have hg (x : G) : g.val (QuotientGroup.mk x) = bruhatSchwartz_cyclicOrbitSum m γ hγ x f :=
      (hQ.choose_spec x).trans (congrArg (bruhatSchwartz_cyclicOrbitSum m γ hγ x) hu')
    obtain ⟨a, ha, hAa⟩ := exists_bruhatCyclic_compact_periodization_lift m hm hms γ hγ g
    have hz (x : G) : bruhatSchwartz_cyclicOrbitSum m γ hγ x (f - a) = 0 :=
      ((bruhatSchwartz_cyclicOrbitSum m γ hγ x).map_sub f a).trans
        ((congrArg (bruhatSchwartz_cyclicOrbitSum m γ hγ x f - ·)
          ((hAa x).trans (hg x))).trans (sub_self _))
    obtain ⟨w, hw, _⟩ := bruhatSchwartzDifference_eq_of_orbitSum_zero m hm hms γ hγ (f - a) hz
    obtain ⟨b, v, hb, hB⟩ := ih (fun g hg ↦ hgs g (List.mem_cons_of_mem _ hg)) w
    refine ⟨a + bruhatSchwartzDifference γ b, v,
      ha.add (bruhatSchwartzDifference_hasCompactSupport γ b hb), ?_⟩
    change f = (a + bruhatSchwartzDifference γ b) +
      bruhatSchwartzDifference γ (bruhatSchwartzDifferenceProduct gs v)
    have hF : f = a + bruhatSchwartzDifference γ w := by
      rw [hw]
      abel
    rw [hF, hB, map_add, add_assoc]

/-- The finite difference product on the full exponential-decay space. -/
def modulatedDecay_cyclicDifferenceProduct (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    List G → ModulatedExponentialInductive m I →L[ℂ] ModulatedExponentialInductive m I
  | [] => ContinuousLinearMap.id ℂ _
  | γ :: gs => (modulatedDecay_cyclicDifference m hm hms γ I h0).comp
      (modulatedDecay_cyclicDifferenceProduct I h0 gs)

include hm hms in
theorem modulatedDecay_zeroInclusion_cyclicDifferenceProduct
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G) (f : ModulatedExponentialInductive m I) :
    modulatedDecay_zeroInclusion m I h0 (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs f) =
      bruhatSchwartzDifferenceProduct gs (modulatedDecay_zeroInclusion m I h0 f) := by
  induction gs with
  | nil => rfl
  | cons γ gs ih =>
    apply Subtype.ext
    funext x
    let u := modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs f
    let v := bruhatSchwartzDifferenceProduct gs (modulatedDecay_zeroInclusion m I h0 f)
    change (modulatedDecay_cyclicDifference m hm hms γ I h0 u).val x =
      (bruhatSchwartzDifference γ v).val x
    rw [modulatedDecay_cyclicDifference_apply, bruhatSchwartzDifference_apply]
    exact congrArg₂ (· - ·) (congrArg (fun g : BruhatSchwartz G ↦ g.val x) ih)
      (congrArg (fun g : BruhatSchwartz G ↦ g.val (γ * x)) ih)

include hm hms in
/-- A weighted function in the ordinary product range is in the weighted
product range. The ordinary preimage inherits every weight of the output. -/
theorem modulatedDecay_cyclicDifferenceProduct_range_preimage
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (gs : List G) (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd)
    (f : ModulatedExponentialInductive m I) :
    modulatedDecay_zeroInclusion m I h0 f ∈ (bruhatSchwartzDifferenceProduct gs).range ↔
      f ∈ (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs).range := by
  constructor
  · rintro ⟨v, hv⟩
    have hval : (bruhatSchwartzDifferenceProduct gs v).val = f.val := congrArg Subtype.val hv
    have hmem : v.val ∈ modulatedExponentialDecaySubmodule m I := by
      apply (Submodule.mem_iInf _).mpr
      intro a
      apply bruhatSchwartzDifferenceProduct_inherits_weight m hm hms gs hgs
      rw [hval]
      exact (Submodule.mem_iInf _).mp (ModulatedExponentialInductive.algebraicEquiv f).property a
    let u : ModulatedExponentialInductive m I :=
      ModulatedExponentialInductive.algebraicEquiv.symm ⟨v.val, hmem⟩
    refine ⟨u, ModulatedExponentialInductive.algebraicEquiv.injective (Subtype.ext ?_)⟩
    have hu : modulatedDecay_zeroInclusion m I h0 u = v := Subtype.ext rfl
    have he := modulatedDecay_zeroInclusion_cyclicDifferenceProduct m hm hms I h0 gs u
    change (modulatedDecay_cyclicDifferenceProduct m hm hms I h0 gs u).val = f.val
    exact congrArg (fun g : BruhatSchwartz G ↦ g.val)
      (he.trans ((congrArg (bruhatSchwartzDifferenceProduct gs) hu).trans hv))
  · rintro ⟨u, hu⟩
    exact ⟨modulatedDecay_zeroInclusion m I h0 u,
      (modulatedDecay_zeroInclusion_cyclicDifferenceProduct m hm hms I h0 gs u).symm.trans
        (congrArg (modulatedDecay_zeroInclusion m I h0) hu)⟩

end

end Masullo
