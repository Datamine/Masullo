import AdelicFourierDerivative
import SLocalFlatTestSpace
import SLocalThetaDualGeneration
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev V := mixedEmbedding.mixedSpace F
private abbrev Place := HeightOneSpectrum (𝓞 F)

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel

/-- Odd tests have zero S-unit theta, since multiplication of the S-unit
index by the diagonal unit `-1` negates every summand. -/
theorem sLocalTheta_zero_of_odd (S : Finset (Place F))
    (f : SAdeles F S → ℂ) (hf : ∀ x, f (-x) = -f x) :
    sLocalTheta F S f = 0 := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [sLocalTheta_mk]
  let U := Additive (sIntegerRing F S)ˣ
  let a : U := Additive.ofMul (-1)
  let φ (u : U) := f (sIntegerDiagonal F S u.toMul.val * g.val)
  change (∑' u, φ u) = 0
  have he (u : U) : φ (u + a) = -φ u := by
    change f (sIntegerDiagonal F S (u.toMul * (-1 : (sIntegerRing F S)ˣ)).val * g.val) = _
    rw [Units.val_mul, Units.val_neg, Units.val_one, mul_neg, mul_one, map_neg, neg_mul, hf]
  have hs : -(∑' u, φ u) = ∑' u, φ u := by
    rw [← tsum_neg]
    exact (tsum_congr he).symm.trans ((Equiv.addRight a).tsum_eq φ)
  linear_combination (-1 / 2 : ℂ) * hs

private theorem mixed_dist_one_of_hyperplane {x : V F}
    (hx : (∃ v : {v : InfinitePlace F // v.IsReal}, x.1 v = 0) ∨
      ∃ v : {v : InfinitePlace F // v.IsComplex}, x.2 v = 0) :
    1 ≤ dist x 1 := by
  rw [dist_eq_norm]
  rcases hx with ⟨v, hv⟩ | ⟨v, hv⟩
  · have h := (norm_le_pi_norm (x - 1).1 v).trans (norm_fst_le (x - 1))
    simpa [hv] using h
  · have h := (norm_le_pi_norm (x - 1).2 v).trans (norm_snd_le (x - 1))
    simpa [hv] using h

private theorem exists_odd_archimedeanFlat :
    ∃ a : archimedeanFlatTestSubspace F, a.val 1 = 1 ∧
      ∀ x : V F, a.val (-x) = -a.val x := by
  have hc : (-1 : V F) ≠ 1 := by
    intro h
    apply (neg_ne_self.mpr (one_ne_zero : (1 : F) ≠ 0))
    apply mixedEmbedding_injective F
    simpa using h
  let r := min (1 / 2 : ℝ) (dist (-1 : V F) 1 / 2)
  have hr : 0 < r := lt_min (by norm_num) (half_pos (dist_pos.mpr hc))
  let b : ContDiffBump (1 : V F) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let ψ : V F → ℂ := fun x => (b x : ℂ)
  have hψ : HasCompactSupport ψ := b.hasCompactSupport.comp_left Complex.ofReal_zero
  let u := hψ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let J := (LinearIsometryEquiv.neg ℝ (E := V F)).toContinuousLinearEquiv
  let a := u - SchwartzMap.compCLMOfContinuousLinearEquiv ℂ J u
  have ha (x : V F) : a x = ψ x - ψ (-x) := rfl
  have hnear (x : V F) (hx : 1 ≤ dist x 1) :
      ψ =ᶠ[𝓝 x] (0 : V F → ℂ) := by
    have hlt : r < dist x 1 := (min_le_left _ _).trans_lt ((by norm_num : (1 / 2 : ℝ) < 1).trans_le hx)
    have ho : IsOpen {y : V F | r < dist y 1} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    filter_upwards [ho.mem_nhds hlt] with y hy
    change (b y : ℂ) = 0
    rw [b.zero_of_le_dist (le_of_lt hy), Complex.ofReal_zero]
  have hflat : a ∈ archimedeanFlatTestSubspace F := by
    rw [archimedeanFlatTestSubspace, mem_schwartzFlatSubspace]
    intro x hx n
    have hneg : (∃ v : {v : InfinitePlace F // v.IsReal}, (-x).1 v = 0) ∨
        ∃ v : {v : InfinitePlace F // v.IsComplex}, (-x).2 v = 0 := by
      simpa only [Set.mem_ofPred_eq, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, neg_eq_zero] using hx
    have hvan : (a : V F → ℂ) =ᶠ[𝓝 x] (0 : V F → ℂ) := by
      filter_upwards [hnear x (mixed_dist_one_of_hyperplane F hx),
        (continuous_neg.tendsto x).eventually (hnear (-x) (mixed_dist_one_of_hyperplane F hneg))]
        with y hy hn
      simp only [ha, hy, hn, Pi.zero_apply, sub_self]
    simpa using (hvan.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
  refine ⟨⟨a, hflat⟩, ?_, ?_⟩
  · change a 1 = 1
    rw [ha]
    change (b 1 : ℂ) - (b (-1) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le),
      b.zero_of_le_dist ((min_le_right _ _).trans (half_le_self (dist_nonneg))), Complex.ofReal_one,
      Complex.ofReal_zero, sub_zero]
  · intro x
    change a (-x) = -a x
    rw [ha, ha, neg_neg, neg_sub]

/-- At the archimedean stage there is a nonzero flat test representing
the zero theta class. Thus a flat representative is not unique even
at the trivial character and with no finite principal-value operator. -/
theorem sLocalFlatRepresentative_empty_nonunique :
    ∃ f : sLocalPolarFreeTestSubspace F (∅ : Finset (Place F)),
      f ≠ 0 ∧ GlobalBruhat.polarEvaluation F f.val.val = 0 ∧ sLocalThetaOperator F ∅ f.val = 0 := by
  obtain ⟨a, ha, hodd⟩ := exists_odd_archimedeanFlat F
  let f := sLocalPolarFreePure F ∅ a (fun v => False.elim (Finset.notMem_empty v.val v.property))
    (fun v => False.elim (Finset.notMem_empty v.val v.property))
  have hf (x : SAdeles F (∅ : Finset (Place F))) :
      sLocalBruhatRestriction F ∅ f.val.val x = a.val (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) := by
    change sLocalBruhatRestriction F ∅
      (sLocalBruhatPure F ∅ a.val (locallyConstantTestPiProduct _)).val x = _
    rw [sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply, Finset.prod_of_isEmpty, mul_one]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro hz
    have he := hf 1
    rw [hz] at he
    change (sLocalBruhatRestriction F ∅ 0) 1 = _ at he
    rw [map_zero, Pi.zero_apply, Prod.fst_one, map_one, ha] at he
    exact zero_ne_one he
  · have ha₀ : a.val 0 = 0 := by
      have h := hodd 0
      rw [neg_zero] at h
      linear_combination (1 / 2 : ℂ) * h
    have ha₁ : (∫ x : V F, a.val x) = 0 := by
      have hneg : MeasurePreserving (fun x : V F => -x) :=
        (volume_preserving_pi fun _ => Measure.measurePreserving_neg (volume : Measure ℝ)).prod
          (volume_preserving_pi fun _ => Measure.measurePreserving_neg (volume : Measure ℂ))
      letI : (volume : Measure (V F)).IsNegInvariant := ⟨hneg.map_eq⟩
      have h := integral_neg_eq_self (fun x : V F => a.val x) volume
      simp only [hodd, integral_neg] at h
      linear_combination (-1 / 2 : ℂ) * h
    let b : ∀ v : (∅ : Finset (Place F)), locallyConstantTests (v.val.adicCompletion F) :=
      fun v => False.elim (Finset.notMem_empty v.val v.property)
    let ψ := insertFinite F ∅ (locallyConstantTestPiProduct b)
    change GlobalBruhat.polarEvaluation F (GlobalBruhat.pure F ψ a.val) = 0
    apply Prod.ext
    · change a.val (InfiniteAdeleRing.ringEquiv_mixedSpace F 0) * ψ.toLocallyConstant 0 = 0
      rw [map_zero, ha₀, zero_mul]
    · exact globalBruhatFourier_pure_zero_of_archIntegral_zero F ψ a.val ha₁
  · change sLocalTheta F ∅ (sLocalBruhatRestriction F ∅ f.val.val) = 0
    apply sLocalTheta_zero_of_odd
    intro x
    rw [hf, hf, Prod.fst_neg, map_neg, hodd]

/-- The nonzero odd flat test and the zero test give the same homogeneous
class at every norm-one character of the archimedean S-local stage. -/
theorem sLocalFlatRepresentative_empty_not_injective
    (ν : Measure (SLocalThetaNormOne F ∅)) [ν.IsHaarMeasure]
    (ω : PontryaginDual (SLocalThetaNormOne F ∅)) :
    ¬ Injective (fun f : sLocalPolarFreeTestSubspace F (∅ : Finset (Place F)) =>
      (sLocalHomogeneousThetaKernel F ∅ ν ω).mkQ f.val) := by
  intro hinj
  obtain ⟨f, hf, _, hθ⟩ := sLocalFlatRepresentative_empty_nonunique F
  apply hf
  apply hinj
  have hmem : f.val ∈ sLocalHomogeneousThetaKernel F ∅ ν ω := by
    apply (mem_sLocalHomogeneousThetaKernel_iff F ∅ ν ω f.val).2
    intro q
    unfold sLocalHomogeneousTheta
    change (∫ k : SLocalThetaNormOne F ∅, (ω k : ℂ) *
      sLocalThetaOperator F ∅ f.val (k.val * q) ∂ν) = 0
    simp [hθ]
  exact ((Submodule.Quotient.mk_eq_zero _).2 hmem).trans (map_zero _).symm

end

end Masullo
