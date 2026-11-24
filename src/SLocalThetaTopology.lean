import SLocalThetaFourier
import AdelicThetaDecay
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical ContDiff NumberField RestrictedProduct SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev G := GlobalThetaQuotient F
private abbrev E (S : Finset (Place F)) := SLocalThetaQuotient F S

/-- The global theta quotient has the locally convex final topology for
the maps from the ordinary S-local theta quotients. -/
theorem globalThetaQuotient_continuous_of_stages {R : Type*} [AddCommGroup R]
    [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]
    (L : G F →ₗ[ℂ] R)
    (hL : ∀ S : Finset (Place F), Continuous (L.comp (sLocalThetaToGlobal F S).toLinearMap)) :
    Continuous L := by
  let K := (globalThetaOperator F).ker
  apply K.isQuotientMap_mkQ.continuous_iff.mpr
  change Continuous (L.comp K.mkQ)
  apply GlobalBruhat.continuous_of_pure F (PolynormableSpace.withSeminorms ℂ R)
  intro ψ
  obtain ⟨S, hS⟩ := sLocalBruhatProjection_pure_eventually F ψ
  have he : (fun φ ↦ L (K.mkQ (GlobalBruhat.pure F ψ φ))) =
      (L.comp (sLocalThetaToGlobal F S).toLinearMap) ∘
        (sLocalThetaOperator F S).ker.mkQ ∘ sLocalBruhatCorestrict F S ∘ GlobalBruhat.pure F ψ := by
    funext φ
    change L (K.mkQ (GlobalBruhat.pure F ψ φ)) =
      L (K.mkQ (sLocalBruhatProjection F S (GlobalBruhat.pure F ψ φ)))
    rw [hS S (Finset.Subset.refl S)]
  change Continuous (fun φ ↦ L (K.mkQ (GlobalBruhat.pure F ψ φ)))
  rw [he]
  exact (hL S).comp ((sLocalThetaOperator F S).ker.mkQL.continuous.comp
    ((sLocalBruhatCorestrict F S).continuous.comp (GlobalBruhat.pure_continuous F ψ)))

theorem globalThetaQuotient_continuous_iff_stages {R : Type*} [AddCommGroup R]
    [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]
    (L : G F →ₗ[ℂ] R) :
    Continuous L ↔
      ∀ S : Finset (Place F), Continuous (L.comp (sLocalThetaToGlobal F S).toLinearMap) :=
  ⟨fun h S ↦ h.comp (sLocalThetaToGlobal F S).continuous,
    globalThetaQuotient_continuous_of_stages F L⟩

variable {R : Type*} [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]

private theorem globalThetaQuotient_exhausted (q : G F) :
    ∃ S, ∃ x : E F S, sLocalThetaToGlobal F S x = q := by
  obtain ⟨S, _, _, x, hx⟩ := globalThetaQuotient_exhausted_by_different_stages F ∅ q
  exact ⟨S, x, hx⟩

/-- The global ordinary theta quotient realizes the locally convex
inductive limit of the S-local quotients. -/
theorem globalThetaQuotient_existsUnique_lift
    (L : ∀ S : Finset (Place F), E F S →L[ℂ] R)
    (hL : ∀ (S T : Finset (Place F)) (h : S ⊆ T) (x : E F S),
      L T (sLocalThetaTransition F h x) = L S x) :
    ∃! A : G F →L[ℂ] R, ∀ (S : Finset (Place F)) (x : E F S),
      A (sLocalThetaToGlobal F S x) = L S x := by
  have hcommon (S T : Finset (Place F)) (x : E F S) (y : E F T)
      (hxy : sLocalThetaToGlobal F S x = sLocalThetaToGlobal F T y) :
      L S x = L T y := by
    let U := S ∪ T
    have hs : S ⊆ U := Finset.subset_union_left
    have ht : T ⊆ U := Finset.subset_union_right
    have he : sLocalThetaTransition F hs x = sLocalThetaTransition F ht y := by
      apply sLocalThetaToGlobal_injective F U
      rw [sLocalThetaToGlobal_transition, sLocalThetaToGlobal_transition, hxy]
    rw [← hL S U hs x, ← hL T U ht y, he]
  choose stage repr hrepr using globalThetaQuotient_exhausted F
  let a (q : G F) := L (stage q) (repr q)
  have ha (S : Finset (Place F)) (x : E F S) : a (sLocalThetaToGlobal F S x) = L S x :=
    hcommon _ S _ x (hrepr _)
  let Aₗ : G F →ₗ[ℂ] R :=
    { toFun := a
      map_add' := fun q r ↦ by
        let U := stage q ∪ stage r
        let x := sLocalThetaTransition F (Finset.subset_union_left (s₁ := stage q)
          (s₂ := stage r)) (repr q)
        let y := sLocalThetaTransition F (Finset.subset_union_right (s₁ := stage q)
          (s₂ := stage r)) (repr r)
        have hx : sLocalThetaToGlobal F U x = q :=
          (sLocalThetaToGlobal_transition F _ (repr q)).trans (hrepr q)
        have hy : sLocalThetaToGlobal F U y = r :=
          (sLocalThetaToGlobal_transition F _ (repr r)).trans (hrepr r)
        rw [← hx, ← hy, ← map_add, ha, ha, ha, map_add]
      map_smul' := fun c q ↦ by
        rw [← hrepr q, ← map_smul, ha, ha, RingHom.id_apply, map_smul] }
  have hc : Continuous Aₗ := by
    apply globalThetaQuotient_continuous_of_stages F
    intro S
    have h : Aₗ.comp (sLocalThetaToGlobal F S).toLinearMap = (L S).toLinearMap :=
      LinearMap.ext (ha S)
    rw [h]
    exact (L S).continuous
  refine ⟨⟨Aₗ, hc⟩, ha, ?_⟩
  intro B hB
  apply ContinuousLinearMap.ext
  intro q
  rw [← hrepr q, hB]
  exact (ha _ _).symm

private theorem sLocalBruhatProjection_leftTranslate (S : Finset (Place F))
    (p : Idele F) (f : sLocalBruhatImage F S) :
    let g := Units.map (sAdelesProjection F S).toMonoidHom p
    sLocalBruhatProjection F S (GlobalBruhat.leftTranslate F p f.val) =
      GlobalBruhat.leftTranslate F (sLocalEmbed F S g).val f.val := by
  intro g
  let a := sLocalEmbed F S g
  have hproj : sAdelesProjection F S (a.val⁻¹).val = g.inv := by
    have he : a.val⁻¹ = (sLocalEmbed F S g⁻¹).val := by rw [map_inv, Subgroup.coe_inv]
    rw [he, sLocalEmbed_project]
    rfl
  have hp : sAdelesProjection F S (p⁻¹).val = g.inv := rfl
  have hi (w : Place F) (hw : w ∉ S) : a.val.inv.2 w = 1 := by
    change (a.val⁻¹).val.2 w = 1
    have he : a.val⁻¹ = (sLocalEmbed F S g⁻¹).val := by rw [map_inv, Subgroup.coe_inv]
    rw [he]
    exact sLocalEmbed_outside_one F S g⁻¹ w hw
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  let b := GlobalBruhat.leftTranslate F p f.val
  change GlobalBruhat.evaluation F x (sLocalBruhatProjection F S b) =
    GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F a.val f.val)
  have he := sLocalBruhatRestriction_reconstruct F S (sLocalBruhatCorestrict F S b) x
  rw [sLocalBruhatCorestrict_restrict] at he
  change GlobalBruhat.evaluation F x (sLocalBruhatProjection F S b) = _ at he
  rw [he, GlobalBruhat.leftTranslate_apply, sLocalBruhatRestriction_reconstruct]
  have hr : sLocalBruhatRestriction F S b (sAdelesProjection F S x) =
      sLocalBruhatRestriction F S f.val (g.inv * sAdelesProjection F S x) := by
    change GlobalBruhat.evaluation F (sLocalBruhatPad F S (sAdelesProjection F S x))
      (GlobalBruhat.leftTranslate F p f.val) = _
    rw [GlobalBruhat.leftTranslate_apply, ← sLocalBruhatPad_mul_project, hp]
    rfl
  rw [hr, map_mul, hproj]
  have hcond : (∀ w ∉ S, ((a.val⁻¹).val * x).2 w ∈ w.adicCompletionIntegers F) ↔
      ∀ w ∉ S, x.2 w ∈ w.adicCompletionIntegers F := by
    refine forall₂_congr fun w hw ↦ ?_
    change a.val.inv.2 w * x.2 w ∈ w.adicCompletionIntegers F ↔
      x.2 w ∈ w.adicCompletionIntegers F
    rw [hi w hw, one_mul]
  simp only [hcond]

set_option maxHeartbeats 800000 in
private theorem exists_positive_archStageTheta :
    ∃ f : sLocalBruhatImage F ∅, 0 < ‖globalThetaOperator F f.val 1‖ := by
  let A := Adeles F
  let K := FiniteAdeleRing (𝓞 F) F
  let I : Set K := finiteIntegralAdeles F
  have hIo : IsOpen I := by
    have he : I = {a : K | ∀ w : Place F, a w ∈ w.adicCompletionIntegers F} :=
      Set.ext (mem_finiteIntegralAdeles_iff F)
    rw [he]
    exact RestrictedProduct.isOpen_forall_mem
      (fun w ↦ Valued.isOpen_valuationSubring (w.adicCompletion F))
  letI : T2Space K :=
    inferInstanceAs (T2Space (Πʳ w : Place F, [w.adicCompletion F, w.adicCompletionIntegers F]))
  let ψ₀ := compactOpenIndicator (X := K) ⟨I, isCompact_finiteIntegralAdeles F, hIo⟩
  let ψ : FiniteBruhat F := ⟨⟨ψ₀.val, ψ₀.property.1⟩, ψ₀.property.2⟩
  obtain ⟨u, _, hc, hd, hu, h₁⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (s := univ)
      (x := (1 : mixedEmbedding.mixedSpace F)) univ_mem
  let φ := (hc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hd)
  let f := GlobalBruhat.pure F ψ φ
  let v := (GlobalBruhat.algebraicEquiv F f).val
  have hv (a : A) : v a = (u (mixedArch a) : ℂ) * I.indicator (fun _ ↦ (1 : ℂ)) a.2 := rfl
  have hnonneg (a : A) : 0 ≤ (v a).re := by
    rw [hv]
    by_cases ha : a.2 ∈ I
    · rw [indicator_of_mem ha, mul_one, Complex.ofReal_re]
      exact (hu (mem_range_self (mixedArch a))).1
    · rw [indicator_of_notMem ha, mul_zero, Complex.zero_re]
  have hf₁ : v 1 = 1 := by
    rw [hv, map_one, h₁, Complex.ofReal_one, indicator_of_mem
      (show (1 : A).2 ∈ I from (finiteIntegralAdeles F).one_mem), one_mul]
  have hmem : f ∈ sLocalBruhatImage F ∅ := by
    apply (sLocalBruhatImage_iff_support_tail_invariant F ∅ f).mpr
    constructor
    · rintro a ⟨w, _, hw⟩
      change v a = 0
      rw [hv, indicator_of_notMem (show a.2 ∉ I from fun h ↦
        hw ((mem_finiteIntegralAdeles_iff F a.2).mp h w)), mul_zero]
    · intro b hb a
      change v (a + finiteAdelicTranslation F b) = v a
      rw [hv, hv]
      have he : (a + finiteAdelicTranslation F b).2 ∈ I ↔ a.2 ∈ I := by
        change a.2 + b ∈ finiteIntegralAdeles F ↔ a.2 ∈ finiteIntegralAdeles F
        exact (finiteIntegralAdeles F).toAddSubgroup.add_mem_cancel_right
          ((mem_finiteIntegralAdeles_iff F b).mpr hb.2)
      have hArch : mixedArch (a + finiteAdelicTranslation F b) = mixedArch a := by
        change (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a.1 + 0) =
          (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1
        rw [add_zero]
      rw [hArch]
      by_cases ha : a.2 ∈ I
      · rw [indicator_of_mem ha, indicator_of_mem (he.mpr ha)]
      · rw [indicator_of_notMem ha, indicator_of_notMem (mt he.mp ha)]
  refine ⟨⟨f, hmem⟩, ?_⟩
  have hs := adelicThetaNorm_summable F (GlobalBruhat.algebraicEquiv F f).property (1 : Idele F)
  have hsum : Summable (fun t : Fˣ ↦ (thetaSummand F v 1 t).re) := Complex.reCLM.summable hs.of_norm
  have h2 : (thetaSummand F v 1 (1 : Fˣ)).re = 1 := by
    rw [thetaSummand, map_one, mul_one]
    exact congrArg Complex.re hf₁
  have hpositive : 1 ≤ (globalThetaOperator F f 1).re := by
    rw [← map_one (ideleClassMap F)]
    change 1 ≤ (∑' t, thetaSummand F v 1 t).re
    rw [Complex.re_tsum hs.of_norm, ← h2]
    exact hsum.le_tsum (1 : Fˣ) (fun t _ ↦ hnonneg _)
  exact (zero_lt_one.trans_le hpositive).trans_le (Complex.re_le_norm _)

private theorem norm_arch_projection_two :
    let p := principalIdele F (Units.mk0 (2 : F) (by norm_num))
    let g := Units.map (sAdelesProjection F ∅).toMonoidHom p
    1 < ideleNorm F (sLocalEmbed F ∅ g).val := by
  intro p g
  let a := sLocalEmbed F ∅ g
  change 1 < (∏ v : InfinitePlace F, ‖a.val.val.1 v‖ ^ v.mult) *
    ∏ᶠ w : Place F, ‖a.val.val.2 w‖
  have hFin : (∏ᶠ w : Place F, ‖a.val.val.2 w‖) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro w
    rw [sLocalEmbed_outside_one F ∅ g w (Finset.notMem_empty w), norm_one]
  rw [hFin, mul_one, sLocalEmbed_arch F ∅ g]
  calc
    1 = ∏ _ : InfinitePlace F, (1 : ℝ) := by simp
    _ < _ := Finset.prod_lt_prod_of_nonempty (fun _ _ ↦ zero_lt_one) ?_ Finset.univ_nonempty
  intro v _
  have hv : g.val.1 v = 2 := by
    change algebraMap F v.Completion (2 : F) = 2
    exact map_ofNat _ 2
  rw [hv]
  have ht : 1 < ‖(2 : v.Completion)‖ := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _) (2 : v.Completion), map_ofNat]
    norm_num
  exact one_lt_pow₀ ht v.mult_ne_zero

/-- The test-space projection onto the archimedean stage does not preserve
the global theta kernel. The witness is a test minus a principal translate. -/
theorem archStageProjection_fails_thetaKernel :
    ∃ b : GlobalBruhat F, b ∈ (globalThetaOperator F).ker ∧
      sLocalBruhatProjection F ∅ b ∉ (globalThetaOperator F).ker := by
  obtain ⟨f, hf⟩ := exists_positive_archStageTheta F
  let u := Units.mk0 (2 : F) (by norm_num)
  let p := principalIdele F u
  let g := Units.map (sAdelesProjection F ∅).toMonoidHom p
  let a := (sLocalEmbed F ∅ g).val
  let r := ideleClassMap F a
  let b := f.val - GlobalBruhat.leftTranslate F p f.val
  let θ := globalThetaOperator F f.val
  have hp : ideleClassMap F p = 1 := (QuotientGroup.eq_one_iff p).mpr ⟨u, rfl⟩
  refine ⟨b, ?_, ?_⟩
  · apply LinearMap.mem_ker.mpr
    change globalThetaOperator F (f.val - GlobalBruhat.leftTranslate F p f.val) = 0
    rw [map_sub, sub_eq_zero]
    funext q
    rw [globalThetaOperator_leftTranslate, hp, inv_one]
    exact (congrArg (globalThetaOperator F f.val) (one_mul q)).symm
  · intro h
    have he := LinearMap.mem_ker.mp h
    change globalThetaOperator F (sLocalBruhatProjection F ∅
      (f.val - GlobalBruhat.leftTranslate F p f.val)) = 0 at he
    rw [map_sub, sLocalBruhatProjection_fixes F ∅ f.val f.property,
      sLocalBruhatProjection_leftTranslate, map_sub, sub_eq_zero] at he
    have hfix (q : IdeleClass F) : θ q = θ (r⁻¹ * q) :=
      (congrFun he q).trans (globalThetaOperator_leftTranslate F a f.val q)
    have hpow (n : ℕ) : θ (r ^ n) = θ 1 := by
      induction n with
      | zero => rw [pow_zero]
      | succ n ih =>
        rw [hfix (r ^ (n + 1)), pow_succ', ← mul_assoc, inv_mul_cancel, one_mul, ih]
    have hm : 1 < ideleClassNorm F r := by
      change 1 < ideleClassNorm F (ideleClassMap F a)
      rw [ideleClassNorm_mk]
      exact norm_arch_projection_two F
    obtain ⟨C, _, hC⟩ :=
      adelicTheta_largeNorm_bounded F {f.val} (Bornology.isVonNBounded_singleton f.val) 1
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖θ 1‖) hm
    have hlarge : 1 ≤ ideleClassNorm F (r ^ n) := by
      rw [map_pow]
      exact one_le_pow₀ hm.le
    have hbound := hC f.val (mem_singleton _) (r ^ n) hlarge
    rw [pow_one, map_pow] at hbound
    have hnle (q : IdeleClass F) : ‖θ q‖ ≤
        adelicThetaAbs F (GlobalBruhat.algebraicEquiv F f.val).val q := by
      obtain ⟨z, rfl⟩ := ideleClassMap_surjective F q
      rw [adelicThetaAbs_mk]
      exact norm_tsum_le_tsum_norm
        (adelicThetaNorm_summable F (GlobalBruhat.algebraicEquiv F f.val).property z)
    have hsmall := mul_le_mul_of_nonneg_left (hnle (r ^ n))
      (pow_nonneg (zero_le_one.trans hm.le) n)
    rw [hpow] at hsmall
    exact ((not_lt_of_ge (hsmall.trans hbound))
      (by simpa only [mul_comm ‖θ 1‖] using (div_lt_iff₀ hf).mp hn))

/-- The proposed coordinate projection cannot descend even as a function
on the global theta quotient. -/
theorem archStageProjection_no_thetaQuotient_map :
    ¬ ∃ P : G F → G F, ∀ f : GlobalBruhat F,
      P (Submodule.Quotient.mk f) = Submodule.Quotient.mk (sLocalBruhatProjection F ∅ f) := by
  rintro ⟨P, hP⟩
  obtain ⟨b, hb, hbad⟩ := archStageProjection_fails_thetaKernel F
  let K := (globalThetaOperator F).ker
  have h0 : P 0 = 0 := by simpa only [map_zero, Submodule.Quotient.mk_zero] using hP 0
  have h := hP b
  rw [(Submodule.Quotient.mk_eq_zero K).mpr hb, h0] at h
  exact hbad ((Submodule.Quotient.mk_eq_zero K).mp h.symm)

end

end Masullo
