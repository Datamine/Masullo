import FiniteThetaShellStages
import SLocalThetaFrechet
import SLocalPrincipalValue

open Function IsDedekindDomain NumberField Set Topology

open scoped Classical NumberField SchwartzMap TensorProduct

namespace Masullo

noncomputable section

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Mix := mixedEmbedding.mixedSpace F
private abbrev Arch := 𝓢(Mix F, ℂ)
private abbrev FinTest (v : Place F) := locallyConstantTests (v.adicCompletion F)
private abbrev Theta (S : Finset (Place F)) := SLocalThetaQuotient F S

variable (S : Finset (Place F))

private def finiteUnit (g : (SAdeles F S)ˣ) (w : S) : (w.val.adicCompletion F)ˣ := by
  let ev : SAdeles F S →+* w.val.adicCompletion F :=
    { toFun := fun x ↦ x.2 w
      map_one' := rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  exact Units.map ev.toMonoidHom g

/-- Pullback by the inverse archimedean coordinate of an S-idele. -/
def sLocalArchPullback (g : (SAdeles F S)ˣ) : Arch F →L[ℂ] Arch F := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let u := Units.map e.toMonoidHom ((MulEquiv.prodUnits g⁻¹).1)
  let A : Mix F ≃ₗ[ℝ] Mix F :=
    { u.mulLeft with
      map_add' := mul_add _
      map_smul' := fun _ _ ↦ mul_smul_comm _ _ _ }
  exact SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv

/-- Compute the pullback in the mixed real and complex coordinates. -/
theorem sLocalArchPullback_apply (g : (SAdeles F S)ˣ) (φ : Arch F) (a : InfiniteAdeleRing F) :
    sLocalArchPullback F S g φ (InfiniteAdeleRing.ringEquiv_mixedSpace F a) =
      φ (InfiniteAdeleRing.ringEquiv_mixedSpace F (g.inv.1 * a)) := by
  rw [map_mul]
  rfl

private theorem testExt {f h : sLocalBruhatImage F S}
    (he : sLocalBruhatRestriction F S f.val = sLocalBruhatRestriction F S h.val) :
    f = h := by
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x f.val = GlobalBruhat.evaluation F x h.val
  rw [sLocalBruhatRestriction_reconstruct F S f, sLocalBruhatRestriction_reconstruct F S h, he]

private def pureClass (φ : Arch F) (f : ∀ w : S, FinTest F w.val) : Theta F S :=
  (sLocalThetaOperator F S).ker.mkQL (sLocalBruhatPure F S φ (locallyConstantTestPiProduct f))

/-- Translate the selected finite factors by their respective unit coordinates. -/
def sLocalFinitePiTranslate (g : (SAdeles F S)ˣ) (f : ∀ w : S, FinTest F w.val) :
    ∀ w : S, FinTest F w.val :=
  fun w ↦ locallyConstantTestTranslate _ (finiteUnit F S g w) (f w)

/-- Translation acts factor by factor on a pure S-local test. -/
theorem sLocalBruhatLeftTranslate_pure_piProduct (g : (SAdeles F S)ˣ) (φ : Arch F) (f : ∀ w : S, FinTest F w.val) :
    sLocalBruhatLeftTranslate F S g (sLocalBruhatPure F S φ (locallyConstantTestPiProduct f)) =
      sLocalBruhatPure F S (sLocalArchPullback F S g φ) (locallyConstantTestPiProduct (sLocalFinitePiTranslate F S g f)) := by
  apply testExt F S
  funext x
  rw [sLocalBruhatLeftTranslate_restrict, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict,
    locallyConstantTestPiProduct_apply, locallyConstantTestPiProduct_apply, sLocalArchPullback_apply]
  rfl

private def localPrincipal (u : (sIntegerRing F S)ˣ) : (SAdeles F S)ˣ :=
  Units.map (sAdelesProjection F S).toMonoidHom (principalIdele F (sUnitToField F S u))

private theorem pureClass_principal (u : (sIntegerRing F S)ˣ) (φ : Arch F)
    (f : ∀ w : S, FinTest F w.val) :
    pureClass F S (sLocalArchPullback F S (localPrincipal F S u) φ)
        (sLocalFinitePiTranslate F S (localPrincipal F S u) f) = pureClass F S φ f := by
  unfold pureClass
  rw [← sLocalBruhatLeftTranslate_pure_piProduct]
  let b := sLocalBruhatPure F S φ (locallyConstantTestPiProduct f)
  change Submodule.Quotient.mk (sLocalBruhatLeftTranslate F S (localPrincipal F S u) b) =
    Submodule.Quotient.mk b
  rw [← sLocalThetaTranslateIdeles_mk]
  exact sLocalThetaTranslate_sUnit F S u _

private theorem finiteUnit_principal_pow (u : (sIntegerRing F S)ˣ) (n : ℤ) (w : S) :
    finiteUnit F S (localPrincipal F S (u ^ n)) w =
      (finiteUnit F S (localPrincipal F S u) w) ^ n := by
  unfold localPrincipal finiteUnit
  simp only [map_zpow]

private theorem replaceProduct_apply (i : S) (f : ∀ w : S, FinTest F w.val)
    (q : FinTest F i.val) (x : ∀ w : S, w.val.adicCompletion F) :
    (locallyConstantTestPiProduct (Function.update f i q)).val x =
      (q.val (x i)) * ∏ w ∈ Finset.univ.erase i, (f w).val (x w) := by
  rw [locallyConstantTestPiProduct_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    Function.update_self]
  congr 1
  exact Finset.prod_congr rfl
    (fun w hw ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)])

private def replaceCoordinate (i : S) (f : ∀ w : S, FinTest F w.val) :
    FinTest F i.val →ₗ[ℂ] locallyConstantTests ((w : S) → w.val.adicCompletion F) where
  toFun g := locallyConstantTestPiProduct (Function.update f i g)
  map_add' g h := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply, replaceProduct_apply, add_mul]
  map_smul' c g := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      replaceProduct_apply, mul_assoc]

private def replaceClass (φ : Arch F) (i : S) (f : ∀ w : S, FinTest F w.val) :
    FinTest F i.val →ₗ[ℂ] Theta F S :=
  (sLocalThetaOperator F S).ker.mkQ.comp
    ((sLocalBruhatPure F S φ).comp (replaceCoordinate F S i f))

private theorem replaceClass_apply (φ : Arch F) (i : S) (f : ∀ w : S, FinTest F w.val)
    (g : FinTest F i.val) :
    replaceClass F S φ i f g = pureClass F S φ (Function.update f i g) := rfl

private theorem translate_mul {K : Type*} [NormedField K] (a b : Kˣ)
    (f : locallyConstantTests K) :
    locallyConstantTestTranslate K a (locallyConstantTestTranslate K b f) =
      locallyConstantTestTranslate K (a * b) f := by
  apply Subtype.ext
  funext x
  change f.val (b.inv * (a.inv * x)) = f.val ((a * b).inv * x)
  rw [← mul_assoc]
  rfl

private theorem translate_one {K : Type*} [NormedField K] (f : locallyConstantTests K) :
    locallyConstantTestTranslate K (1 : Kˣ) f = f := by
  apply Subtype.ext
  funext x
  change f.val (1 * x) = f.val x
  rw [one_mul]

private theorem translate_preserves_invariant {K : Type*} [NormedField K] (H : Subgroup Kˣ)
    (a : Kˣ) (f : locallyConstantTests K)
    (hf : ∀ u : H, ∀ x : K, f.val (u.val.val * x) = f.val x) :
    ∀ u : H, ∀ x : K, (locallyConstantTestTranslate K a f).val (u.val.val * x) =
      (locallyConstantTestTranslate K a f).val x := by
  intro u x
  change f.val (a.inv * (u.val.val * x)) = f.val (a.inv * x)
  rw [mul_left_comm, hf]

private theorem ballCompact (v : Place F) : IsCompact (Metric.closedBall (0 : v.adicCompletion F) 1) := by
  rw [finiteCompletion_closedBall]
  exact finitePlaceIntegral_compact F v

private theorem ballOpen (v : Place F) : IsOpen (Metric.closedBall (0 : v.adicCompletion F) 1) := by
  rw [finiteCompletion_closedBall]
  exact Valued.isOpen_valuationSubring _

private def unitBall (v : Place F) : FinTest F v :=
  compactOpenIndicator _ ⟨_, ballCompact F v, ballOpen F v⟩

private theorem unitBall_translate (v : Place F) (a : (v.adicCompletion F)ˣ)
    (ha : ‖a.val‖ = 1) :
    locallyConstantTestTranslate _ a (unitBall F v) = unitBall F v := by
  apply Subtype.ext
  funext x
  change (Metric.closedBall (0 : v.adicCompletion F) 1).indicator (fun _ => (1 : ℂ)) (a.inv * x) =
    (Metric.closedBall (0 : v.adicCompletion F) 1).indicator (fun _ => (1 : ℂ)) x
  simp only [indicator_apply, Metric.mem_closedBall, dist_zero_right, norm_mul,
    show a.inv = a.val⁻¹ from Units.val_inv_eq_inv_val a, norm_inv, ha, inv_one, one_mul]

private def template (v : Place F) (p : (v.adicCompletion F)ˣ)
    (H : Subgroup (v.adicCompletion F)ˣ) : Submodule ℂ (FinTest F v) :=
  ℂ ∙ unitBall F v ⊔ thetaAnnulusInvariant p H

private theorem template_finite (v : Place F) (p : (v.adicCompletion F)ˣ)
    (H : Subgroup (v.adicCompletion F)ˣ) (hH : IsOpen (H : Set (v.adicCompletion F)ˣ)) :
    FiniteDimensional ℂ (template F v p H) := by
  letI := thetaAnnulusInvariant_finiteDimensional p (ballCompact F v) (ballOpen F v) H hH
  unfold template
  infer_instance

private theorem template_unitBall (v : Place F) (p : (v.adicCompletion F)ˣ)
    (H : Subgroup (v.adicCompletion F)ˣ) : unitBall F v ∈ template F v p H :=
  (show ℂ ∙ unitBall F v ≤ template F v p H from le_sup_left) (Submodule.mem_span_singleton_self _)

private theorem template_annulus_mem (v : Place F) (p : (v.adicCompletion F)ˣ)
    (H : Subgroup (v.adicCompletion F)ˣ) : thetaAnnulusInvariant p H ≤ template F v p H :=
  le_sup_right

private theorem template_normOne (v : Place F) (p : (v.adicCompletion F)ˣ)
    (H : Subgroup (v.adicCompletion F)ˣ) (a : (v.adicCompletion F)ˣ) (ha : ‖a.val‖ = 1)
    (f : FinTest F v) (hf : f ∈ template F v p H) :
    locallyConstantTestTranslate _ a f ∈ template F v p H := by
  let L := locallyConstantTestTranslate (v.adicCompletion F) a
  have he : template F v p H ≤ (template F v p H).comap L := by
    apply sup_le
    · apply Submodule.span_le.mpr
      intro b hb
      obtain rfl : b = unitBall F v := hb
      change L (unitBall F v) ∈ template F v p H
      rw [show L (unitBall F v) = unitBall F v from unitBall_translate F v a ha]
      exact template_unitBall F v p H
    · intro b hb
      exact template_annulus_mem F v p H (thetaAnnulusInvariant_translate_mem p H a ha hb)
  exact he hf

private def invariantLocal (w : S) (H : Subgroup (w.val.adicCompletion F)ˣ) :
    Submodule ℂ (FinTest F w.val) where
  carrier := {f | ∀ (h : H) (x : w.val.adicCompletion F), f.val (h.val.val * x) = f.val x}
  zero_mem' := fun _ _ ↦ rfl
  add_mem' hf hg := fun h x ↦ by simp only [Submodule.coe_add, Pi.add_apply, hf h x, hg h x]
  smul_mem' c _ hf := fun h x ↦ by simp only [Submodule.coe_smul, Pi.smul_apply, hf h x]

private theorem template_invariant (w : S) (p : (w.val.adicCompletion F)ˣ)
    (H : Subgroup (w.val.adicCompletion F)ˣ) (hn : ∀ h : H, ‖h.val.val‖ = 1) :
    template F w.val p H ≤ invariantLocal F S w H := by
  apply sup_le
  · apply Submodule.span_le.mpr
    rintro _ rfl h x
    have he := congrArg (fun f : FinTest F w.val ↦ f.val x)
      (unitBall_translate F w.val h.val⁻¹ (by
        rw [Units.val_inv_eq_inv_val, norm_inv, hn h, inv_one]))
    change (unitBall F w.val).val ((↑((h.val⁻¹)⁻¹) : w.val.adicCompletion F) * x) =
      (unitBall F w.val).val x at he
    rwa [inv_inv] at he
  · exact fun f hf ↦ hf.2

private def templateClasses (A : ∀ w : S, Submodule ℂ (FinTest F w.val)) : Submodule ℂ (Theta F S) :=
  Submodule.span ℂ {q | ∃ (φ : Arch F) (f : ∀ w : S, FinTest F w.val),
    (∀ w, f w ∈ A w) ∧ q = pureClass F S φ f}

private theorem templateClasses_mem (A : ∀ w : S, Submodule ℂ (FinTest F w.val))
    (φ : Arch F) (f : ∀ w : S, FinTest F w.val) (hf : ∀ w, f w ∈ A w) :
    pureClass F S φ f ∈ templateClasses F S A :=
  Submodule.subset_span ⟨φ, f, hf, rfl⟩

private theorem finiteUnit_norm_pow_one (u : (sIntegerRing F S)ˣ)
    (w : S) (hu : ‖(finiteUnit F S (localPrincipal F S u) w).val‖ = 1) (n : ℤ) :
    ‖(finiteUnit F S (localPrincipal F S (u ^ n)) w).val‖ = 1 := by
  rw [finiteUnit_principal_pow, Units.val_zpow_eq_zpow_val, norm_zpow, hu, one_zpow]

set_option maxHeartbeats 600000 in
private theorem reduce_invariant_products
    (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
    (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
    (hnorm : ∀ (w : S) (h : H w), ‖h.val.val‖ = 1)
    (u : S → (sIntegerRing F S)ˣ)
    (hc : ∀ i : S, ‖(finiteUnit F S (localPrincipal F S (u i)) i).val‖ < 1)
    (hu : ∀ (i w : S), w ≠ i → ‖(finiteUnit F S (localPrincipal F S (u i)) w).val‖ = 1)
    (t : Finset S) (φ : Arch F) (f : ∀ w : S, FinTest F w.val)
    (hf : ∀ (w : S), w ∈ t → ∀ (h : H w) x, (f w).val (h.val.val * x) = (f w).val x)
    (ht : ∀ (w : S), w ∉ t →
      f w ∈ template F w.val (finiteUnit F S (localPrincipal F S (u w)) w) (H w)) :
    pureClass F S φ f ∈ templateClasses F S
      (fun w ↦ template F w.val (finiteUnit F S (localPrincipal F S (u w)) w) (H w)) := by
  let p (w : S) := finiteUnit F S (localPrincipal F S (u w)) w
  let A (w : S) := template F w.val (p w) (H w)
  let P := templateClasses F S A
  change pureClass F S φ f ∈ P
  induction t using Finset.induction_on generalizing φ f with
  | empty =>
    exact templateClasses_mem F S A φ f (fun w ↦ ht w (Finset.notMem_empty _))
  | insert i t hi ih =>
    let L := replaceClass F S φ i f
    have hterm (n : ℤ) (a : FinTest F i.val) (ha : a ∈ A i) :
        L (locallyConstantTestTranslate _ (p i ^ n) a) ∈ P := by
      let g := localPrincipal F S ((u i) ^ (-n))
      let f₀ := Function.update f i (locallyConstantTestTranslate _ (p i ^ n) a)
      let f₁ := sLocalFinitePiTranslate F S g f₀
      change pureClass F S φ f₀ ∈ P
      rw [← pureClass_principal F S ((u i) ^ (-n)) φ f₀]
      change pureClass F S (sLocalArchPullback F S g φ) f₁ ∈ P
      apply ih
      · intro w hw b x
        have hwi : w ≠ i := fun e ↦ hi (e ▸ hw)
        change (locallyConstantTestTranslate _ (finiteUnit F S g w) (f₀ w)).val _ =
          (locallyConstantTestTranslate _ (finiteUnit F S g w) (f₀ w)).val x
        dsimp only [f₀]
        simp only [Function.update_of_ne hwi]
        exact translate_preserves_invariant (H w) _ _ (hf w (Finset.mem_insert_of_mem hw)) b x
      · intro w hw
        by_cases hwi : w = i
        · subst w
          have he : f₁ i = a := by
            change locallyConstantTestTranslate _ (finiteUnit F S g i) (f₀ i) = a
            have hpow : finiteUnit F S g i = p i ^ (-n) :=
              finiteUnit_principal_pow F S (u i) (-n) i
            dsimp only [f₀]
            rw [Function.update_self, hpow, translate_mul, zpow_neg, inv_mul_cancel, translate_one]
          rw [he]
          exact ha
        · have hnot : w ∉ insert i t := by simp [hwi, hw]
          change locallyConstantTestTranslate _ (finiteUnit F S g w) (f₀ w) ∈ A w
          dsimp only [f₀]
          rw [Function.update_of_ne hwi]
          exact template_normOne F w.val (p w) (H w) _
            (finiteUnit_norm_pow_one F S (u i) w (hu i w hwi) (-n)) _ (ht w hnot)
    obtain ⟨_, M, N, a, he⟩ := thetaShell_invariant_normalForm (p i)
      (ballCompact F i.val) (ballOpen F i.val) (hc i) (H i) (hH i) (hnorm i)
      (f i) (hf i (Finset.mem_insert_self _ _))
    have hL : L (f i) = pureClass F S φ f := by
      change replaceClass F S φ i f (f i) = _
      rw [replaceClass_apply, Function.update_eq_self]
    rw [← hL, he, map_add, map_smul, map_sum]
    refine P.add_mem (P.smul_mem _ (hterm (N : ℤ) _ (template_unitBall F i.val (p i) (H i))))
      (P.sum_mem fun j _ ↦ hterm (-(M : ℤ) + (j : ℤ)) _ (template_annulus_mem F i.val (p i) (H i) (a j).property))

/-- For fixed open integral-unit stabilizers, products of invariant finite
tests reduce in the theta quotient to products from finite-dimensional
template spaces. The shell dilations are absorbed by S-unit translations. -/
theorem sLocalTheta_reduce_invariant_products
    (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
    (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
    (hnorm : ∀ (w : S) (h : H w), ‖h.val.val‖ = 1) :
    ∃ A : ∀ w : S, Submodule ℂ (FinTest F w.val),
      (∀ w, FiniteDimensional ℂ (A w)) ∧ (∀ w, A w ≤ invariantLocal F S w (H w)) ∧
      ∀ (φ : Arch F) (f : ∀ w : S, FinTest F w.val),
        (∀ (w : S) (h : H w) x, (f w).val (h.val.val * x) = (f w).val x) →
        pureClass F S φ f ∈ templateClasses F S A := by
  choose u hu using exists_sUnit_contracts_one_place F S
  let p (w : S) := finiteUnit F S (localPrincipal F S (u w)) w
  refine ⟨fun w ↦ template F w.val (p w) (H w),
    fun w ↦ template_finite F w.val (p w) (H w) (hH w),
    fun w ↦ template_invariant F S w (p w) (H w) (hnorm w), fun φ f hf ↦ ?_⟩
  apply reduce_invariant_products F S H hH hnorm u (fun i ↦ (hu i).1)
    (fun i w he ↦ (hu i).2 w.val (fun e ↦ he (Subtype.ext e))) Finset.univ φ f
  · exact fun w _ ↦ hf w
  · exact fun w hw ↦ (hw (Finset.mem_univ w)).elim

private def thetaSlice (ψ : locallyConstantTests ((w : S) → w.val.adicCompletion F)) :
    Arch F →L[ℂ] Theta F S :=
  (sLocalThetaOperator F S).ker.mkQL.comp
    ⟨(sLocalBruhatPure F S).flip ψ, (GlobalBruhat.pure_continuous F _).subtype_mk _⟩

/-- A finite product of archimedean Schwartz spaces continuously parametrizes
the span of theta classes of the fixed integral-unit invariant pure tests.
The finite-coordinate inputs of the parametrization are fixed in advance. -/
theorem sLocalTheta_invariant_products_factor_finite_with_lift
    (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
    (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
    (hnorm : ∀ (w : S) (h : H w), ‖h.val.val‖ = 1) :
    ∃ (J : Type u) (L : (J → Arch F) →L[ℂ] Theta F S), Finite J ∧
      L.toLinearMap.range ≤ templateClasses F S (fun w ↦ invariantLocal F S w (H w)) ∧
      (∀ (φ : Arch F) (f : ∀ w : S, FinTest F w.val),
        (∀ (w : S) (h : H w) x, (f w).val (h.val.val * x) = (f w).val x) →
        pureClass F S φ f ∈ range L) ∧
      ∃ U : (J → Arch F) →L[ℂ] sLocalBruhatImage F S,
        (sLocalThetaOperator F S).ker.mkQL.comp U = L := by
  obtain ⟨A, hA, haInv, hr⟩ := sLocalTheta_reduce_invariant_products F S H hH hnorm
  letI (w : S) : FiniteDimensional ℂ (A w) := hA w
  letI (w : S) : Module.Free ℂ (A w) := Module.Free.of_divisionRing ℂ (A w)
  let I (w : S) := Fin (Module.finrank ℂ (A w))
  let b (w : S) : Module.Basis (I w) ℂ (A w) := Module.finBasis ℂ (A w)
  let J := ∀ w : S, I w
  let ψ (j : J) := locallyConstantTestPiProduct (fun w ↦ ((b w) (j w)).val)
  let L : (J → Arch F) →L[ℂ] Theta F S :=
    ∑ j : J, (thetaSlice F S (ψ j)).comp (ContinuousLinearMap.proj j)
  have hmem : templateClasses F S A ≤ L.toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, f, hf, rfl⟩
    let c (w : S) := (b w).repr ⟨f w, hf w⟩
    have hval (w : S) (x : w.val.adicCompletion F) :
        (f w).val x = ∑ j : I w, c w j * ((b w) j).val.val x := by
      have he := congrArg (fun g : A w ↦ g.val.val x) ((b w).sum_repr ⟨f w, hf w⟩)
      exact (show (∑ j : I w, c w j * ((b w) j).val.val x) = (f w).val x from by
        simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, c] using he).symm
    have hψ : locallyConstantTestPiProduct f =
        ∑ j : J, (∏ w : S, c w (j w)) • ψ j := by
      apply Subtype.ext
      funext x
      simp only [locallyConstantTestPiProduct_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ψ]
      simp_rw [hval]
      rw [Fintype.prod_sum]
      exact Finset.sum_congr rfl (fun j _ ↦ Finset.prod_mul_distrib)
    refine ⟨fun j ↦ (∏ w : S, c w (j w)) • φ, ?_⟩
    change L _ = pureClass F S φ f
    have hL : L (fun j ↦ (∏ w : S, c w (j w)) • φ) =
        ∑ j : J, (∏ w : S, c w (j w)) • thetaSlice F S (ψ j) φ := by
      simp only [L, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, map_smul]
    rw [hL]
    unfold pureClass
    rw [hψ, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [map_smul, map_smul]
      rfl
  refine ⟨J, L, inferInstance, ?_, fun φ f hf ↦ hmem (hr φ f hf), ?_⟩
  · rintro _ ⟨g, rfl⟩
    change L g ∈ templateClasses F S (fun w ↦ invariantLocal F S w (H w))
    simp only [L, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    exact (templateClasses F S _).sum_mem fun j _ ↦
      templateClasses_mem F S _ (g j) _ (fun w ↦ haInv w ((b w) (j w)).property)
  · let U (j : J) : Arch F →L[ℂ] sLocalBruhatImage F S :=
      ⟨(sLocalBruhatPure F S).flip (ψ j), (GlobalBruhat.pure_continuous F _).subtype_mk _⟩
    refine ⟨∑ j : J, (U j).comp (ContinuousLinearMap.proj j), ?_⟩
    ext g
    simp only [L, sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, map_sum]
    rfl

theorem sLocalTheta_invariant_products_factor_finite
    (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
    (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
    (hnorm : ∀ (w : S) (h : H w), ‖h.val.val‖ = 1) :
    ∃ (J : Type u) (L : (J → Arch F) →L[ℂ] Theta F S), Finite J ∧
      L.toLinearMap.range ≤ templateClasses F S (fun w ↦ invariantLocal F S w (H w)) ∧
      (∀ (φ : Arch F) (f : ∀ w : S, FinTest F w.val),
        (∀ (w : S) (h : H w) x, (f w).val (h.val.val * x) = (f w).val x) →
        pureClass F S φ f ∈ range L) := by
  obtain ⟨J, L, hJ, hsub, hL, _⟩ :=
    sLocalTheta_invariant_products_factor_finite_with_lift F S H hH hnorm
  exact ⟨J, L, hJ, hsub, hL⟩

private abbrev Coordinates := (w : S) → w.val.adicCompletion F
private abbrev ProductTest := locallyConstantTests (Coordinates F S)

/-- Invariance in a single finite coordinate under an integral-unit subgroup. -/
def thetaFiniteInvariantAt (w : S) (H : Subgroup (w.val.adicCompletion F)ˣ)
    (ψ : ProductTest F S) : Prop :=
  ∀ (h : H) (x : Coordinates F S) (a : w.val.adicCompletion F),
    ψ.val (Function.update x w (h.val.val * a)) = ψ.val (Function.update x w a)

private theorem exists_invariantProjection (w : S) (H : Subgroup (w.val.adicCompletion F)ˣ) :
    ∃ L : FinTest F w.val →ₗ[ℂ] FinTest F w.val,
      (∀ f, L f ∈ invariantLocal F S w H) ∧
      (∀ f, f ∈ invariantLocal F S w H → L f = f) := by
  let V := invariantLocal F S w H
  let j : V →ₗ[ℂ] FinTest F w.val := V.subtype
  have hj : j.ker = ⊥ := V.ker_subtype
  obtain ⟨R, hR⟩ := LinearMap.exists_leftInverse_of_injective
    (V := V) (V' := FinTest F w.val) j hj
  refine ⟨V.subtype.comp R, fun f ↦ (R f).property, ?_⟩
  intro f hf
  exact congrArg Subtype.val (DFunLike.congr_fun hR (⟨f, hf⟩ : V))

private theorem coordinateMap_fixes (w : S) (H : Subgroup (w.val.adicCompletion F)ˣ)
    (L : FinTest F w.val →ₗ[ℂ] FinTest F w.val)
    (hL : ∀ f, f ∈ invariantLocal F S w H → L f = f)
    (ψ : ProductTest F S) (hψ : thetaFiniteInvariantAt F S w H ψ) :
    sLocalCoordinateMap F S w L ψ = ψ := by
  apply Subtype.ext
  funext x
  rw [sLocalCoordinateMap_apply]
  have he (q : FinTest F w.val) (hq : ∀ a, q.val a = ψ.val (Function.update x w a)) :
      (L q).val (x w) = ψ.val x := by
    rw [hL q (fun h a ↦ by rw [hq, hq]; exact hψ h x a), hq, Function.update_eq_self]
  exact he _ (sLocalCoordinateSection_apply F S w ψ x)

private theorem coordinateMap_piProduct (w : S)
    (L : FinTest F w.val →ₗ[ℂ] FinTest F w.val) (f : ∀ w : S, FinTest F w.val) :
    sLocalCoordinateMap F S w L (locallyConstantTestPiProduct f) =
      locallyConstantTestPiProduct (Function.update f w (L (f w))) := by
  apply Subtype.ext
  funext x
  rw [sLocalCoordinateMap_apply, replaceProduct_apply]
  let c := ∏ i ∈ Finset.univ.erase w, (f i).val (x i)
  have he (q : FinTest F w.val)
      (hq : ∀ a, q.val a = (locallyConstantTestPiProduct f).val (Function.update x w a)) :
      (L q).val (x w) = (L (f w)).val (x w) * c := by
    have hq' : q = c • f w := by
      apply Subtype.ext
      funext a
      rw [hq, locallyConstantTestPiProduct_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ w),
        Function.update_self]
      change (f w).val a * _ = c * (f w).val a
      rw [mul_comm c]
      congr 1
      exact Finset.prod_congr rfl
        (fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    rw [hq', map_smul]
    exact mul_comm _ _
  exact he _ (sLocalCoordinateSection_apply F S w (locallyConstantTestPiProduct f) x)

private theorem invariant_factors_span
    (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
    (ψ : ProductTest F S) (hψ : ∀ w, thetaFiniteInvariantAt F S w (H w) ψ) :
    ψ ∈ Submodule.span ℂ {g : ProductTest F S | ∃ f : ∀ w : S, FinTest F w.val,
      (∀ w, f w ∈ invariantLocal F S w (H w)) ∧ g = locallyConstantTestPiProduct f} := by
  choose P hP hfix using fun w ↦ exists_invariantProjection F S w (H w)
  let R (w : S) := sLocalCoordinateMap F S w (P w)
  have exists_Q (t : Finset S) :
      ∃ Q : ProductTest F S →ₗ[ℂ] ProductTest F S,
        (∀ f, (∀ w ∈ t, thetaFiniteInvariantAt F S w (H w) f) → Q f = f) ∧
        (∀ f : ∀ w : S, FinTest F w.val,
          ∃ g : ∀ w : S, FinTest F w.val, (∀ w ∈ t, g w ∈ invariantLocal F S w (H w)) ∧
            Q (locallyConstantTestPiProduct f) = locallyConstantTestPiProduct g) := by
    induction t using Finset.induction_on with
    | empty => exact ⟨LinearMap.id, fun _ _ ↦ rfl, fun f ↦ ⟨f, by simp, rfl⟩⟩
    | insert i t hi ih =>
      obtain ⟨Q, hQ, hgen⟩ := ih
      refine ⟨(R i).comp Q, ?_, ?_⟩
      · intro f hf
        change R i (Q f) = f
        rw [hQ f (fun w hw ↦ hf w (Finset.mem_insert_of_mem hw))]
        exact coordinateMap_fixes F S i (H i) (P i) (hfix i) f (hf i (Finset.mem_insert_self _ _))
      · intro f
        obtain ⟨g, hg, hQg⟩ := hgen f
        refine ⟨Function.update g i (P i (g i)), ?_, ?_⟩
        · intro w hw
          by_cases he : w = i
          · subst w
            rw [Function.update_self]
            exact hP i _
          · rw [Function.update_of_ne he]
            exact hg w ((Finset.mem_insert.mp hw).resolve_left he)
        · change R i (Q (locallyConstantTestPiProduct f)) = _
          rw [hQg]
          exact coordinateMap_piProduct F S i (P i) g
  obtain ⟨Q, hQ, hgen⟩ := exists_Q Finset.univ
  let V : Submodule ℂ (ProductTest F S) :=
    Submodule.span ℂ {g : ProductTest F S | ∃ f : ∀ w : S, FinTest F w.val,
      (∀ w, f w ∈ invariantLocal F S w (H w)) ∧ g = locallyConstantTestPiProduct f}
  have he : Submodule.span ℂ (range (locallyConstantTestPiProduct
      (X := fun w : S ↦ w.val.adicCompletion F))) ≤ V.comap Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, hg, he⟩ := hgen f
    change Q (locallyConstantTestPiProduct f) ∈ V
    rw [he]
    exact Submodule.subset_span ⟨g, fun w ↦ hg w (Finset.mem_univ _), rfl⟩
  have hm : Q ψ ∈ V := he (by rw [locallyConstantTest_span_piProduct]; exact Submodule.mem_top)
  rwa [hQ ψ (fun w _ ↦ hψ w)] at hm

/-- The span of theta classes represented by finite tests invariant in
each coordinate under the indicated subgroup. -/
def sLocalThetaInvariantTestSpan (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ) :
    Submodule ℂ (Theta F S) :=
  Submodule.span ℂ {q | ∃ (φ : Arch F) (ψ : ProductTest F S),
    (∀ w, thetaFiniteInvariantAt F S w (H w) ψ) ∧
    q = (sLocalThetaOperator F S).ker.mkQ (sLocalBruhatPure F S φ ψ)}

private theorem piProduct_invariantAt (w : S) (H : Subgroup (w.val.adicCompletion F)ˣ)
    (f : ∀ i : S, FinTest F i.val) (hf : f w ∈ invariantLocal F S w H) :
    thetaFiniteInvariantAt F S w H (locallyConstantTestPiProduct f) := by
  intro h x a
  simp only [locallyConstantTestPiProduct_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), ← Finset.mul_prod_erase
    (f := fun i ↦ (f i).val (Function.update x w a i)) _ (Finset.mem_univ w)]
  simp only [Function.update_self, hf h a]
  congr 1
  exact Finset.prod_congr rfl fun i hi ↦ by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi), Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- At fixed integral-unit levels, all theta classes represented by finite
tests invariant in every coordinate admit one continuous parametrization
from a finite product of archimedean Schwartz spaces. -/
theorem sLocalTheta_invariant_finiteTests_factor_with_lift
    (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
    (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
    (hnorm : ∀ (w : S) (h : H w), ‖h.val.val‖ = 1) :
    ∃ (J : Type u) (L : (J → Arch F) →L[ℂ] Theta F S), Finite J ∧
      L.toLinearMap.range = sLocalThetaInvariantTestSpan F S H ∧
      ∃ U : (J → Arch F) →L[ℂ] sLocalBruhatImage F S,
        (sLocalThetaOperator F S).ker.mkQL.comp U = L := by
  obtain ⟨J, L, hJ, hrev, hL, hU⟩ := sLocalTheta_invariant_products_factor_finite_with_lift F S H hH hnorm
  refine ⟨J, L, hJ, le_antisymm (hrev.trans ?_) ?_, hU⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨φ, f, hf, rfl⟩
    exact Submodule.subset_span ⟨φ, locallyConstantTestPiProduct f,
      fun w ↦ piProduct_invariantAt F S w (H w) f (hf w), rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨φ, ψ, hψ, rfl⟩
    let Θ := (sLocalThetaOperator F S).ker.mkQ.comp (sLocalBruhatPure F S φ)
    have he : Submodule.span ℂ {g : ProductTest F S | ∃ f : ∀ w : S, FinTest F w.val,
        (∀ w, f w ∈ invariantLocal F S w (H w)) ∧ g = locallyConstantTestPiProduct f} ≤
        L.toLinearMap.range.comap Θ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨f, hf, rfl⟩
      exact hL φ f hf
    exact he (invariant_factors_span F S H ψ hψ)

theorem sLocalTheta_invariant_finiteTests_factor
    (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ)
    (hH : ∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ))
    (hnorm : ∀ (w : S) (h : H w), ‖h.val.val‖ = 1) :
    ∃ (J : Type u) (L : (J → Arch F) →L[ℂ] Theta F S), Finite J ∧
      L.toLinearMap.range = sLocalThetaInvariantTestSpan F S H := by
  obtain ⟨J, L, hJ, hL, _⟩ := sLocalTheta_invariant_finiteTests_factor_with_lift F S H hH hnorm
  exact ⟨J, L, hJ, hL⟩


theorem sLocalThetaInvariantTestSpan_antitone
    {H G : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ} (h : ∀ w, H w ≤ G w) :
    sLocalThetaInvariantTestSpan F S G ≤ sLocalThetaInvariantTestSpan F S H := by
  apply Submodule.span_le.mpr
  rintro _ ⟨φ, ψ, hψ, rfl⟩
  exact Submodule.subset_span ⟨φ, ψ, fun w u x a ↦ hψ w ⟨u.val, h w u.property⟩ x a, rfl⟩

theorem sLocalThetaFiniteTests_have_invariant_levels (ψ : ProductTest F S) :
    ∃ H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ,
      (∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ)) ∧
      (∀ (w : S) (h : H w), ‖h.val.val‖ = 1) ∧
      ∀ w, thetaFiniteInvariantAt F S w (H w) ψ := by
  have hψ : ψ ∈ Submodule.span ℂ (range (locallyConstantTestPiProduct
      (X := fun w : S ↦ w.val.adicCompletion F))) := by
    rw [locallyConstantTest_span_piProduct]
    exact Submodule.mem_top
  induction hψ using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f, rfl⟩ := hg
    choose H hH hnorm hf using fun w ↦
      thetaTests_exists_open_integralStabilizer (ballOpen F w.val) {f w}
    exact ⟨H, hH, hnorm, fun w ↦
      piProduct_invariantAt F S w (H w) f (hf w _ (Finset.mem_singleton_self _))⟩
  | zero =>
    choose H hH hn _ using fun w : S ↦
      thetaTests_exists_open_integralStabilizer (ballOpen F w.val) (∅ : Finset (FinTest F w.val))
    exact ⟨H, hH, hn, fun _ _ _ _ ↦ rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨H, hH, hn, hf'⟩ := hf
    obtain ⟨G, hG, _, hg'⟩ := hg
    refine ⟨fun w ↦ H w ⊓ G w, fun w ↦ (hH w).inter (hG w),
      fun w u ↦ hn w ⟨u.val, u.property.1⟩, fun w u x a ↦ ?_⟩
    simp only [Submodule.coe_add, Pi.add_apply, hf' w ⟨u.val, u.property.1⟩ x a,
      hg' w ⟨u.val, u.property.2⟩ x a]
  | smul c f _ hf =>
    obtain ⟨H, hH, hn, hf'⟩ := hf
    refine ⟨H, hH, hn, fun w u x a ↦ ?_⟩
    simp only [Submodule.coe_smul, Pi.smul_apply, hf' w u x a]

/-- The integral-unit invariant test spans exhaust the S-local theta
quotient. This includes theta classes represented by coupled finite tests. -/
theorem sLocalThetaInvariantTestSpan_exhaust (q : Theta F S) :
    ∃ H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ,
      (∀ w : S, IsOpen (H w : Set (w.val.adicCompletion F)ˣ)) ∧
      (∀ (w : S) (h : H w), ‖h.val.val‖ = 1) ∧
      q ∈ sLocalThetaInvariantTestSpan F S H := by
  letI : TopologicalSpace (ProductTest F S) := finestLocallyConvexTopology _
  letI : TopologicalSpace (Arch F ⊗[ℂ] ProductTest F S) := inductiveTensorTopology _ _
  let e := sLocalBruhatTensorEquiv F S
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (sLocalThetaOperator F S).ker q
  obtain ⟨a, rfl⟩ := e.surjective f
  let L := (sLocalThetaOperator F S).ker.mkQ.comp e.toLinearEquiv.toLinearMap
  change ∃ H, _ ∧ _ ∧ L a ∈ sLocalThetaInvariantTestSpan F S H
  induction a using TensorProduct.induction_on with
  | zero =>
    obtain ⟨H, hH, hn, _⟩ := sLocalThetaFiniteTests_have_invariant_levels F S 0
    exact ⟨H, hH, hn, by rw [map_zero]; exact Submodule.zero_mem _⟩
  | add a b ha hb =>
    obtain ⟨H, hH, hn, hHa⟩ := ha
    obtain ⟨G, hG, _, hGb⟩ := hb
    refine ⟨fun w ↦ H w ⊓ G w, fun w ↦ (hH w).inter (hG w),
      fun w u ↦ hn w ⟨u.val, u.property.1⟩, ?_⟩
    rw [map_add]
    exact Submodule.add_mem _
      (sLocalThetaInvariantTestSpan_antitone F S (fun _ ↦ inf_le_left) hHa)
      (sLocalThetaInvariantTestSpan_antitone F S (fun _ ↦ inf_le_right) hGb)
  | tmul φ ψ =>
    obtain ⟨H, hH, hn, hψ⟩ := sLocalThetaFiniteTests_have_invariant_levels F S ψ
    exact ⟨H, hH, hn, Submodule.subset_span ⟨φ, ψ, hψ, rfl⟩⟩

end

end Masullo
