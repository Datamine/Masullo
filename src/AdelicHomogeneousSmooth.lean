import AdelicThetaDecay
import ArchimedeanIdeleExponential
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ContDiff NumberField SchwartzMap

namespace Masullo

noncomputable section

private theorem hasFDerivAt_fin_of_continuous_partials
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (f : (Fin n → ℝ) → E) (p : Fin n → (Fin n → ℝ) → E)
    (hp : ∀ i, Continuous (p i))
    (hd : ∀ x i, HasDerivAt (fun t : ℝ => f (Function.update x i t)) (p i x) (x i)) :
    ∀ x, HasFDerivAt f (∑ i, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (p i x)) x := by
  classical
  induction n with
  | zero =>
    intro x
    have he : f = fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
    rw [he, Finset.univ_eq_empty, Finset.sum_empty]
    exact hasFDerivAt_const _ _
  | succ n ih =>
    let e := Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)
    let g (a : ℝ) (v : Fin n → ℝ) := f (Fin.cons a v)
    let p₁ (a : ℝ) (v : Fin n → ℝ) :=
      (ContinuousLinearMap.id ℝ ℝ).smulRight (p 0 (Fin.cons a v))
    let p₂ (a : ℝ) (v : Fin n → ℝ) :=
      ∑ i : Fin n, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
        (p i.succ (Fin.cons a v))
    have he : Continuous (fun z : ℝ × (Fin n → ℝ) =>
        (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ)) := e.continuous
    have hd₁ (z : ℝ × (Fin n → ℝ)) :
        HasFDerivAt (g · z.2) (p₁ z.1 z.2) z.1 := by
      have h := hd (Fin.cons z.1 z.2) 0
      simp_rw [Fin.update_cons_zero, Fin.cons_zero] at h
      exact h.hasFDerivAt
    have hd₂ (z : ℝ × (Fin n → ℝ)) :
        HasFDerivAt (g z.1) (p₂ z.1 z.2) z.2 := by
      apply ih (g z.1) (fun i v => p i.succ (Fin.cons z.1 v))
      · intro i
        exact (hp i.succ).comp (he.comp (continuous_const.prodMk continuous_id))
      · intro v i
        have h := hd (Fin.cons z.1 v) i.succ
        simpa only [g, ← Fin.cons_update, Fin.cons_succ] using h
    have hc₁ : Continuous (Function.uncurry p₁) :=
      ((ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous).comp
        ((hp 0).comp he)
    have hc₂ : Continuous (Function.uncurry p₂) :=
      continuous_finsetSum _ fun i _ =>
        ((ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) E
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)).continuous).comp
          ((hp i.succ).comp he)
    intro x
    let z := e.symm x
    have h := (hasStrictFDerivAt_uncurry_coprod (f := g) (f₁ := p₁) (f₂ := p₂)
      (u := z) (Eventually.of_forall hd₁) (Eventually.of_forall hd₂)
      hc₁.continuousAt hc₂.continuousAt).hasFDerivAt.comp x e.symm.hasFDerivAt
    have hfun : (Function.uncurry g ∘ e.symm) = f :=
      funext fun v => congrArg f (e.apply_symm_apply v)
    have h' : HasFDerivAt f ((p₁ z.1 z.2).coprod (p₂ z.1 z.2) ∘L e.symm.toContinuousLinearMap) x :=
      h.congr_of_eventuallyEq (Eventually.of_forall fun v => (congrFun hfun v).symm)
    convert h' using 1
    ext v
    simp only [sum_apply, add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
      p₁, p₂, ContinuousLinearMap.id_apply, Fin.sum_univ_succ, add_apply]
    have hz : (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) = x := e.apply_symm_apply x
    rw [hz]
    rfl

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F

local instance homogeneousSmoothMeasurable : MeasurableSpace (K F) := borel _
local instance homogeneousSmoothBorel : BorelSpace (K F) := ⟨rfl⟩

/-- The directional identity in the original positive-real parameter at one. -/
theorem adelicHomogeneousTheta_positive_hasDerivAt
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (q : IdeleClass F) :
    HasDerivAt (fun t : ℝ => adelicHomogeneousTheta F ν χ f.val
      (ideleClassMap F (γ (Multiplicative.ofAdd (Real.log t))) * q))
      (adelicHomogeneousTheta F ν χ (algebraicBruhatDeriv F γ hγ f).val q) 1 := by
  let a (t : ℝ) := ideleClassMap F (γ (Multiplicative.ofAdd t)) * q
  have ha : a 0 = q := by
    change ideleClassMap F (γ 1) * q = q
    rw [map_one, map_one]
    exact one_mul q
  have hl : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log (one_ne_zero (α := ℝ))
  have hd := adelicHomogeneousTheta_log_hasDerivAt F γ hγ ν χ f q 0
  change HasDerivAt (fun t : ℝ => adelicHomogeneousTheta F ν χ f.val (a t))
    (adelicHomogeneousTheta F ν χ (algebraicBruhatDeriv F γ hγ f).val (a 0)) 0 at hd
  rw [ha] at hd
  have hp : Real.log 1 = 0 := Real.log_one
  have hd' : HasDerivAt (fun t : ℝ => adelicHomogeneousTheta F ν χ f.val (a t))
    (adelicHomogeneousTheta F ν χ (algebraicBruhatDeriv F γ hγ f).val q) (Real.log 1) :=
      hp.symm ▸ hd
  simpa only [Function.comp_def, one_smul, a] using hd'.scomp 1 hl

/-- Logarithmic derivatives of the homogeneous theta average are obtained by
iterating the test-space directional derivative. -/
theorem adelicHomogeneousTheta_log_iteratedDeriv
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (q : IdeleClass F) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => adelicHomogeneousTheta F ν χ f.val
      (ideleClassMap F (γ (Multiplicative.ofAdd t)) * q)) =
      fun t : ℝ => adelicHomogeneousTheta F ν χ
        (((algebraicBruhatDeriv F γ hγ)^[n]) f).val
        (ideleClassMap F (γ (Multiplicative.ofAdd t)) * q) := by
  induction n with
  | zero => rw [iteratedDeriv_zero]; rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Function.iterate_succ_apply']
    exact (adelicHomogeneousTheta_log_hasDerivAt F γ hγ ν χ
      (((algebraicBruhatDeriv F γ hγ)^[n]) f) q t).deriv

/-- The homogeneous theta average is smooth along every idelic
one-parameter subgroup in its logarithmic coordinate. -/
theorem adelicHomogeneousTheta_log_smooth
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (γ : Multiplicative ℝ →* Idele F) (hγ : Continuous γ)
    (f : bruhatSubmodule F) (q : IdeleClass F) :
    ContDiff ℝ ∞ (fun t : ℝ => adelicHomogeneousTheta F ν χ f.val
      (ideleClassMap F (γ (Multiplicative.ofAdd t)) * q)) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _
  rw [adelicHomogeneousTheta_log_iteratedDeriv F ν χ γ hγ f q n]
  intro t
  exact (adelicHomogeneousTheta_log_hasDerivAt F γ hγ ν χ
    (((algebraicBruhatDeriv F γ hγ)^[n]) f) q t).differentiableAt

/-- Homogeneous theta is jointly smooth in the logarithms of
any finite family of commuting idelic one-parameter subgroups. -/
theorem adelicHomogeneousTheta_product_smooth
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (n : ℕ) (γ : Fin n → Multiplicative ℝ →* Idele F)
    (hγ : ∀ i, Continuous (γ i)) (f : bruhatSubmodule F) (q : IdeleClass F) :
    ContDiff ℝ ∞ (fun x : Fin n → ℝ => adelicHomogeneousTheta F ν χ f.val
      ((∏ i, ideleClassMap F (γ i (Multiplicative.ofAdd (x i)))) * q)) := by
  let S (x : Fin n → ℝ) (i : Fin n) := ideleClassMap F (γ i (Multiplicative.ofAdd (x i)))
  let a (x : Fin n → ℝ) := (∏ i, S x i) * q
  let T (u : bruhatSubmodule F) (x : Fin n → ℝ) := adelicHomogeneousTheta F ν χ u.val (a x)
  let D (i : Fin n) := algebraicBruhatDeriv F (γ i) (hγ i)
  have ha : Continuous a :=
    (continuous_finsetProd _ fun i _ => (ideleClassMap_continuous F).comp
      ((hγ i).comp (continuous_ofAdd.comp (continuous_apply i)))).mul continuous_const
  have hT (u : bruhatSubmodule F) : Continuous (T u) :=
    (adelicHomogeneousTheta_continuous F ν χ u.property).comp ha
  have hp (u : bruhatSubmodule F) (x : Fin n → ℝ) (i : Fin n) :
      HasDerivAt (fun t : ℝ => T u (Function.update x i t)) (T (D i u) x) (x i) := by
    let r := (∏ j ∈ Finset.univ.erase i, S x j) * q
    have he (t : ℝ) : a (Function.update x i t) =
        ideleClassMap F (γ i (Multiplicative.ofAdd t)) * r := by
      unfold a r
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_assoc]
      congr 1
      · simp only [S, Function.update_self]
      · apply congrArg (fun z : IdeleClass F => z * q)
        apply Finset.prod_congr rfl
        intro j hj
        simp only [S, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hx : a x = ideleClassMap F (γ i (Multiplicative.ofAdd (x i))) * r := by
      simpa only [Function.update_eq_self] using he (x i)
    simpa only [T, D, he, hx] using adelicHomogeneousTheta_log_hasDerivAt F (γ i)
      (hγ i) ν χ u r (x i)
  have hd (u : bruhatSubmodule F) := hasFDerivAt_fin_of_continuous_partials n (T u)
    (fun i => T (D i u)) (fun i => hT (D i u)) (hp u)
  change ContDiff ℝ ∞ (T f)
  apply contDiff_infty.mpr
  have hC (m : ℕ) (u : bruhatSubmodule F) : ContDiff ℝ m (T u) := by
    induction m generalizing u with
    | zero => exact contDiff_zero.mpr (hT u)
    | succ m ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hd u x).differentiableAt, by simp, ?_⟩
      have he : fderiv ℝ (T u) = fun x =>
          ∑ i, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (T (D i u) x) :=
        funext fun x => (hd u x).fderiv
      rw [he]
      exact ContDiff.sum (fun i _ => ((ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) ℂ
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)).contDiff).comp (ih (D i u)))
  exact fun m => hC m f

private abbrev Arch := mixedEmbedding.mixedSpace F

private theorem adelicHomogeneousTheta_mixedExp_smooth
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (f : bruhatSubmodule F) (q : IdeleClass F) :
    ContDiff ℝ ∞ (fun x : Arch F => adelicHomogeneousTheta F ν χ f.val
      (ideleClassMap F (mixedArchExpIdele F (Multiplicative.ofAdd x)) * q)) := by
  let b := Module.finBasis ℝ (Arch F)
  let e := b.equivFun.toContinuousLinearEquiv
  let L (i : Fin (Module.finrank ℝ (Arch F))) : ℝ →L[ℝ] Arch F :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (b i)
  let γ (i : Fin (Module.finrank ℝ (Arch F))) : Multiplicative ℝ →* Idele F :=
    (mixedArchExpIdele F).comp (L i).toLinearMap.toAddMonoidHom.toMultiplicative
  have hγ (i : Fin (Module.finrank ℝ (Arch F))) : Continuous (γ i) :=
    (mixedArchExpIdele_continuous F).comp
      (continuous_ofAdd.comp ((L i).continuous.comp continuous_toAdd))
  have hs := (adelicHomogeneousTheta_product_smooth F ν χ _ γ hγ f q).comp e.contDiff
  have he (x : Arch F) :
      (∏ i, ideleClassMap F (γ i (Multiplicative.ofAdd (e x i)))) =
        ideleClassMap F (mixedArchExpIdele F (Multiplicative.ofAdd x)) := by
    let j := (ideleClassMap F).comp (mixedArchExpIdele F)
    change (∏ i, j (Multiplicative.ofAdd (e x i • b i))) = _
    rw [← map_prod, ← ofAdd_sum]
    exact congrArg (fun y : Arch F => j (Multiplicative.ofAdd y)) (b.sum_repr x)
  have heq : (fun x : Arch F => adelicHomogeneousTheta F ν χ f.val
      (ideleClassMap F (mixedArchExpIdele F (Multiplicative.ofAdd x)) * q)) =
      (fun x => adelicHomogeneousTheta F ν χ f.val
        ((∏ i, ideleClassMap F (γ i (Multiplicative.ofAdd (x i)))) * q)) ∘ e := by
    funext x
    exact congrArg (fun g : IdeleClass F => adelicHomogeneousTheta F ν χ f.val (g * q)) (he x).symm
  rw [heq]
  exact hs

private def mixedLog (x : Arch F) : Arch F :=
  (fun v => Real.log (x.1 v), fun v => Complex.log (x.2 v))

private theorem mixedLog_contDiffAt_one : ContDiffAt ℝ ∞ (mixedLog F) 1 := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro v
    let r (x : Arch F) := x.1 v
    have hr : ContDiffAt ℝ ∞ r 1 := (contDiff_pi.mp contDiff_fst v).contDiffAt
    exact ((Real.contDiffAt_log (x := 1)).mpr one_ne_zero).comp 1 hr
  · apply contDiffAt_pi.mpr
    intro v
    let r (x : Arch F) := x.2 v
    have hr : ContDiffAt ℝ ∞ r 1 := (contDiff_pi.mp contDiff_snd v).contDiffAt
    have hlog : ContDiffAt ℂ ∞ Complex.log 1 := Complex.contDiffAt_log Complex.one_mem_slitPlane
    exact (hlog.restrict_scalars ℝ).comp 1 hr

private theorem mixedExp_mixedLog_eventually :
    ∀ᶠ x : Arch F in 𝓝 1, mixedExp F (mixedLog F x) = x := by
  have hR : ∀ᶠ x : Arch F in 𝓝 1, ∀ v, 0 < x.1 v := by
    apply eventually_all.mpr
    intro v
    exact (isOpen_lt continuous_const ((continuous_apply v).comp continuous_fst)).mem_nhds
      (show (0 : ℝ) < 1 from zero_lt_one)
  have hC : ∀ᶠ x : Arch F in 𝓝 1, ∀ v, x.2 v ≠ 0 := by
    apply eventually_all.mpr
    intro v
    have hc : Continuous (fun x : Arch F => x.2 v) :=
      (continuous_apply v).comp continuous_snd
    have hopen : IsOpen {x : Arch F | x.2 v ≠ 0} :=
      (isOpen_ne (x := (0 : ℂ))).preimage hc
    exact hopen.mem_nhds (show (1 : ℂ) ≠ 0 from one_ne_zero)
  filter_upwards [hR, hC] with x hx hy
  apply Prod.ext
  · funext v
    exact Real.exp_log (hx v)
  · funext v
    exact Complex.exp_log (hy v)

/-- The homogeneous theta average is smooth in the actual archimedean
coordinates, with the finite component fixed. -/
theorem adelicHomogeneousTheta_arch_smooth
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (f : bruhatSubmodule F) (q : IdeleClass F) :
    ContDiffOn ℝ ∞ (fun x : Arch F => if hx : IsUnit x then
      adelicHomogeneousTheta F ν χ f.val (ideleClassMap F (mixedArchUnitIdele F hx.unit) * q)
      else 0) {x | IsUnit x} := by
  intro x hx
  let a := hx.unit
  let p (y : Arch F) := y * (a⁻¹ : (Arch F)ˣ).val
  have hp : ContDiff ℝ ∞ p := contDiff_id.mul contDiff_const
  have hpx : p x = 1 := by
    change x * a.inv = 1
    rw [← hx.unit_spec]
    exact a.val_inv
  let J := mixedArchUnitIdele F
  let q' := ideleClassMap F (J a) * q
  have hc := (adelicHomogeneousTheta_mixedExp_smooth F ν χ f q').contDiffAt
    (x := mixedLog F (p x))
  have hl : ContDiffAt ℝ ∞ (mixedLog F ∘ p) x := by
    apply ContDiffAt.comp x _ hp.contDiffAt
    rw [hpx]
    exact mixedLog_contDiffAt_one F
  apply ContDiffAt.contDiffWithinAt
  refine (hc.comp x hl).congr_of_eventuallyEq ?_
  have hv : Tendsto p (𝓝 x) (𝓝 1) := hp.continuous.tendsto' x 1 hpx
  filter_upwards [hv.eventually (mixedExp_mixedLog_eventually F)] with y hy
  let u := mixedExpUnits F (Multiplicative.ofAdd (mixedLog F (p y))) * a
  have huy : u.val = y := by
    change mixedExp F (mixedLog F (p y)) * a.val = y
    rw [hy]
    change (y * a.inv) * a.val = y
    rw [mul_assoc, a.inv_val, mul_one]
  have hu : IsUnit y := ⟨u, huy⟩
  have he : hu.unit = u := Units.ext (hu.unit_spec.trans huy.symm)
  rw [dite_eq_left hu, he]
  change adelicHomogeneousTheta F ν χ f.val (ideleClassMap F (J u) * q) =
    adelicHomogeneousTheta F ν χ f.val
      (ideleClassMap F (mixedArchExpIdele F (Multiplicative.ofAdd (mixedLog F (p y)))) * q')
  congr 1
  simp only [u, q', map_mul, mul_assoc]
  rfl

local notation "𝒟" => GlobalBruhat.derivative F (ideleExpSection F) (ideleExpSection_continuous F)

private theorem homogeneous_radial_iteratedDeriv
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (f : GlobalBruhat F) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => adelicHomogeneousTheta F ν χ
      (GlobalBruhat.algebraicEquiv F f).val (ideleClassExpSection F (Multiplicative.ofAdd t))) =
      fun t : ℝ => adelicHomogeneousTheta F ν χ
        (GlobalBruhat.algebraicEquiv F ((𝒟 ^ n) f)).val
        (ideleClassExpSection F (Multiplicative.ofAdd t)) := by
  have he (n : ℕ) : GlobalBruhat.algebraicEquiv F ((𝒟 ^ n) f) =
      ((algebraicBruhatDeriv F (ideleExpSection F) (ideleExpSection_continuous F))^[n])
        (GlobalBruhat.algebraicEquiv F f) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Function.iterate_succ_apply']
      have h (x : GlobalBruhat F) :
          GlobalBruhat.algebraicEquiv F (𝒟 x) =
            algebraicBruhatDeriv F (ideleExpSection F) (ideleExpSection_continuous F)
              (GlobalBruhat.algebraicEquiv F x) :=
        (GlobalBruhat.algebraicEquiv F).apply_symm_apply _
      change GlobalBruhat.algebraicEquiv F (𝒟 ((𝒟 ^ n) f)) = _
      rw [h, ih]
  have h := adelicHomogeneousTheta_log_iteratedDeriv F ν χ
    (ideleExpSection F) (ideleExpSection_continuous F) (GlobalBruhat.algebraicEquiv F f) 1 n
  have harg (t : ℝ) : ideleClassMap F (ideleExpSection F (Multiplicative.ofAdd t)) * 1 =
      ideleClassExpSection F (Multiplicative.ofAdd t) := by
    change ideleClassMap F (ideleExpSection F (Multiplicative.ofAdd t)) * 1 =
      ideleClassMap F (ideleExpSection F (Multiplicative.ofAdd t))
    exact mul_one (ideleClassMap F (ideleExpSection F (Multiplicative.ofAdd t)))
  simp_rw [harg] at h
  simpa only [he] using h

private theorem radial_derivative_zero_terms (f : GlobalBruhat F) :
    (GlobalBruhat.algebraicEquiv F (𝒟 f)).val 0 = 0 ∧
    (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F (𝒟 f))).val 0 =
      -(GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 := by
  have he : GlobalBruhat.algebraicEquiv F (𝒟 f) =
      algebraicBruhatDeriv F (ideleExpSection F) (ideleExpSection_continuous F)
        (GlobalBruhat.algebraicEquiv F f) :=
    (GlobalBruhat.algebraicEquiv F).apply_symm_apply _
  rw [GlobalBruhat.fourier_apply, GlobalBruhat.fourier_apply, he]
  simpa only [neg_smul, one_smul] using algebraicBruhatDeriv_zero_terms F (ideleExpSection F)
    (ideleExpSection_continuous F) 1
    (fun t => by rw [mul_one]; exact ideleNorm_expSection F (Multiplicative.ofAdd t))
    (GlobalBruhat.algebraicEquiv F f)

private theorem radial_derivative_powers_zero_terms (f : GlobalBruhat F)
    (hf : (GlobalBruhat.algebraicEquiv F f).val 0 = 0)
    (hFourier : (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0) (n : ℕ) :
    (GlobalBruhat.algebraicEquiv F ((𝒟 ^ n) f)).val 0 = 0 ∧
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F ((𝒟 ^ n) f))).val 0 = 0 := by
  induction n with
  | zero => simpa using And.intro hf hFourier
  | succ n ih =>
    rw [pow_succ']
    have h := radial_derivative_zero_terms F ((𝒟 ^ n) f)
    refine ⟨h.1, ?_⟩
    change (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F
      (𝒟 ((𝒟 ^ n) f)))).val 0 = 0
    rw [h.2, ih.2, neg_zero]

/-- All radial derivatives decay exponentially at both ends, uniformly on
bounded sets of tests subject to the stated vanishing condition. -/
theorem adelicHomogeneousTheta_radial_derivative_decay
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B) (n N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B,
      (χ ≠ 1 ∨ ((GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
        (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0)) →
      ∀ t : ℝ, ‖iteratedDeriv n (fun r : ℝ => adelicHomogeneousTheta F ν χ
        (GlobalBruhat.algebraicEquiv F f).val (ideleClassExpSection F (Multiplicative.ofAdd r))) t‖
        ≤ C * Real.exp (-(N : ℝ) * |t|) := by
  let T := 𝒟 ^ n
  obtain ⟨C, hC, h⟩ := adelicHomogeneousTheta_decay_bounded F ν (T '' B) (hB.image T) N
  refine ⟨C, hC, fun f hf hvan t => ?_⟩
  rw [homogeneous_radial_iteratedDeriv F ν χ f n]
  let q := ideleClassExpSection F (Multiplicative.ofAdd t)
  have hqt : ideleClassNorm F q = Real.exp t := ideleClassNorm_expSection F _
  have hest := (h (T f) (mem_image_of_mem T hf) χ).2 q
  by_cases ht : 0 ≤ t
  · have hlarge : 1 ≤ ideleClassNorm F q := by rw [hqt]; exact Real.one_le_exp_iff.mpr ht
    have hb := hest.1 hlarge
    rw [hqt, ← Real.exp_nat_mul, ← Real.exp_neg] at hb
    simpa only [abs_of_nonneg ht, neg_mul] using hb
  · have ht' := le_of_not_ge ht
    have hsmall : ideleClassNorm F q ≤ 1 := by rw [hqt]; exact Real.exp_le_one_iff.mpr ht'
    have hz :
        (if χ = 1 then ν.real univ •
          ((ideleClassNorm F q)⁻¹ • (GlobalBruhat.algebraicEquiv F
            (GlobalBruhat.fourier F (T f))).val 0 -
            (GlobalBruhat.algebraicEquiv F (T f)).val 0) else 0) = 0 := by
      rcases hvan with hχ | ⟨hzero, hFourier⟩
      · exact ite_eq_right hχ
      · have hD := radial_derivative_powers_zero_terms F f hzero hFourier n
        change (GlobalBruhat.algebraicEquiv F (T f)).val 0 = 0 ∧
          (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F (T f))).val 0 = 0 at hD
        simp [hD.1, hD.2]
    have hb := hest.2 hsmall
    rw [hz, sub_zero, hqt, ← Real.exp_nat_mul] at hb
    simpa only [abs_of_nonpos ht', neg_mul_neg] using hb

/-- The logarithmic profile in the vanishing cases of Theorem 2.2.5.4
belongs to the Schwartz space. Every derivative has the exponential
bounds of `adelicHomogeneousTheta_radial_derivative_decay`. -/
def adelicHomogeneousTheta_radialSchwartz
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (f : GlobalBruhat F)
    (hvan : χ ≠ 1 ∨ ((GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0)) : 𝓢(ℝ, ℂ) where
  toFun t := adelicHomogeneousTheta F ν χ (GlobalBruhat.algebraicEquiv F f).val
    (ideleClassExpSection F (Multiplicative.ofAdd t))
  smooth' := by
    have h := adelicHomogeneousTheta_log_smooth F ν χ (ideleExpSection F)
      (ideleExpSection_continuous F) (GlobalBruhat.algebraicEquiv F f) 1
    have harg (t : ℝ) : ideleClassMap F (ideleExpSection F (Multiplicative.ofAdd t)) * 1 =
        ideleClassExpSection F (Multiplicative.ofAdd t) := by
      change ideleClassMap F (ideleExpSection F (Multiplicative.ofAdd t)) * 1 =
        ideleClassMap F (ideleExpSection F (Multiplicative.ofAdd t))
      exact mul_one (ideleClassMap F (ideleExpSection F (Multiplicative.ofAdd t)))
    simpa only [harg] using h
  decay' k n := by
    obtain ⟨C, hC, hdecay⟩ := adelicHomogeneousTheta_radial_derivative_decay F ν χ {f}
      (isVonNBounded_singleton (𝕜 := ℂ) f) n 1
    refine ⟨(k.factorial : ℝ) * C, fun t => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    have ht := hdecay f (mem_singleton _) hvan t
    simp only [Nat.cast_one, neg_mul, one_mul] at ht
    have hk : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hpoly := (div_le_iff₀ hk).mp (Real.pow_div_factorial_le_exp _ (abs_nonneg t) k)
    calc
      _ ≤ |t| ^ k * (C * Real.exp (-|t|)) :=
        mul_le_mul_of_nonneg_left ht (pow_nonneg (abs_nonneg _) _)
      _ ≤ (Real.exp |t| * (k.factorial : ℝ)) * (C * Real.exp (-|t|)) :=
        mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = (k.factorial : ℝ) * C := by
        rw [show (Real.exp |t| * (k.factorial : ℝ)) * (C * Real.exp (-|t|)) =
          (k.factorial : ℝ) * C * (Real.exp |t| * Real.exp (-|t|)) by ring]
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]


/-- Multiplication by the compact character turns the homogeneous theta
function into the radial Schwartz profile in the vanishing cases. -/
theorem adelicHomogeneousTheta_twisted_radialSchwartz
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (f : GlobalBruhat F)
    (hvan : χ ≠ 1 ∨ ((GlobalBruhat.algebraicEquiv F f).val 0 = 0 ∧
      (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val 0 = 0))
    (q : IdeleClass F) :
    (χ (ideleClassNormOnePart F q) : ℂ) *
      adelicHomogeneousTheta F ν χ (GlobalBruhat.algebraicEquiv F f).val q =
        adelicHomogeneousTheta_radialSchwartz F ν χ f hvan (Real.log (ideleClassNorm F q)) := by
  let k := ideleClassNormOnePart F q
  let r := ideleClassExpSection F (ideleClassLogNorm F q)
  have hq : k.val * r = q := (ideleClassSplit F).symm_apply_apply q
  have h := adelicHomogeneousTheta_translate F ν χ (GlobalBruhat.algebraicEquiv F f).val k r
  rw [hq] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]
  rfl

/-- The two-sided homogeneous estimate of Theorem 2.2.5.4, uniform
on a bounded family in the final Schwartz-slice topology. -/
theorem adelicHomogeneousTheta_twoSided_bounded
    (ν : Measure (K F)) [ν.IsHaarMeasure] (χ : PontryaginDual (K F))
    (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ q : IdeleClass F,
      let u := (GlobalBruhat.algebraicEquiv F f).val
      let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
      let m := ideleClassNorm F q
      (1 ≤ m → ‖adelicHomogeneousTheta F ν χ u q‖ ≤ C * (m ^ N)⁻¹) ∧
      (m ≤ 1 → ‖adelicHomogeneousTheta F ν χ u q -
        (if χ = 1 then ν.real univ • (m⁻¹ • v 0 - u 0) else 0)‖ ≤ C * m ^ N) ∧
      ((χ ≠ 1 ∨ (u 0 = 0 ∧ v 0 = 0)) →
        ‖adelicHomogeneousTheta F ν χ u q‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log m|)) := by
  obtain ⟨C, hC, h⟩ := adelicHomogeneousTheta_decay_bounded F ν B hB N
  refine ⟨C, hC, fun f hf q => ?_⟩
  let m := ideleClassNorm F q
  have hpos : 0 < m := ideleClassNorm_pos F q
  have hest := (h f hf χ).2 q
  refine ⟨hest.1, hest.2, fun hv => ?_⟩
  rcases le_total 1 m with hlarge | hsmall
  · have he : Real.exp (-(N : ℝ) * |Real.log m|) = (m ^ N)⁻¹ := by
      rw [abs_of_nonneg (Real.log_nonneg hlarge), neg_mul, Real.exp_neg, Real.exp_nat_mul,
        Real.exp_log hpos]
    change _ ≤ C * Real.exp (-(N : ℝ) * |Real.log m|)
    rw [he]
    exact hest.1 hlarge
  · have he : Real.exp (-(N : ℝ) * |Real.log m|) = m ^ N := by
      rw [abs_of_nonpos (Real.log_nonpos hpos.le hsmall), neg_mul_neg, Real.exp_nat_mul,
        Real.exp_log hpos]
    change _ ≤ C * Real.exp (-(N : ℝ) * |Real.log m|)
    rw [he]
    have hb := hest.2 hsmall
    rcases hv with hχ | ⟨hu, hw⟩
    · simpa only [hχ, ite_false, sub_zero] using hb
    · simpa only [hu, hw, smul_zero, sub_zero, ite_self] using hb

end

end Masullo
