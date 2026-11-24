import SLocalArchLaurentInterpolation

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull a Schwartz test back along multiplication by a nonzero real scalar. -/
def schwartzScalarPullback (a : ℝ) (ha : a ≠ 0) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.smulLeft (Units.mk0 a ha))

@[simp] theorem schwartzScalarPullback_apply (a : ℝ) (ha : a ≠ 0) (f : 𝓢(E, ℂ)) (x : E) :
    schwartzScalarPullback a ha f x = f (a • x) := rfl

/-- On shrinking supports, the polynomial weight in a Schwartz seminorm
does not grow. Each derivative costs one power of the inverse dilation. -/
theorem schwartzScalarPullback_seminorm_le (a : ℝ) (ha : 1 ≤ a) (f : 𝓢(E, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (schwartzScalarPullback a (zero_lt_one.trans_le ha).ne' f) ≤
      a ^ n * SchwartzMap.seminorm ℂ k n f := by
  have hpos : 0 < a := zero_lt_one.trans_le ha
  let A : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  have hA (x : E) : A x = a • x := rfl
  have hAn : ‖A‖ ≤ a :=
    ContinuousLinearMap.opNorm_le_bound _ hpos.le (fun x ↦ by rw [hA, norm_smul, Real.norm_of_nonneg hpos.le])
  have hfun : ⇑(schwartzScalarPullback a hpos.ne' f) = (⇑f) ∘ A := rfl
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
  intro x
  rw [hfun, A.iteratedFDeriv_comp_right (f.smooth ⊤) x (i := n)
    (WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤))]
  have hder : ‖(iteratedFDeriv ℝ n f (A x)).compContinuousLinearMap (fun _ ↦ A)‖ ≤
      ‖iteratedFDeriv ℝ n f (A x)‖ * a ^ n := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  have hnorm : ‖x‖ ≤ ‖A x‖ := by
    rw [hA, norm_smul, Real.norm_of_nonneg hpos.le]
    exact le_mul_of_one_le_left (norm_nonneg _) ha
  calc
    _ ≤ ‖A x‖ ^ k * (‖iteratedFDeriv ℝ n f (A x)‖ * a ^ n) := by gcongr
    _ = a ^ n * (‖A x‖ ^ k * ‖iteratedFDeriv ℝ n f (A x)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ k n f (A x)) (by positivity)

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev FiniteTests := locallyConstantTests (∀ v : S, v.val.adicCompletion F)

/-- The inverse logarithmic norm dilation acts on the mixed coordinates
by a common scalar and fixes the finite coordinates. -/
theorem sLocalExpSection_inv_mul_components (t : ℝ) (x : SAdeles F S) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F
        (((sLocalExpSection F S (Multiplicative.ofAdd t)).inv * x).1) =
      Real.exp (-t / Module.finrank ℚ F) • InfiniteAdeleRing.ringEquiv_mixedSpace F x.1 ∧
    ((sLocalExpSection F S (Multiplicative.ofAdd t)).inv * x).2 = x.2 := by
  let u := Multiplicative.ofAdd t
  have hu : u⁻¹ = Multiplicative.ofAdd (-t) := rfl
  have hi : (sLocalExpSection F S u).inv = (sLocalExpSection F S (Multiplicative.ofAdd (-t))).val := by
    rw [← hu, map_inv]
    rfl
  rw [hi]
  constructor
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((ideleExpSection F (Multiplicative.ofAdd (-t))).val.1 * x.1) = _
    rw [map_mul, ideleExpSection_mixed, smul_mul_assoc, one_mul]
    rfl
  · have h (v : S) : (sLocalExpSection F S (Multiplicative.ofAdd (-t))).val.2 v = 1 := by
      change (ideleExpSection F (Multiplicative.ofAdd (-t))).val.2 v = 1
      rw [(ideleExpSection_components F (Multiplicative.ofAdd (-t))).2]
      rfl
    funext v
    change (sLocalExpSection F S (Multiplicative.ofAdd (-t))).val.2 v * x.2 v = x.2 v
    rw [h, one_mul]

/-- Positive norm translation of a pure S-local test changes only
its archimedean Schwartz function. -/
theorem sLocalBruhatLeftTranslate_expSection_pure (t : ℝ) (f : Arch F) (g : FiniteTests F S) :
    sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t))
        (sLocalBruhatPure F S f g) =
      sLocalBruhatPure F S (schwartzScalarPullback (Real.exp (-t / Module.finrank ℚ F))
        (Real.exp_pos _).ne' f) g := by
  let lhs := sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t))
    (sLocalBruhatPure F S f g)
  let rhs := sLocalBruhatPure F S (schwartzScalarPullback (Real.exp (-t / Module.finrank ℚ F))
    (Real.exp_pos _).ne' f) g
  change lhs = rhs
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext z
  change GlobalBruhat.evaluation F z lhs.val = GlobalBruhat.evaluation F z rhs.val
  rw [sLocalBruhatRestriction_reconstruct F S lhs, sLocalBruhatRestriction_reconstruct F S rhs]
  dsimp only [lhs, rhs]
  rw [
    sLocalBruhatLeftTranslate_restrict, sLocalBruhatPure_restrict, sLocalBruhatPure_restrict,
    schwartzScalarPullback_apply]
  rw [(sLocalExpSection_inv_mul_components F S t (sAdelesProjection F S z)).1,
    (sLocalExpSection_inv_mul_components F S t (sAdelesProjection F S z)).2]

/-- Every right closed half-plane contains only finitely many distinct
archimedean pole centers of a fixed component. -/
theorem sLocalArchPoleCenters_finite_of_re_ge
    (ω : PontryaginDual (SLocalThetaNormOne F S)) (b : ℝ) :
    {c : ℂ | 0 < sLocalArchPoleCount F S ω c ∧ b ≤ c.re}.Finite := by
  let N (_ : InfinitePlace F) := ⌈-b⌉₊
  refine (sLocalArchPoleCutoff F S ω N).finite_toSet.subset ?_
  rintro c ⟨hc, hb⟩
  obtain ⟨n, hn⟩ := (sLocalArchPoleCount_pos_iff_exists_cutoff F S ω c).mp hc
  apply (mem_sLocalArchPoleCutoff F S ω N c).mpr
  rcases (mem_sLocalArchPoleCutoff F S ω _ c).mp hn with
    ⟨v, m, _, he⟩ | ⟨v, m, _, he⟩
  · refine Or.inl ⟨v, m, ?_, he⟩
    change c = -(sLocalRealArchParameters F S ω v).1 -
      (((sLocalRealArchParameters F S ω v).2 % 2 : ℕ) : ℂ) - 2 * (m : ℂ) at he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.neg_re, sLocalRealArchParameters_re, neg_zero,
      Complex.natCast_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
    have hmb : (m : ℝ) ≤ -b := by
      linarith [Nat.cast_nonneg (α := ℝ) m,
        Nat.cast_nonneg (α := ℝ) ((sLocalRealArchParameters F S ω v).2 % 2)]
    exact_mod_cast hmb.trans (Nat.le_ceil (-b))
  · refine Or.inr ⟨v, m, ?_, he⟩
    change c = -(sLocalComplexArchParameters F S ω v).1 -
      ((sLocalComplexArchParameters F S ω v).2.natAbs : ℂ) / 2 - (m : ℂ) at he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.neg_re, sLocalComplexArchParameters_re, neg_zero,
      Complex.natCast_re, Complex.div_ofNat_re] at hre
    have hmb : (m : ℝ) ≤ -b := by
      linarith [Nat.cast_nonneg (α := ℝ) (sLocalComplexArchParameters F S ω v).2.natAbs]
    exact_mod_cast hmb.trans (Nat.le_ceil (-b))

abbrev SLocalArchPoleCenter (ω : PontryaginDual (SLocalThetaNormOne F S)) :=
  {c : ℂ // 0 < sLocalArchPoleCount F S ω c}

/-- The distinct centers form a countably infinite set. -/
theorem sLocalArchPoleCenter_enumerable (ω : PontryaginDual (SLocalThetaNormOne F S)) :
    Nonempty (ℕ ≃ SLocalArchPoleCenter F S ω) := by
  obtain ⟨e⟩ := sLocalArchPoleIndex_enumerable F S ω
  letI : Countable (SLocalArchPoleIndex F S ω) := e.symm.injective.countable
  letI : Infinite (SLocalArchPoleIndex F S ω) := Infinite.of_injective e e.injective
  let j (c : SLocalArchPoleCenter F S ω) : SLocalArchPoleIndex F S ω :=
    ⟨(c.val, 1), zero_lt_one, c.property⟩
  letI : Countable (SLocalArchPoleCenter F S ω) :=
    Function.Injective.countable (f := j) (fun _ _ h ↦ Subtype.ext (congrArg (fun i ↦ i.val.1) h))
  have hInf : Infinite (SLocalArchPoleCenter F S ω) := by
    apply not_finite_iff_infinite.mp
    intro hfin
    letI := hfin
    let B := Fintype.card (InfinitePlace F) + S.card
    let q (i : SLocalArchPoleIndex F S ω) : SLocalArchPoleCenter F S ω × Fin (B+1) :=
      (⟨i.val.1, i.property.1.trans_le i.property.2⟩,
        ⟨i.val.2, Nat.lt_succ_of_le
          (i.property.2.trans ((Nat.le_add_right _ _ : sLocalArchPoleCount F S ω i.val.1 ≤
            sLocalPoleCount F S ω i.val.1).trans (sLocalPoleCount_le_places F S ω i.val.1)))⟩)
    letI : Finite (SLocalArchPoleIndex F S ω) := Finite.of_injective q
      (fun _ _ h ↦ Subtype.ext (Prod.ext (congrArg (fun x ↦ x.1.val) h) (congrArg (fun x ↦ x.2.val) h)))
    exact not_finite (SLocalArchPoleIndex F S ω)
  letI := hInf
  obtain ⟨hD⟩ := nonempty_denumerable (SLocalArchPoleCenter F S ω)
  letI := hD
  exact ⟨(Denumerable.eqv _).symm⟩

/-- In every enumeration of the distinct pole centers the real parts
tend to negative infinity. -/
theorem sLocalArchPoleCenter_re_tendsto_atBot (ω : PontryaginDual (SLocalThetaNormOne F S))
    (e : ℕ ≃ SLocalArchPoleCenter F S ω) :
    Tendsto (fun n ↦ (e n).val.re) atTop atBot := by
  rw [tendsto_atBot]
  intro b
  have hinj : Function.Injective (fun n ↦ (e n).val) := Subtype.val_injective.comp e.injective
  have hfinite := (sLocalArchPoleCenters_finite_of_re_ge F S ω b).preimage hinj.injOn
  have h := hfinite.eventually_cofinite_notMem
  rw [Nat.cofinite_eq_atTop] at h
  filter_upwards [h] with n hn
  exact le_of_lt (lt_of_not_ge (fun he ↦ hn ⟨(e n).property, he⟩))

/-- Shrink the archimedean support while compensating the Mellin
translation factor at the chosen spectral center. -/
def sLocalArchNormalizedDilation (c : ℂ) (t : ℝ) (f : Arch F) : Arch F :=
  Complex.exp (c * (t : ℂ)) •
    schwartzScalarPullback (Real.exp (t / Module.finrank ℚ F)) (Real.exp_pos _).ne' f

theorem sLocalArchNormalizedDilation_seminorm_le
    (c : ℂ) (t : ℝ) (ht : 0 ≤ t) (f : Arch F) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (sLocalArchNormalizedDilation F c t f) ≤
      Real.exp ((c.re + (n : ℝ) / Module.finrank ℚ F) * t) *
        SchwartzMap.seminorm ℂ k n f := by
  let d : ℝ := Module.finrank ℚ F
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have ha : 1 ≤ Real.exp (t / d) := Real.one_le_exp_iff.mpr (div_nonneg ht hd)
  unfold sLocalArchNormalizedDilation
  rw [map_smul_eq_mul, Complex.norm_exp]
  calc
    _ ≤ Real.exp (c * (t : ℂ)).re *
        (Real.exp (t / d) ^ n * SchwartzMap.seminorm ℂ k n f) :=
      mul_le_mul_of_nonneg_left (schwartzScalarPullback_seminorm_le _ ha f k n) (by positivity)
    _ = _ := by
      rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero,
        ← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      change c.re * t + (n : ℝ) * (t / d) = (c.re + (n : ℝ) / d) * t
      ring

/-- A sufficiently far left center permits arbitrarily small
normalized corrections in any fixed Schwartz seminorm. -/
theorem sLocalArchNormalizedDilation_seminorm_tendsto
    (c : ℂ) (f : Arch F) (k n : ℕ) (hc : c.re + (n : ℝ) / Module.finrank ℚ F < 0) :
    Tendsto (fun t : ℝ ↦ SchwartzMap.seminorm ℂ k n (sLocalArchNormalizedDilation F c t f))
      atTop (𝓝 0) := by
  let b := c.re + (n : ℝ) / Module.finrank ℚ F
  have hb : Tendsto (fun t : ℝ ↦ b * t) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg hc).2 tendsto_id
  have h := (Real.tendsto_exp_atBot.comp hb).mul_const (SchwartzMap.seminorm ℂ k n f)
  refine squeeze_zero' (g := fun t ↦ Real.exp (b * t) * SchwartzMap.seminorm ℂ k n f)
    (.of_forall fun _ ↦ apply_nonneg _ _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact sLocalArchNormalizedDilation_seminorm_le F c t ht f k n
  · simpa only [zero_mul, Function.comp_apply] using h

private abbrev L (v : S) := v.val.adicCompletion F
private abbrev K := SLocalThetaNormOne F S

attribute [local instance] sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
variable (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

private abbrev Z (ω : PontryaginDual (K F S)) (f : Arch F) (g : FiniteTests F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) (sLocalBruhatPure F S f g)

/-- The normalized dilation preserves the finite slice and multiplies the
Mellin germ by an entire exponential with value one at the chosen center. -/
theorem sLocalArchNormalizedDilation_germ (ω : PontryaginDual (K F S))
    (c : ℂ) (t : ℝ) (f : Arch F) (g : FiniteTests F S) (w : ℂ) :
    Z F S μ ω (sLocalArchNormalizedDilation F c t f) g =ᶠ[𝓝[≠] w]
      fun z ↦ Complex.exp ((c - z) * (t : ℂ)) * Z F S μ ω f g z := by
  let a := Real.exp (t / Module.finrank ℚ F)
  let u := sLocalExpSection F S (Multiplicative.ofAdd (-t))
  let h := schwartzScalarPullback a (Real.exp_pos _).ne' f
  have hp : sLocalBruhatLeftTranslate F S u (sLocalBruhatPure F S f g) =
      sLocalBruhatPure F S h g := by
    simpa only [u, h, a, neg_neg] using sLocalBruhatLeftTranslate_expSection_pure F S (-t) f g
  have he := sLocalProductZetaContinued_expSection F S μ ω (sLocalBruhatPure F S f g) (-t) w
  change (fun z ↦ sLocalContinuedMellinEval F S μ ω z
    (sLocalBruhatLeftTranslate F S u (sLocalBruhatPure F S f g))) =ᶠ[𝓝[≠] w] _ at he
  rw [hp] at he
  filter_upwards [he] with z hz
  change sLocalContinuedMellinEval F S μ ω z
    (sLocalBruhatPure F S (Complex.exp (c * (t : ℂ)) • h) g) = _
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, hz]
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  congr 2
  ring

/-- Normalizing at one center leaves the pole orders at every center
unchanged. In particular, a correction introduces no poles at centers
where the original test was regular. -/
theorem sLocalArchNormalizedDilation_order (ω : PontryaginDual (K F S))
    (c : ℂ) (t : ℝ) (f : Arch F) (g : FiniteTests F S) (w : ℂ) :
    meromorphicOrderAt (Z F S μ ω (sLocalArchNormalizedDilation F c t f) g) w =
      meromorphicOrderAt (Z F S μ ω f g) w := by
  rw [meromorphicOrderAt_congr (sLocalArchNormalizedDilation_germ F S μ ω c t f g w)]
  let H (z : ℂ) := Complex.exp ((c-z) * (t : ℂ))
  have hH : AnalyticAt ℂ H w := ((analyticAt_const.sub analyticAt_id).mul analyticAt_const).cexp
  have hZ : MeromorphicAt (Z F S μ ω f g) w :=
    sLocalProductZetaContinued_meromorphic F S μ ω _ _ _ w
  change meromorphicOrderAt (H * Z F S μ ω f g) w = _
  rw [meromorphicOrderAt_mul hH.meromorphicAt hZ, hH.meromorphicOrderAt_eq,
    hH.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _), ENat.map_zero]
  exact zero_add _

/-- The leading coefficient of a test of pole order at most `k` is
unchanged by the normalized dilation at that center. -/
theorem sLocalArchNormalizedDilation_laurentCoeff (ω : PontryaginDual (K F S))
    (c : ℂ) (t : ℝ) (f : Arch F) (g : FiniteTests F S) (k : ℕ)
    (hk : k ≤ sLocalAllowedPoleOrder F S ω c)
    (ho : (↑(-(k : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f g) c) :
    sLocalLaurentCoeff F S μ ω c k
        (sLocalBruhatPure F S (sLocalArchNormalizedDilation F c t f) g) =
      sLocalLaurentCoeff F S μ ω c k (sLocalBruhatPure F S f g) := by
  let a := Real.exp (t / Module.finrank ℚ F)
  let u := sLocalExpSection F S (Multiplicative.ofAdd (-t))
  let h := schwartzScalarPullback a (Real.exp_pos _).ne' f
  let B := sLocalLaurentCoeff F S μ ω c k
  let N := sLocalAllowedPoleOrder F S ω c
  let x := sLocalBruhatPure F S f g
  have hp : sLocalBruhatLeftTranslate F S u x = sLocalBruhatPure F S h g := by
    simpa only [u, x, h, a, neg_neg] using sLocalBruhatLeftTranslate_expSection_pure F S (-t) f g
  have hq (j : ℕ) (hj : j ≠ 0) : sLocalLaurentCoeff F S μ ω c (k+j) x = 0 :=
    (sLocalLaurentCoeff_vanish_iff F S μ ω c k x).mpr ho _ (by omega)
  have ht := sLocalLaurentCoeff_translate F S μ ω c k hk u x
  change B (sLocalBruhatLeftTranslate F S u x) = sLocalZetaWeight F S ω c (QuotientGroup.mk u) *
    ∑ j ∈ Finset.range (N-k+1),
      (((sLocalZetaSplit F S).symm (QuotientGroup.mk u)).1 : ℂ)^j / (j.factorial : ℂ) *
        sLocalLaurentCoeff F S μ ω c (k+j) x at ht
  rw [show (sLocalZetaSplit F S).symm (QuotientGroup.mk u) = (-t, (1 : K F S))
      from sLocalZetaSplit_expSection F S (-t),
      show sLocalZetaWeight F S ω c (QuotientGroup.mk u) = Complex.exp (c * ((-t : ℝ) : ℂ))
      from sLocalZetaWeight_expSection F S ω (-t) c,
      Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.zero_lt_succ _))] at ht
  swap
  · intro j _ hj
    rw [hq j hj, mul_zero]
  have he : B (sLocalBruhatPure F S h g) = Complex.exp (-(c * (t : ℂ))) * B x := by
    rw [hp] at ht
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, add_zero, one_mul,
      Complex.ofReal_neg, mul_neg] using ht
  change B (sLocalBruhatPure F S (Complex.exp (c * (t : ℂ)) • h) g) = B x
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, he, ← mul_assoc, ← Complex.exp_add]
  simp

/-- On the same finite test slice, the leading coefficient can be kept
fixed while making any finite family of allowed seminorms arbitrarily small. -/
theorem exists_sLocalArchSmallLeadingCorrection (ω : PontryaginDual (K F S))
    (c : ℂ) (f : Arch F) (g : FiniteTests F S) (k : ℕ)
    (hk : k ≤ sLocalAllowedPoleOrder F S ω c)
    (ho : (↑(-(k : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f g) c)
    (Q : Finset (ℕ × ℕ)) (hQ : ∀ i ∈ Q, c.re + (i.2 : ℝ) / Module.finrank ℚ F < 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ h : Arch F, (∀ i ∈ Q, SchwartzMap.seminorm ℂ i.1 i.2 h < ε) ∧
      sLocalLaurentCoeff F S μ ω c k (sLocalBruhatPure F S h g) =
        sLocalLaurentCoeff F S μ ω c k (sLocalBruhatPure F S f g) ∧
      ∀ w : ℂ, meromorphicOrderAt (Z F S μ ω h g) w = meromorphicOrderAt (Z F S μ ω f g) w := by
  have hsmall : ∀ᶠ t : ℝ in atTop, ∀ i ∈ Q,
      SchwartzMap.seminorm ℂ i.1 i.2 (sLocalArchNormalizedDilation F c t f) < ε := by
    rw [eventually_all_finset]
    exact fun i hi ↦ (sLocalArchNormalizedDilation_seminorm_tendsto F c f i.1 i.2 (hQ i hi)).eventually
      (gt_mem_nhds hε)
  obtain ⟨t, ht⟩ := hsmall.exists
  exact ⟨sLocalArchNormalizedDilation F c t f, ht,
    sLocalArchNormalizedDilation_laurentCoeff F S μ ω c t f g k hk ho,
    sLocalArchNormalizedDilation_order F S μ ω c t f g⟩

/-- A single choice of finite factors works for every finite prescription
of archimedean pole orders. Only the Schwartz factor needs to change. -/
theorem exists_sLocalArchFixedFinitePoleOrderSlice (ω : PontryaginDual (K F S)) :
    ∃ g : ∀ v : S, locallyConstantTests (L F S v),
      (∀ v, (g v).val 0 = 0) ∧
      ∀ (T : Finset ℂ) (k : ℂ → ℕ), (∀ w ∈ T, k w ≤ sLocalArchPoleCount F S ω w) →
        ∃ f : Arch F, ∀ w ∈ T,
          meromorphicOrderAt (Z F S μ ω f (locallyConstantTestPiProduct g)) w = -(k w : WithTop ℤ) := by
  obtain ⟨f, g, h0, hf⟩ := exists_sLocalArchFullPoleOrderPureTest F S μ ω
  refine ⟨g, h0, fun T k hk ↦ ?_⟩
  let ψ := locallyConstantTestPiProduct g
  let P : Arch F →ₗ[ℂ] sLocalBruhatImage F S := (sLocalBruhatPure F S).flip ψ
  have hExp (x : sLocalBruhatImage F S) (hx : x ∈ P.range) (t : ℝ) :
      ∃ y ∈ P.range, ∀ c : ℂ,
        sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
          (sLocalComplexArchParameters F S ω) y =ᶠ[𝓝[≠] c] fun z ↦
          Complex.exp (z * (t : ℂ)) * sLocalProductZetaContinued F S μ ω
            (sLocalRealArchParameters F S ω) (sLocalComplexArchParameters F S ω) x z := by
    obtain ⟨q, rfl⟩ := hx
    let a := Real.exp (-t / Module.finrank ℚ F)
    let q' := schwartzScalarPullback a (Real.exp_pos _).ne' q
    refine ⟨P q', ⟨q', rfl⟩, fun c ↦ ?_⟩
    have ht : sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t)) (P q) = P q' :=
      sLocalBruhatLeftTranslate_expSection_pure F S t q ψ
    have he : (fun z ↦ sLocalContinuedMellinEval F S μ ω z
        (sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t)) (P q)))
        =ᶠ[𝓝[≠] c] fun z ↦ Complex.exp (z * (t : ℂ)) * sLocalContinuedMellinEval F S μ ω z (P q) :=
      sLocalProductZetaContinued_expSection F S μ ω (P q) t c
    rw [ht] at he
    exact he
  obtain ⟨q, ⟨p, rfl⟩, hq⟩ := exists_sLocalArchPrescribedFinitePoleOrders_of_closed_under_exp
    F S μ ω P.range hExp (P f) ⟨f, rfl⟩ hf T k hk
  exact ⟨p, hq⟩

/-- A fixed finite slice admits arbitrarily small isolated corrections
at each center sufficiently far left for the requested seminorms.
Earlier centers can be kept regular, and higher orders at the target
are kept zero. -/
theorem exists_sLocalArchFixedFiniteIsolatedCorrection (ω : PontryaginDual (K F S)) :
    ∃ g : ∀ v : S, locallyConstantTests (L F S v), (∀ v, (g v).val 0 = 0) ∧
      let ψ := locallyConstantTestPiProduct g
      ∀ (T : Finset ℂ) (c : ℂ) (k : ℕ), 0 < k → k ≤ sLocalArchPoleCount F S ω c →
        ∀ (b : ℂ) (Q : Finset (ℕ × ℕ)), (∀ i ∈ Q, c.re + (i.2 : ℝ) / Module.finrank ℚ F < 0) →
        ∀ ε : ℝ, 0 < ε → ∃ f : Arch F,
          (∀ i ∈ Q, SchwartzMap.seminorm ℂ i.1 i.2 f < ε) ∧
          sLocalLaurentCoeff F S μ ω c k (sLocalBruhatPure F S f ψ) = b ∧
          (∀ j > k, sLocalLaurentCoeff F S μ ω c j (sLocalBruhatPure F S f ψ) = 0) ∧
          ∀ w ∈ T, w ≠ c → ∀ j > 0,
            sLocalLaurentCoeff F S μ ω w j (sLocalBruhatPure F S f ψ) = 0 := by
  obtain ⟨g, h0, hg⟩ := exists_sLocalArchFixedFinitePoleOrderSlice F S μ ω
  refine ⟨g, h0, ?_⟩
  let ψ := locallyConstantTestPiProduct g
  change ∀ (T : Finset ℂ) (c : ℂ) (k : ℕ), _
  intro T c k hkp hk b Q hQ ε hε
  let n (z : ℂ) := if z = c then k else 0
  have htn (w : ℂ) (_ : w ∈ insert c T) : n w ≤ sLocalArchPoleCount F S ω w := by
    by_cases h : w = c
    · subst w
      simpa [n] using hk
    · simp [n, h]
  obtain ⟨f, hf⟩ := hg (insert c T) n htn
  let P : Arch F →ₗ[ℂ] sLocalBruhatImage F S := (sLocalBruhatPure F S).flip ψ
  have hf' (w : ℂ) (hw : w ∈ insert c T) :
      meromorphicOrderAt (Z F S μ ω f ψ) w = -(n w : WithTop ℤ) := hf w hw
  have hc : meromorphicOrderAt (Z F S μ ω f ψ) c = -(k : WithTop ℤ) := by
    simpa only [n, ite_eq_left rfl] using hf' c (Finset.mem_insert_self _ _)
  let B := sLocalLaurentCoeff F S μ ω c k
  have hB : B (P f) ≠ 0 := sLocalLaurentCoeff_ne_zero_of_exact_order F S μ ω (P f) c k hkp hc
  let F' := (b / B (P f)) • f
  have hval : B (P F') = b := by
    rw [show F' = (b / B (P f)) • f from rfl, map_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hB]
  have hav (w : ℂ) (hw : w ∈ insert c T) :
      (↑(-(n w : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω F' ψ) w := by
    apply (sLocalLaurentCoeff_vanish_iff F S μ ω w (n w) (P F')).mp
    intro j hj
    have ho : (↑(-(n w : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f ψ) w := by
      rw [hf' w hw]
      rfl
    have hz := (sLocalLaurentCoeff_vanish_iff F S μ ω w (n w) (P f)).mpr ho j hj
    rw [show F' = (b / B (P f)) • f from rfl, map_smul, map_smul, hz, smul_zero]
  have hOrder : k ≤ sLocalAllowedPoleOrder F S ω c := by
    rw [sLocalAllowedPoleOrder_eq_count, sLocalPoleCount]
    exact hk.trans (Nat.le_add_right _ _)
  have hAtC : (↑(-(k : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω F' ψ) c := by
    simpa only [n, ite_eq_left rfl] using hav c (Finset.mem_insert_self _ _)
  obtain ⟨h, hs, hcoeff, hrest⟩ :=
    exists_sLocalArchSmallLeadingCorrection F S μ ω c F' ψ k hOrder hAtC Q hQ ε hε
  refine ⟨h, hs, hcoeff.trans hval, ?_, ?_⟩
  · apply (sLocalLaurentCoeff_vanish_iff F S μ ω c k (P h)).mpr
    have he := hrest c
    change (↑(-(k : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω h ψ) c
    rwa [he]
  · intro w hw hne
    apply (sLocalLaurentCoeff_vanish_iff F S μ ω w 0 (P h)).mpr
    change (↑(-(0 : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω h ψ) w
    rw [hrest w]
    simpa only [n, ite_eq_right hne, Nat.cast_zero, neg_zero] using hav w (Finset.mem_insert_of_mem hw)

end

end Masullo
