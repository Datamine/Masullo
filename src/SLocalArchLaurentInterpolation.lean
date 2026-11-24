import SLocalArchGammaWitness
import SLocalArchPoleFiltration
import Mathlib.Algebra.Polynomial.Eval.Defs

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev L (v : S) := v.val.adicCompletion F
private abbrev K := SLocalThetaNormOne F S
private abbrev Tests := sLocalBruhatImage F S
private abbrev Full := sLocalFiniteNonzeroTestSubspace F S Finset.univ

attribute [local instance] sLocalZetaUnfolding_classMeasurable sLocalZetaUnfolding_classBorel
  sLocalZetaUnfolding_idelesMeasurable

variable [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
variable (μ : ∀ v : S, Measure (L F S v)ˣ)
  [∀ v : S, (μ v).IsHaarMeasure] [∀ v : S, SigmaFinite (μ v)]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
variable (ν : Measure (K F S)) [ν.IsHaarMeasure]

private abbrev Z (ω : PontryaginDual (K F S)) (f : Tests F S) :=
  sLocalProductZetaContinued F S μ ω (sLocalRealArchParameters F S ω)
    (sLocalComplexArchParameters F S ω) f

variable (hν : IsWeilQuotientMeasure (sUnitImage F S)
  (sLocalZetaProductMeasure F S μ (archimedeanMultiplicativeHaar F))
  Measure.count (sLocalClassHaar F S ν))

omit [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
/-- The class of the canonical positive section has logarithmic coordinate
`t` and trivial norm-one coordinate. -/
theorem sLocalZetaSplit_expSection (t : ℝ) :
    (sLocalZetaSplit F S).symm (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))) =
      (t, (1 : K F S)) := by
  apply (sLocalZetaSplit F S).injective
  rw [Homeomorph.apply_symm_apply]
  symm
  change QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t)) *
    ((1 : K F S) : SIdeleQuotient F S) = _
  rw [Subgroup.coe_one]
  exact mul_one (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t)) :
    SIdeleQuotient F S)

omit [∀ v : S, MeasurableSpace (L F S v)ˣ] [∀ v : S, BorelSpace (L F S v)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
theorem sLocalZetaWeight_expSection (ω : PontryaginDual (K F S)) (t : ℝ) (z : ℂ) :
    sLocalZetaWeight F S ω z (QuotientGroup.mk (sLocalExpSection F S (Multiplicative.ofAdd t))) =
      Complex.exp (z * (t : ℂ)) := by
  rw [sLocalZetaWeight, sLocalZetaSplit_expSection F S]
  simp

/-- Radial translation multiplies the actual continued Mellin transform
by the spectral exponential at every punctured germ. -/
theorem sLocalProductZetaContinued_expSection (ω : PontryaginDual (K F S))
    (g : Tests F S) (t : ℝ) (c : ℂ) :
    Z F S μ ω (sLocalBruhatLeftTranslate F S (sLocalExpSection F S (Multiplicative.ofAdd t)) g)
      =ᶠ[𝓝[≠] c] fun z ↦ Complex.exp (z * (t : ℂ)) * Z F S μ ω g z := by
  let u := sLocalExpSection F S (Multiplicative.ofAdd t)
  let g' := sLocalBruhatLeftTranslate F S u g
  refine boundedPoleMellinSpace_unique_germs
    (isOpen_lt (continuous_const (y := (0 : ℝ))) Complex.continuous_re) ⟨1, by simp⟩
    (sLocalProductZetaContinued_meromorphic F S μ ω _ _ g')
    (fun z ↦ ((analyticAt_id.mul analyticAt_const).cexp.meromorphicAt).mul
      (sLocalProductZetaContinued_meromorphic F S μ ω _ _ g z)) ?_ c
  intro z hz
  have hreg : z ∈ sLocalMellinRegularSet F S ω :=
    (sLocalMellinRegularSet_iff_noEulerPole F S ω z).mpr
      (le_of_not_gt (fun h ↦ sLocalEulerDenominator_ne_zero_of_pos F S ω hz
        ((sLocalEulerFactor_order_lt_zero_iff F S ω z).mp h)))
  have hm := sLocalProductZetaContinued_leftTranslate F S μ ω u g hreg
  rw [show sLocalZetaWeight F S ω z (QuotientGroup.mk u) = Complex.exp (z * (t : ℂ))
    from sLocalZetaWeight_expSection F S ω t z] at hm
  exact hm

include hν in
/-- An exponential multiplier in the spectral variable is realized inside
the same full finite principal-value test range. -/
theorem exists_sLocalArchExpMultiply (ω : PontryaginDual (K F S))
    (f : Tests F S) (hf : f ∈ Full F S) (t : ℝ) :
    ∃ f' ∈ Full F S, ∀ c : ℂ,
      Z F S μ ω f' =ᶠ[𝓝[≠] c] fun z ↦ Complex.exp (z * (t : ℂ)) * Z F S μ ω f z := by
  change f ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ at hf
  rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace] at hf
  obtain ⟨g, rfl⟩ := hf
  let u := sLocalExpSection F S (Multiplicative.ofAdd t)
  let g' := sLocalBruhatLeftTranslate F S u g
  refine ⟨sLocalWeilPrincipalValues F S Finset.univ g', ?_, fun c ↦ ?_⟩
  · change _ ∈ sLocalFiniteNonzeroTestSubspace F S Finset.univ
    rw [← sLocalWeilPrincipalValues_range_eq_nonzeroTestSubspace]
    exact ⟨g', rfl⟩
  filter_upwards [sLocalWeilPrincipalValues_continued F S μ ν hν ω Finset.univ g' c,
    sLocalWeilPrincipalValues_continued F S μ ν hν ω Finset.univ g c,
    sLocalProductZetaContinued_expSection F S μ ω g t c] with z h₁ h₂ h₃
  let m := sLocalSelectedEulerMultiplier F S ω Finset.univ z
  calc
    _ = m * Z F S μ ω g' z := h₁
    _ = Complex.exp (z * (t : ℂ)) * (m * Z F S μ ω g z) := by
      change Z F S μ ω g' z = _ at h₃
      rw [h₃, mul_left_comm]
    _ = _ := congrArg (_ * ·) h₂.symm

omit [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ] in
private theorem exists_sLocalArchPolynomialMultiply_of_closed_under_exp
    (ω : PontryaginDual (K F S)) (V : Submodule ℂ (Tests F S))
    (hExp : ∀ (f : Tests F S), f ∈ V → ∀ t : ℝ, ∃ f' ∈ V, ∀ c : ℂ,
      Z F S μ ω f' =ᶠ[𝓝[≠] c] fun z ↦ Complex.exp (z * (t : ℂ)) * Z F S μ ω f z)
    (f : Tests F S) (hf : f ∈ V) (t : ℝ) (p : Polynomial ℂ) :
    ∃ f' ∈ V, ∀ c : ℂ, Z F S μ ω f' =ᶠ[𝓝[≠] c] fun z ↦
      p.eval (Complex.exp (z * (t : ℂ))) * Z F S μ ω f z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨g, hg, hpg⟩ := hp
    obtain ⟨h, hh, hqh⟩ := hq
    refine ⟨g + h, V.add_mem hg hh, fun c ↦ ?_⟩
    filter_upwards [hpg c, hqh c] with z hpgz hqhz
    change sLocalContinuedMellinEval F S μ ω z (g + h) = _
    rw [map_add]
    change Z F S μ ω g z + Z F S μ ω h z = _
    rw [hpgz, hqhz, Polynomial.eval_add, add_mul]
  | monomial n a =>
    obtain ⟨g, hg, he⟩ := hExp f hf ((n : ℝ) * t)
    refine ⟨a • g, V.smul_mem a hg, fun c ↦ ?_⟩
    filter_upwards [he c] with z hz
    change sLocalContinuedMellinEval F S μ ω z (a • g) = _
    rw [map_smul, smul_eq_mul]
    change a * Z F S μ ω g z = _
    rw [hz, Polynomial.eval_monomial, ← mul_assoc, ← Complex.exp_nat_mul]
    push_cast
    ring_nf

include hν in
/-- A polynomial in one radial exponential multiplies the Mellin transform
of a test without leaving the full finite principal-value range. -/
theorem exists_sLocalArchPolynomialMultiply (ω : PontryaginDual (K F S))
    (f : Tests F S) (hf : f ∈ Full F S) (t : ℝ) (p : Polynomial ℂ) :
    ∃ f' ∈ Full F S, ∀ c : ℂ, Z F S μ ω f' =ᶠ[𝓝[≠] c] fun z ↦
      p.eval (Complex.exp (z * (t : ℂ))) * Z F S μ ω f z :=
  exists_sLocalArchPolynomialMultiply_of_closed_under_exp F S μ ω (Full F S)
    (exists_sLocalArchExpMultiply F S μ ν hν ω) f hf t p

private theorem exists_radialExp_injOn (T : Finset ℂ) :
    ∃ t : ℝ, 0 < t ∧ InjOn (fun z : ℂ ↦ Complex.exp (z * (t : ℂ))) T := by
  let B := 1 + ∑ z ∈ T, |z.im|
  have hB : 0 < B := by dsimp [B]; positivity
  let t := Real.pi / B
  have ht : 0 < t := div_pos Real.pi_pos hB
  have hb (z : ℂ) (hz : z ∈ T) : |(z * (t : ℂ)).im| < Real.pi := by
    have hle : |z.im| ≤ ∑ w ∈ T, |w.im| :=
      Finset.single_le_sum (fun i _ ↦ abs_nonneg i.im) hz
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add, abs_mul, abs_of_pos ht,
      show Real.pi = B * t by dsimp [t]; field_simp]
    exact mul_lt_mul_of_pos_right (by dsimp [B]; linarith) ht
  refine ⟨t, ht, fun x hx y hy he ↦ ?_⟩
  have h := Complex.exp_inj_of_neg_pi_lt_of_le_pi (abs_lt.mp (hb x hx)).1
    (abs_lt.mp (hb x hx)).2.le (abs_lt.mp (hb y hy)).1 (abs_lt.mp (hb y hy)).2.le he
  exact mul_left_injective₀ (Complex.ofReal_ne_zero.mpr ht.ne') h

/-- In a test subspace that admits radial exponential multiplication, a
full-order test produces arbitrary finite reductions of its pole orders. -/
theorem exists_sLocalArchPrescribedFinitePoleOrders_of_closed_under_exp
    (ω : PontryaginDual (K F S)) (V : Submodule ℂ (Tests F S))
    (hExp : ∀ (f : Tests F S), f ∈ V → ∀ t : ℝ, ∃ f' ∈ V, ∀ c : ℂ,
      Z F S μ ω f' =ᶠ[𝓝[≠] c] fun z ↦ Complex.exp (z * (t : ℂ)) * Z F S μ ω f z)
    (f : Tests F S) (hf : f ∈ V)
    (hfOrder : ∀ c : ℂ, meromorphicOrderAt (Z F S μ ω f) c = -(sLocalArchPoleCount F S ω c : WithTop ℤ))
    (T : Finset ℂ) (k : ℂ → ℕ) (hk : ∀ w ∈ T, k w ≤ sLocalArchPoleCount F S ω w) :
    ∃ f ∈ V, ∀ w ∈ T, meromorphicOrderAt (Z F S μ ω f) w = -(k w : WithTop ℤ) := by
  obtain ⟨t, ht, hT⟩ := exists_radialExp_injOn T
  let e (z : ℂ) := Complex.exp (z * (t : ℂ))
  let d (w : ℂ) := sLocalArchPoleCount F S ω w - k w
  let p : Polynomial ℂ := ∏ w ∈ T, (Polynomial.X - Polynomial.C (e w)) ^ d w
  obtain ⟨g, hg, he⟩ := exists_sLocalArchPolynomialMultiply_of_closed_under_exp F S μ ω V hExp f hf t p
  refine ⟨g, hg, fun w hw ↦ ?_⟩
  let A (u z : ℂ) := e z - e u
  have hA (u : ℂ) : AnalyticAt ℂ (A u) w :=
    ((analyticAt_id.mul analyticAt_const).cexp).sub analyticAt_const
  have hAo : analyticOrderAt (A w) w = 1 := by
    have hd : HasDerivAt (A w) (e w * (t : ℂ)) w := by
      simpa [A, e] using (((hasDerivAt_id w).mul_const (t : ℂ)).cexp).sub_const (e w)
    exact (hA w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (sub_self _)
      (by rw [hd.deriv]; exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr ht.ne'))
  have hNear (u : ℂ) (hu : u ∈ T) (hne : u ≠ w) : A u w ≠ 0 :=
    fun hz ↦ hne (hT hu hw (sub_eq_zero.mp hz).symm)
  have hProd : meromorphicOrderAt (fun z ↦ ∏ u ∈ T, A u z ^ d u) w = (d w : WithTop ℤ) := by
    have ho := meromorphicOrderAt_fun_prod (s := T) (f := fun u z ↦ A u z ^ d u)
      (fun u _ ↦ (hA u).meromorphicAt.pow (d u))
    rw [ho, Finset.sum_eq_single_of_mem w hw]
    · change meromorphicOrderAt (A w ^ d w) w = _
      rw [meromorphicOrderAt_pow (hA w).meromorphicAt, (hA w).meromorphicOrderAt_eq, hAo]
      simp
    · intro u hu hne
      change meromorphicOrderAt (A u ^ d u) w = 0
      rw [meromorphicOrderAt_pow (hA u).meromorphicAt, (hA u).meromorphicOrderAt_eq,
        (hA u).analyticOrderAt_eq_zero.mpr (hNear u hu hne)]
      simp
  have hEval : (fun z ↦ p.eval (e z)) = fun z ↦ ∏ u ∈ T, A u z ^ d u := by
    funext z
    simp [p, A, Polynomial.eval_prod]
  rw [meromorphicOrderAt_congr (he w)]
  change meromorphicOrderAt ((fun z ↦ p.eval (e z)) * Z F S μ ω f) w = _
  have hM : MeromorphicAt (fun z ↦ ∏ u ∈ T, A u z ^ d u) w :=
    MeromorphicAt.fun_prod (fun u _ ↦ (hA u).meromorphicAt.pow (d u))
  have hfM : MeromorphicAt (Z F S μ ω f) w := sLocalProductZetaContinued_meromorphic F S μ ω _ _ f w
  have hfO : meromorphicOrderAt (Z F S μ ω f) w = -(sLocalArchPoleCount F S ω w : WithTop ℤ) :=
    hfOrder w
  rw [hEval, meromorphicOrderAt_mul hM hfM, hProd, hfO]
  change ((d w : ℤ) : WithTop ℤ) + ↑(-(sLocalArchPoleCount F S ω w : ℤ)) = ↑(-(k w : ℤ))
  rw [← WithTop.coe_add, WithTop.coe_eq_coe]
  have hkw := hk w hw
  dsimp [d]
  omega

include hν in
/-- Any finite selection of pole orders up to the allowed multiplicities
can be attained exactly by one test in the full finite principal-value range. -/
theorem exists_sLocalArchPrescribedFinitePoleOrders (ω : PontryaginDual (K F S))
    (T : Finset ℂ) (k : ℂ → ℕ) (hk : ∀ w ∈ T, k w ≤ sLocalArchPoleCount F S ω w) :
    ∃ f ∈ Full F S, ∀ w ∈ T, meromorphicOrderAt (Z F S μ ω f) w = -(k w : WithTop ℤ) := by
  obtain ⟨f, hf, ho⟩ := exists_sLocalArchFullPoleOrderTest F S μ ω
  exact exists_sLocalArchPrescribedFinitePoleOrders_of_closed_under_exp F S μ ω (Full F S)
    (exists_sLocalArchExpMultiply F S μ ν hν ω) f hf ho T k hk

private abbrev V (ω : PontryaginDual (K F S)) := sLocalArchPolarImage F S ν ω
private abbrev I (ω : PontryaginDual (K F S)) (N : InfinitePlace F → ℕ) :=
  SLocalArchCutoffIndex F S ω N

include hν in
private theorem sLocalArchCutoff_relation (ω : PontryaginDual (K F S)) (N : InfinitePlace F → ℕ)
    [Fintype (I F S ω N)] (a : I F S ω N → ℂ)
    (ha : ∀ q : V F S ν ω, ∑ i, a i * sLocalArchCutoffCoefficients F S μ ν hν ω N q i = 0)
    (i₀ : I F S ω N) : a i₀ = 0 := by
  by_contra h₀
  let c := i₀.val.val.1
  let P (n : ℕ) := ∃ i : I F S ω N, i.val.val.1 = c ∧ i.val.val.2 = n ∧ a i ≠ 0
  have hP : ∃ n, P n := ⟨i₀.val.val.2, i₀, rfl, rfl, h₀⟩
  let k := Nat.find hP
  have hPk : P k := Nat.find_spec hP
  obtain ⟨i, hi, hik, hia⟩ := hPk
  let T := sLocalArchPoleCutoff F S ω N
  let n (w : ℂ) := if w = c then k else 0
  have hkle : k ≤ sLocalArchPoleCount F S ω c := by
    rw [← hi, ← hik]
    exact i.val.property.2
  have hkp : 0 < k := hik ▸ i.val.property.1
  have hT (w : ℂ) (_ : w ∈ T) : n w ≤ sLocalArchPoleCount F S ω w := by
    by_cases hw : w = c
    · subst w
      simpa [n] using hkle
    · simp [n, hw]
  obtain ⟨f, hf, ho⟩ := exists_sLocalArchPrescribedFinitePoleOrders F S μ ν hν ω T n hT
  let q : V F S ν ω :=
    ⟨(sLocalHomogeneousThetaKernel F S ν ω).mkQ f, ⟨f, hf, rfl⟩⟩
  have hcoeff (j : I F S ω N) :
      sLocalArchCutoffCoefficients F S μ ν hν ω N q j =
        sLocalLaurentCoeff F S μ ω j.val.val.1 j.val.val.2 f := rfl
  have hc : c ∈ T := i₀.property
  have hok : meromorphicOrderAt (Z F S μ ω f) c = -(k : WithTop ℤ) := by
    simpa [n] using ho c hc
  have hmain : a i * sLocalArchCutoffCoefficients F S μ ν hν ω N q i ≠ 0 := by
    rw [hcoeff, hi, hik]
    exact mul_ne_zero hia (sLocalLaurentCoeff_ne_zero_of_exact_order F S μ ω f c k hkp hok)
  have hRest (j : I F S ω N) (_ : j ∈ Finset.univ) (hne : j ≠ i) :
      a j * sLocalArchCutoffCoefficients F S μ ν hν ω N q j = 0 := by
    rw [hcoeff]
    by_cases hj : j.val.val.1 = c
    · by_cases hlt : j.val.val.2 < k
      · have ha₀ : a j = 0 := by
          by_contra hj'
          exact Nat.find_min hP hlt ⟨j, hj, rfl, hj'⟩
        rw [ha₀, zero_mul]
      · have hne' : j.val.val.2 ≠ k := fun he ↦
          hne (Subtype.ext (Subtype.ext (Prod.ext (hj.trans hi.symm) (he.trans hik.symm))))
        have hklt : k < j.val.val.2 := lt_of_le_of_ne (le_of_not_gt hlt) hne'.symm
        have hb : (↑(-(k : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (Z F S μ ω f) c := by
          rw [hok]
          exact le_rfl
        rw [hj, (sLocalLaurentCoeff_vanish_iff F S μ ω c k f).mpr hb _ hklt, mul_zero]
    · have hb : (↑(-(0 : ℤ)) : WithTop ℤ) ≤
          meromorphicOrderAt (Z F S μ ω f) j.val.val.1 := by
        rw [ho _ j.property]
        simp [n, hj]
      rw [(sLocalLaurentCoeff_vanish_iff F S μ ω j.val.val.1 0 f).mpr hb _
        j.val.property.1, mul_zero]
  exact hmain ((Finset.sum_eq_single_of_mem i (Finset.mem_univ _) hRest).symm.trans (ha q))

include hν in
/-- The full finite principal-value image realizes every finite cutoff
array of archimedean Laurent coefficients. -/
theorem sLocalArchCutoffCoefficients_surjective (ω : PontryaginDual (K F S))
    (N : InfinitePlace F → ℕ) :
    Surjective (sLocalArchCutoffCoefficients F S μ ν hν ω N) := by
  let J := I F S ω N
  letI : Finite J := sLocalArchCutoffIndex_finite F S ω N
  letI : Fintype J := Fintype.ofFinite J
  let A := (sLocalArchCutoffCoefficients F S μ ν hν ω N).toLinearMap
  change Surjective A
  apply LinearMap.dualMap_injective_iff.mp
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_iff.mpr
  intro l hl
  have hExpand (x : J → ℂ) : l x = ∑ j : J, l (Pi.single j 1) * x j := by
    have he : x = ∑ j : J, x j • Pi.single j (1 : ℂ) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne (Ne.symm hij)]
    conv_lhs => rw [he, map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]
  have hRel (q : V F S ν ω) :
      ∑ j : J, l (Pi.single j 1) * sLocalArchCutoffCoefficients F S μ ν hν ω N q j = 0 := by
    rw [← hExpand]
    exact DFunLike.congr_fun hl q
  have hZero := sLocalArchCutoff_relation F S μ ν hν ω N (fun j => l (Pi.single j 1)) hRel
  apply LinearMap.ext
  intro x
  simpa only [hZero, zero_mul, Finset.sum_const_zero, LinearMap.zero_apply] using hExpand x

include hν in
/-- The Laurent coefficient functionals in each finite cutoff are
linearly independent on the actual principal-value image. -/
theorem sLocalArchCutoffCoefficients_linearIndependent (ω : PontryaginDual (K F S))
    (N : InfinitePlace F → ℕ) :
    LinearIndependent ℂ (fun i : I F S ω N ↦
      sLocalArchLaurentCoeff F S μ ν hν ω i.val.val.1 i.val.val.2) := by
  let J := I F S ω N
  letI : Finite J := sLocalArchCutoffIndex_finite F S ω N
  letI : Fintype J := Fintype.ofFinite J
  let b (i : J) : StrongDual ℂ (V F S ν ω) :=
    sLocalArchLaurentCoeff F S μ ν hν ω i.val.val.1 i.val.val.2
  change LinearIndependent ℂ b
  have hLI := Fintype.linearIndependent_iff (R := ℂ) (v := b)
  refine hLI.mpr fun a ha i ↦ sLocalArchCutoff_relation F S μ ν hν ω N a (fun q ↦ ?_) i
  have h := DFunLike.congr_fun ha q
  change ∑ j : J, a j * b j q = 0
  simpa only [sum_apply, smul_apply, smul_eq_mul, zero_apply] using h

include hν in
/-- The finite filtration quotient is the entire finite coefficient space
with its product topology. -/
def sLocalArchPoleFiltration_equiv_coefficients (ω : PontryaginDual (K F S))
    (N : InfinitePlace F → ℕ) :
    (V F S ν ω ⧸ sLocalArchPoleFiltration F S μ ν hν ω N) ≃L[ℂ] (I F S ω N → ℂ) := by
  let J := I F S ω N
  letI : Finite J := sLocalArchCutoffIndex_finite F S ω N
  letI : Fintype J := Fintype.ofFinite J
  let T := sLocalArchPoleFiltration F S μ ν hν ω N
  let A := (sLocalArchCutoffCoefficients F S μ ν hν ω N).toLinearMap
  let e : (V F S ν ω ⧸ T) ≃ₗ[ℂ] (J → ℂ) :=
    A.quotKerEquivOfSurjective (sLocalArchCutoffCoefficients_surjective F S μ ν hν ω N)
  letI : FiniteDimensional ℂ (V F S ν ω ⧸ T) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  letI : IsClosed (T : Set (V F S ν ω)) := sLocalArchPoleFiltration_isClosed F S μ ν hν ω N
  letI : T3Space (V F S ν ω ⧸ T) := Submodule.t3_quotient_of_isClosed T
  letI : T2Space (V F S ν ω ⧸ T) := inferInstance
  exact e.toContinuousLinearEquiv

include hν in
/-- Finite interpolation makes the coefficient image dense in the full
product of Laurent coordinates. -/
theorem sLocalArchPolarQuotientCoefficients_denseRange (ω : PontryaginDual (K F S)) :
    DenseRange (sLocalArchPolarQuotientCoefficients F S μ ν hν ω) := by
  intro a
  apply mem_closure_iff_nhds.mpr
  intro U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨J, W, hW, hJU⟩ := hU
  choose n hn using fun i : SLocalArchPoleIndex F S ω ↦
    (sLocalArchPoleCount_pos_iff_exists_cutoff F S ω i.val.1).mp
      (i.property.1.trans_le i.property.2)
  let N (_ : InfinitePlace F) := ∑ i ∈ J, n i
  have hCut (i : SLocalArchPoleIndex F S ω) (hi : i ∈ J) :
      i.val.1 ∈ sLocalArchPoleCutoff F S ω N :=
    sLocalArchPoleCutoff_mono F S ω
      (fun _ ↦ Finset.single_le_sum (fun j _ ↦ Nat.zero_le (n j)) hi) (hn i)
  obtain ⟨q, hq⟩ := sLocalArchCutoffCoefficients_surjective F S μ ν hν ω N
    (fun i ↦ a i.val)
  let Q := sLocalArchPolarQuotientCoefficients F S μ ν hν ω
  refine ⟨Q (Submodule.Quotient.mk q), ⟨hJU ?_, Submodule.Quotient.mk q, rfl⟩⟩
  intro i hi
  change sLocalArchLaurentCoeff F S μ ν hν ω i.val.1 i.val.2 q ∈ W i
  have he : sLocalArchLaurentCoeff F S μ ν hν ω i.val.1 i.val.2 q = a i :=
    congrFun hq ⟨i, hCut i hi⟩
  rw [he]
  exact mem_of_mem_nhds (hW i)

end

end Masullo
