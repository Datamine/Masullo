import RelativeIdelicNorm
import PontryaginBidual
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.PontryaginDual

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct

namespace Masullo

noncomputable section

private abbrev FinRat := FiniteAdeleRing (𝓞 ℚ) ℚ
private abbrev A := Adeles ℚ
private abbrev I := finiteIntegralAdeles ℚ
private abbrev finDiag : ℚ →+* FinRat := algebraMap ℚ FinRat
private abbrev ratDiag : ℚ →+* A := algebraMap ℚ A

/-- The positive exponential on the real quotient by the integers. -/
private def realPhase : ℝ →+ Additive Circle where
  toFun x := Additive.ofMul (Circle.exp (2 * Real.pi * x))
  map_zero' := by simp
  map_add' x y := by
    change Circle.exp (2 * Real.pi * (x + y)) = Circle.exp (2 * Real.pi * x) * Circle.exp (2 * Real.pi * y)
    rw [mul_add, Circle.exp_add]

private theorem realPhase_int (z : ℤ) : realPhase (z : ℝ) = 0 := by
  change Circle.exp (2 * Real.pi * (z : ℝ)) = 1
  rw [mul_comm, Circle.exp_intCast_mul, Circle.exp_two_pi, one_zpow]

private theorem realPhase_eq_zero_iff (x : ℝ) :
    realPhase x = 0 ↔ ∃ z : ℤ, (z : ℝ) = x := by
  refine ⟨fun h => ?_, ?_⟩
  · have he : Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) = 1 := by
      have hh := congrArg (fun u : Additive Circle => (u.toMul : ℂ)) h
      change (Circle.exp (2 * Real.pi * x) : ℂ) = ((1 : Circle) : ℂ) at hh
      rwa [Circle.coe_exp, Circle.coe_one] at hh
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    have hIm := congrArg Complex.im hn
    push_cast at hIm
    have h' : 2 * Real.pi * x = (n : ℝ) * (2 * Real.pi) := by
      simpa [Complex.mul_im, Complex.mul_re] using hIm
    refine ⟨n, mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity) ?_⟩
    exact (mul_comm (2 * Real.pi) (n : ℝ)).trans h'.symm
  · rintro ⟨n, rfl⟩
    exact realPhase_int n

private theorem realPhase_continuous : Continuous realPhase :=
  continuous_ofMul.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))

private theorem integer_of_finDiag_integral {r : ℚ} (hr : finDiag r ∈ I) :
    ∃ z : ℤ, (z : ℚ) = r := by
  obtain ⟨z, hz⟩ := (finiteDiagonal_mem_integral ℚ r).mp hr
  exact ⟨Rat.ringOfIntegersEquiv z, (Rat.ringOfIntegersEquiv_apply_coe z).trans hz⟩

private def finiteRepresentative (a : FinRat) : ℚ :=
  (finiteAdele_sub_diagonal ℚ a).choose

private theorem finiteRepresentative_spec (a : FinRat) :
    a - finDiag (finiteRepresentative a) ∈ I :=
  (finiteAdele_sub_diagonal ℚ a).choose_spec

private def finitePhaseValue (a : FinRat) : Additive Circle :=
  realPhase (finiteRepresentative a : ℝ)

private theorem finitePhaseValue_eq {a : FinRat} {r : ℚ} (hr : a - finDiag r ∈ I) :
    finitePhaseValue a = realPhase (r : ℝ) := by
  have h : finDiag (finiteRepresentative a - r) ∈ I := by
    rw [map_sub, show finDiag (finiteRepresentative a) - finDiag r =
      (a - finDiag r) - (a - finDiag (finiteRepresentative a)) by abel]
    exact I.sub_mem hr (finiteRepresentative_spec a)
  obtain ⟨z, hz⟩ := integer_of_finDiag_integral h
  have hz' : (z : ℝ) = (finiteRepresentative a : ℝ) - (r : ℝ) := by exact_mod_cast hz
  apply sub_eq_zero.mp
  change realPhase (finiteRepresentative a : ℝ) - realPhase (r : ℝ) = 0
  rw [← map_sub, ← hz', realPhase_int]

private def finitePhase : FinRat →+ Additive Circle where
  toFun := finitePhaseValue
  map_zero' := by
    simpa using finitePhaseValue_eq (a := 0) (r := 0) (by simp)
  map_add' a b := by
    have h : a + b - finDiag (finiteRepresentative a + finiteRepresentative b) ∈ I := by
      rw [map_add, add_sub_add_comm]
      exact I.add_mem (finiteRepresentative_spec a) (finiteRepresentative_spec b)
    rw [finitePhaseValue_eq h, Rat.cast_add, map_add]
    rfl

private theorem finitePhase_eq_zero_iff (a : FinRat) : finitePhase a = 0 ↔ a ∈ I := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (realPhase_eq_zero_iff (finiteRepresentative a : ℝ)).mp h
    have hq : (z : ℚ) = finiteRepresentative a := by exact_mod_cast hz
    have hr : finDiag (finiteRepresentative a) ∈ I := by
      apply (finiteDiagonal_mem_integral ℚ _).mpr
      exact ⟨Rat.ringOfIntegersEquiv.symm z, (Rat.ringOfIntegersEquiv_symm_apply_coe z).trans hq⟩
    exact sub_add_cancel a _ ▸ I.add_mem (finiteRepresentative_spec a) hr
  · intro h
    change finitePhaseValue a = 0
    simpa using finitePhaseValue_eq (a := a) (r := 0) (by simpa using h)

private theorem finitePhase_continuous : Continuous finitePhase := by
  apply continuous_of_tendsto_nhds_zero
  have hU : IsOpen (I : Set FinRat) := by
    change IsOpen {a : FinRat | a ∈ I}
    simp only [mem_finiteIntegralAdeles_iff]
    exact RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring (v.adicCompletion ℚ))
  have hm : ∀ᶠ a : FinRat in 𝓝 0, a ∈ I := hU.mem_nhds (I.zero_mem)
  have he : finitePhase =ᶠ[𝓝 0] (fun _ : FinRat => (0 : Additive Circle)) :=
    hm.mono fun a ha => (finitePhase_eq_zero_iff a).2 ha
  exact tendsto_const_nhds.congr' he.symm

/-- The real coordinate at the unique infinite place of the rational adeles. -/
def rationalArchCoordinate : InfiniteAdeleRing ℚ →+* ℝ :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom.comp
    (Pi.evalRingHom _ Rat.infinitePlace)

theorem rationalArchCoordinate_continuous : Continuous rationalArchCoordinate :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

theorem rationalArchCoordinate_injective : Injective rationalArchCoordinate := by
  intro a b h
  have h₀ : a Rat.infinitePlace = b Rat.infinitePlace :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective h
  funext v
  rwa [Subsingleton.elim v Rat.infinitePlace]

@[simp] theorem rationalArchCoordinate_diag (r : ℚ) :
    rationalArchCoordinate (ratDiag r).1 = (r : ℝ) := by
  change InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    (algebraMap ℚ Rat.infinitePlace.Completion r) = (r : ℝ)
  exact RingHom.map_rat_algebraMap
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).toRingHom r

/-- The standard rational adelic character constructed using integral finite
reduction. For a finite representative $r$ its value is $e^{2πi(a_∞-r)}$. -/
def rationalAdelicCharacter : A →+ Additive Circle :=
  realPhase.comp (rationalArchCoordinate.toAddMonoidHom.comp (AddMonoidHom.fst _ _)) -
    finitePhase.comp (AddMonoidHom.snd _ _)

theorem rationalAdelicCharacter_continuous : Continuous rationalAdelicCharacter :=
  (realPhase_continuous.comp (rationalArchCoordinate_continuous.comp continuous_fst)).sub
    (finitePhase_continuous.comp continuous_snd)

theorem rationalAdelicCharacter_apply_of_integral_sub {a : A} {r : ℚ}
    (hr : a.2 - finDiag r ∈ I) :
    rationalAdelicCharacter a = realPhase (rationalArchCoordinate a.1 - (r : ℝ)) := by
  change realPhase (rationalArchCoordinate a.1) - finitePhaseValue a.2 = _
  rw [finitePhaseValue_eq hr, map_sub]

/-- The rational global character is the positive real exponential when
the finite component vanishes. -/
theorem rationalAdelicCharacter_apply_of_zero_finite (a : Adeles ℚ) (ha : a.2 = 0) :
    rationalAdelicCharacter a =
      Additive.ofMul (Circle.exp (2 * Real.pi * rationalArchCoordinate a.1)) := by
  have h := rationalAdelicCharacter_apply_of_integral_sub (a := a) (r := 0) (by simp [ha])
  simpa [realPhase] using h

@[simp] theorem rationalAdelicCharacter_diagonal (r : ℚ) :
    rationalAdelicCharacter (ratDiag r) = 0 := by
  rw [rationalAdelicCharacter_apply_of_integral_sub (r := r), rationalArchCoordinate_diag,
    sub_self, map_zero]
  change finDiag r - finDiag r ∈ I
  rw [sub_self]
  exact I.zero_mem

private theorem rationalAdelicCharacter_sub_diagonal (a : A) (r : ℚ)
    (h : ∀ x : ℚ, rationalAdelicCharacter (a * ratDiag x) = 0) :
    ∀ x : ℚ, rationalAdelicCharacter ((a - ratDiag r) * ratDiag x) = 0 := by
  intro x
  rw [sub_mul, ← map_mul, map_sub, h, rationalAdelicCharacter_diagonal, sub_zero]

/-- The standard rational multiplication pairing has the diagonal rationals
as their own annihilator. -/
theorem rationalAdelicCharacter_annihilator (a : A) :
    (∀ x : ℚ, rationalAdelicCharacter (a * ratDiag x) = 0) ↔ ∃ r : ℚ, ratDiag r = a := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := finiteAdele_sub_diagonal ℚ a.2
    let b := a - ratDiag r
    have hb : ∀ x : ℚ, rationalAdelicCharacter (b * ratDiag x) = 0 :=
      rationalAdelicCharacter_sub_diagonal a r h
    have hbf : b.2 ∈ I := hr
    have hb₀ : rationalAdelicCharacter b = 0 := by simpa only [map_one, mul_one] using hb 1
    have hbPhase : realPhase (rationalArchCoordinate b.1) = 0 := by
      have h := rationalAdelicCharacter_apply_of_integral_sub (a := b) (r := 0)
        (by simpa using hbf)
      simpa only [hb₀, Rat.cast_zero, sub_zero] using h.symm
    obtain ⟨z, hz⟩ := (realPhase_eq_zero_iff _).mp hbPhase
    let d := b - ratDiag (z : ℚ)
    have hd : ∀ x : ℚ, rationalAdelicCharacter (d * ratDiag x) = 0 :=
      rationalAdelicCharacter_sub_diagonal b (z : ℚ) hb
    have hdarch : d.1 = 0 := by
      apply rationalArchCoordinate_injective
      change rationalArchCoordinate (b.1 - (ratDiag (z : ℚ)).1) = rationalArchCoordinate 0
      rw [map_sub, map_zero, rationalArchCoordinate_diag, Rat.cast_intCast, hz, sub_self]
    have hd1 (n : ℕ) (hn : n ≠ 0) :
        (finDiag ((n : ℚ)⁻¹)) * d.2 ∈ I := by
      let y := d * ratDiag ((n : ℚ)⁻¹)
      have hyarch : y.1 = 0 := by
        change d.1 * (ratDiag ((n : ℚ)⁻¹)).1 = 0
        rw [hdarch, zero_mul]
      have hyPhase : rationalAdelicCharacter y = 0 := hd _
      change realPhase (rationalArchCoordinate y.1) - finitePhase y.2 = 0 at hyPhase
      rw [hyarch, map_zero, map_zero, zero_sub, neg_eq_zero] at hyPhase
      have hyf := (finitePhase_eq_zero_iff y.2).mp hyPhase
      change d.2 * finDiag ((n : ℚ)⁻¹) ∈ I at hyf
      rwa [mul_comm] at hyf
    have hdf : d.2 = 0 := by
      apply finiteAdele_eq_zero_of_forall_nat_mul ℚ
      intro n hn
      refine ⟨finDiag ((n : ℚ)⁻¹) * d.2, hd1 n hn, ?_⟩
      rw [← mul_assoc, ← map_natCast finDiag, ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), map_one, one_mul]
    have hd0 : d = 0 := Prod.ext hdarch hdf
    refine ⟨r + (z : ℚ), ?_⟩
    rw [map_add]
    have he : b = ratDiag (z : ℚ) := sub_eq_zero.mp hd0
    exact (congrArg (ratDiag r + ·) he).symm.trans (add_sub_cancel _ _)
  · rintro ⟨r, rfl⟩ x
    rw [← map_mul, rationalAdelicCharacter_diagonal]


variable (F : Type*) [Field F] [NumberField F]

/-- The standard adelic character is the rational character composed with the
trace on the finite free algebra of adeles. -/
def standardAdelicCharacter : Adeles F →+ Additive Circle :=
  rationalAdelicCharacter.comp (relativeAdelicTraceRat F)

theorem standardAdelicCharacter_continuous : Continuous (standardAdelicCharacter F) :=
  rationalAdelicCharacter_continuous.comp (relativeAdelicTraceRat_continuous F)

@[simp] theorem standardAdelicCharacter_diagonal (r : F) :
    standardAdelicCharacter F (algebraMap F (Adeles F) r) = 0 := by
  change rationalAdelicCharacter (relativeAdelicTraceRat F (algebraMap F (Adeles F) r)) = 0
  rw [relativeAdelicTraceRat_diagonal, rationalAdelicCharacter_diagonal]

/-- The adele with zero archimedean part and the given finite component. -/
def finiteAdelicTranslation (u : FiniteAdeleRing (𝓞 F) F) : Adeles F := (0, u)

/-- The trace of an adele with zero archimedean component has zero
archimedean component. This follows from linearity over the rational adeles. -/
theorem relativeAdelicTraceRat_finite_fst (u : FiniteAdeleRing (𝓞 F) F) :
    (relativeAdelicTraceRat F (finiteAdelicTranslation F u)).1 = 0 := by
  let e := finiteAdelicTranslation ℚ 1
  let x := finiteAdelicTranslation F u
  have he : adelesExtension ℚ F e = finiteAdelicTranslation F 1 := by
    apply Prod.ext
    · exact (infiniteAdelesExtension ℚ F).map_zero
    · exact (finiteAdelesExtension ℚ F).map_one
  have h : adelesExtension ℚ F e * x = x := by
    rw [he]
    apply Prod.ext
    · exact zero_mul _
    · exact one_mul _
  have ht := relativeAdelicTraceRat_mul_rat F e x
  rw [h] at ht
  exact (congrArg Prod.fst ht).trans (zero_mul _)

/-- The rational character vanishes on a finite adele exactly when all its
coordinates are integral. -/
theorem rationalAdelicCharacter_finite_eq_zero_iff (u : FinRat) :
    rationalAdelicCharacter (finiteAdelicTranslation ℚ u) = 0 ↔ u ∈ I := by
  change realPhase (rationalArchCoordinate 0) - finitePhase u = 0 ↔ u ∈ I
  rw [map_zero, map_zero, zero_sub, neg_eq_zero, finitePhase_eq_zero_iff]

/-- The kernel of the standard character on finite adeles is the preimage of
the integral rational finite adeles under the finite component of the trace. -/
theorem standardAdelicCharacter_finite_eq_zero_iff (u : FiniteAdeleRing (𝓞 F) F) :
    standardAdelicCharacter F (finiteAdelicTranslation F u) = 0 ↔
      (relativeAdelicTraceRat F (finiteAdelicTranslation F u)).2 ∈ finiteIntegralAdeles ℚ := by
  let z := relativeAdelicTraceRat F (finiteAdelicTranslation F u)
  change rationalAdelicCharacter z = 0 ↔ z.2 ∈ I
  have hz : z = finiteAdelicTranslation ℚ z.2 :=
    Prod.ext (relativeAdelicTraceRat_finite_fst F u) rfl
  conv_lhs => rw [hz]
  exact rationalAdelicCharacter_finite_eq_zero_iff z.2

/-- The kernel of the character on the finite adeles is open. -/
theorem standardAdelicCharacter_finite_kernel_open :
    IsOpen {u : FiniteAdeleRing (𝓞 F) F | standardAdelicCharacter F (finiteAdelicTranslation F u) = 0} := by
  simp_rw [standardAdelicCharacter_finite_eq_zero_iff F]
  have hI : IsOpen (I : Set FinRat) := by
    change IsOpen {a : FinRat | a ∈ I}
    simp only [mem_finiteIntegralAdeles_iff]
    exact RestrictedProduct.isOpen_forall_mem
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion ℚ))
  have h : Continuous (fun u => (relativeAdelicTraceRat F (finiteAdelicTranslation F u)).2) :=
    continuous_snd.comp ((relativeAdelicTraceRat_continuous F).comp
      (continuous_const.prodMk continuous_id))
  exact hI.preimage h

/-- On the finite component of a diagonal element, the standard character
detects whether the rational field trace is an integer. -/
theorem standardAdelicCharacter_finite_diagonal_eq_zero_iff (x : F) :
    standardAdelicCharacter F
      (finiteAdelicTranslation F (algebraMap F (FiniteAdeleRing (𝓞 F) F) x)) = 0 ↔
      ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ F x := by
  let e := finiteAdelicTranslation ℚ 1
  let j := algebraMap F (Adeles F)
  have he : adelesExtension ℚ F e = finiteAdelicTranslation F 1 := by
    apply Prod.ext
    · exact (infiniteAdelesExtension ℚ F).map_zero
    · exact (finiteAdelesExtension ℚ F).map_one
  have hx : adelesExtension ℚ F e * j x =
      finiteAdelicTranslation F (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) := by
    rw [he]
    apply Prod.ext
    · change 0 * (j x).1 = 0
      exact zero_mul _
    · change 1 * (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) = _
      exact one_mul _
  rw [← hx]
  change rationalAdelicCharacter (relativeAdelicTraceRat F (adelesExtension ℚ F e * j x)) = 0 ↔ _
  rw [relativeAdelicTraceRat_mul_rat, relativeAdelicTraceRat_diagonal]
  let r := Algebra.trace ℚ F x
  change realPhase (rationalArchCoordinate (e * ratDiag r).1) -
    finitePhase (e * ratDiag r).2 = 0 ↔ _
  have h1 : (e * ratDiag r).1 = 0 := zero_mul _
  have h2 : (e * ratDiag r).2 = finDiag r := one_mul _
  rw [h1, h2, map_zero, map_zero, zero_sub, neg_eq_zero, finitePhase_eq_zero_iff]
  constructor
  · exact integer_of_finDiag_integral
  · rintro ⟨z, hz⟩
    change finDiag (Algebra.trace ℚ F x) ∈ I
    rw [← hz, map_intCast]
    exact intCast_mem _ _

private abbrev Index (F : Type*) [Field F] [NumberField F] := Module.Free.ChooseBasisIndex ℤ (𝓞 F)

private theorem relativeAdelicTraceRat_coordinate
    (b : letI := (adelesExtension ℚ F).toAlgebra
         Module.Basis (Index F) (Adeles ℚ) (Adeles F))
    (hb : ∀ i, b i = algebraMap F (Adeles F) (integralBasis F i))
    (a : Adeles F) (i : Index F) :
    letI := (adelesExtension ℚ F).toAlgebra
    relativeAdelicTraceRat F
      (a * algebraMap F (Adeles F) ((integralBasis F).traceDual i)) = b.repr a i := by
  letI := (adelesExtension ℚ F).toAlgebra
  let j := algebraMap F (Adeles F)
  let d := (integralBasis F).traceDual i
  let c := b.repr a
  change relativeAdelicTraceRat F (a * j d) = c i
  calc
    _ = relativeAdelicTraceRat F ((∑ k, c k • b k) * j d) :=
      congrArg (fun a' => relativeAdelicTraceRat F (a' * j d)) (b.sum_repr a).symm
    _ = ∑ k, c k * relativeAdelicTraceRat F (b k * j d) := by
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change relativeAdelicTraceRat F ((adelesExtension ℚ F (c k) * b k) * j d) = _
      rw [mul_assoc, relativeAdelicTraceRat_mul_rat]
    _ = ∑ k, if k = i then c k else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, ← map_mul, relativeAdelicTraceRat_diagonal]
      change c k * ratDiag (Algebra.trace ℚ F (integralBasis F k * (integralBasis F).traceDual i)) = _
      rw [Module.Basis.trace_mul_traceDual]
      split_ifs <;> simp
    _ = _ := by simp

/-- The trace-dual basis reconstructs any adele from its trace pairings
against the integral basis. -/
theorem relativeAdelicTraceRat_sum_traceDual (a : Adeles F) :
    (∑ i, adelesExtension ℚ F (relativeAdelicTraceRat F
      (a * algebraMap F (Adeles F) (integralBasis F i))) *
      algebraMap F (Adeles F) ((integralBasis F).traceDual i)) = a := by
  letI := (adelesExtension ℚ F).toAlgebra
  let j := algebraMap F (Adeles F)
  let b := integralBasis F
  let d := b.traceDual
  let t (z : Adeles F) : Adeles F := ∑ i, adelesExtension ℚ F
    (relativeAdelicTraceRat F (z * j (b i))) * j (d i)
  change t a = a
  have hdiag (r : F) : t (j r) = j r := by
    calc
      t (j r) = ∑ i, j ((d.repr r i) • d i) := by
        dsimp only [t]
        apply Finset.sum_congr rfl
        intro i _
        rw [← map_mul, relativeAdelicTraceRat_diagonal, adelesExtension_diagonal,
          Module.Basis.traceDual_repr_apply]
        change j (algebraMap ℚ F (Algebra.trace ℚ F (r * b i))) * j (d i) = _
        rw [← j.map_mul, Algebra.smul_def]
        rfl
      _ = j r := by rw [← map_sum, d.sum_repr]
  obtain ⟨B, hB⟩ := exists_adelicIntegralBasis F
  have hlin (p : Adeles ℚ) (z : Adeles F) : t (adelesExtension ℚ F p * z) =
      adelesExtension ℚ F p * t z := by
    dsimp [t]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, relativeAdelicTraceRat_mul_rat, map_mul, mul_assoc]
  have hadd (z w : Adeles F) : t (z + w) = t z + t w := by
    simp only [t, add_mul, map_add, Finset.sum_add_distrib]
  let T : Adeles F →+ Adeles F :=
    { toFun := t
      map_zero' := by simp [t]
      map_add' := hadd }
  calc
    t a = T (∑ i, B.repr a i • B i) := congrArg T (B.sum_repr a).symm
    _ = ∑ i, B.repr a i • B i := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      change t (adelesExtension ℚ F (B.repr a i) * B i) = _
      rw [hlin, hB, hdiag]
      rfl
    _ = a := B.sum_repr a

/-- The standard trace pairing has exactly the diagonal field as the
annihilator of the diagonal field in the adeles. -/
theorem standardAdelicCharacter_annihilator (a : Adeles F) :
    (∀ x : F, standardAdelicCharacter F (a * algebraMap F (Adeles F) x) = 0) ↔
      ∃ x : F, algebraMap F (Adeles F) x = a := by
  letI := (adelesExtension ℚ F).toAlgebra
  let j := algebraMap F (Adeles F)
  constructor
  · intro h
    obtain ⟨b, hb⟩ := exists_adelicIntegralBasis F
    have hcoord (i : Index F) :
        ∃ r : ℚ, ratDiag r = b.repr a i := by
      apply (rationalAdelicCharacter_annihilator (b.repr a i)).mp
      intro r
      let d := (integralBasis F).traceDual i
      have he : relativeAdelicTraceRat F (a * j d) = b.repr a i :=
        relativeAdelicTraceRat_coordinate F b hb a i
      have ht := h (algebraMap ℚ F r * d)
      change rationalAdelicCharacter (relativeAdelicTraceRat F (a * j (algebraMap ℚ F r * d))) = 0 at ht
      rw [map_mul j, ← adelesExtension_diagonal ℚ F, mul_left_comm a,
        relativeAdelicTraceRat_mul_rat, he] at ht
      rwa [mul_comm]
    choose r hr using hcoord
    refine ⟨(integralBasis F).equivFun.symm r, ?_⟩
    apply (b.equivFun).injective
    have he := adelicIntegralBasis_sum F b hb r
    rw [← he, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    exact funext hr
  · rintro ⟨x, rfl⟩ y
    rw [← map_mul, standardAdelicCharacter_diagonal]


private theorem standardAdelicCharacter_ne_zero :
    ∃ a : Adeles F, standardAdelicCharacter F a ≠ 0 := by
  let z : A := (algebraMap ℚ (InfiniteAdeleRing ℚ) (1 / 2), 0)
  have hz : rationalAdelicCharacter z ≠ 0 := by
    have h := rationalAdelicCharacter_apply_of_integral_sub (a := z) (r := 0)
      (by change (0 : FinRat) - finDiag 0 ∈ I; simp)
    rw [Rat.cast_zero, sub_zero] at h
    have hz' : rationalArchCoordinate z.1 = (1 / 2 : ℝ) := by
      exact (rationalArchCoordinate_diag (1 / 2)).trans (by norm_num)
    rw [h, hz']
    intro hv
    obtain ⟨n, hn⟩ := (realPhase_eq_zero_iff _).mp hv
    have ht : (2 : ℤ) * n = 1 := by exact_mod_cast (show (2 : ℝ) * n = 1 by linarith)
    omega
  let d := Module.finrank ℚ F
  let dA : A := ratDiag (d : ℚ)
  let e := adelesExtension ℚ F
  letI := e.toAlgebra
  let u := ratDiag (d : ℚ)⁻¹ * z
  refine ⟨e u, ?_⟩
  change rationalAdelicCharacter (relativeAdelicTraceRat F (e u)) ≠ 0
  obtain ⟨b⟩ := rationalAdeleEmbedding_hasBasis F
  have he : relativeAdelicTraceRat F (e u) = dA * u := by
    change Algebra.trace A (Adeles F) (algebraMap A (Adeles F) u) = _
    rw [Algebra.trace_algebraMap_of_basis b, Fintype.card_fin, nsmul_eq_mul]
    rw [← map_natCast ratDiag]
  rw [he]
  have hd : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have hu : dA * u = z := by
    dsimp only [dA, u]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd, map_one, one_mul]
  rwa [hu]

private abbrev P := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
private abbrev Q := Adeles F ⧸ P F

/-- The character indexed by a field element on the additive adelic quotient. -/
def adelicQuotientCharacter (x : F) : PontryaginDual (Multiplicative (Q F)) := by
  let j := algebraMap F (Adeles F)
  let h : Adeles F →+ Additive Circle :=
    (standardAdelicCharacter F).comp ((AddMonoidHom.mulLeft (j x)))
  let q : Q F →+ Additive Circle := QuotientAddGroup.lift (P F) h (by
    rintro _ ⟨r, rfl⟩
    change standardAdelicCharacter F (j x * j r) = 0
    rw [← map_mul, standardAdelicCharacter_diagonal])
  have hq : Continuous q := by
    apply QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    exact (standardAdelicCharacter_continuous F).comp (continuous_const.mul continuous_id)
  exact ⟨q.toMultiplicative, continuous_toMul.comp (hq.comp continuous_toAdd)⟩

@[simp] theorem adelicQuotientCharacter_mk (x : F) (a : Adeles F) :
    adelicQuotientCharacter F x (Multiplicative.ofAdd (QuotientAddGroup.mk a : Q F)) =
      (standardAdelicCharacter F (algebraMap F (Adeles F) x * a)).toMul := rfl

private def adelicQuotientCharacterIndex :
    Multiplicative F →* PontryaginDual (Multiplicative (Q F)) where
  toFun x := adelicQuotientCharacter F x.toAdd
  map_one' := by
    apply PontryaginDual.ext
    intro q
    obtain ⟨g, hg⟩ := QuotientAddGroup.mk_surjective q.toAdd
    have he : q = Multiplicative.ofAdd (QuotientAddGroup.mk g : Q F) :=
      (congrArg Multiplicative.ofAdd hg).symm
    rw [he, adelicQuotientCharacter_mk, show Multiplicative.toAdd (1 : Multiplicative F) = 0 from rfl,
      map_zero, zero_mul, map_zero]
    rfl
  map_mul' x y := by
    apply PontryaginDual.ext
    intro q
    obtain ⟨g, hg⟩ := QuotientAddGroup.mk_surjective q.toAdd
    have he : q = Multiplicative.ofAdd (QuotientAddGroup.mk g : Q F) :=
      (congrArg Multiplicative.ofAdd hg).symm
    rw [he]
    change adelicQuotientCharacter F (x.toAdd + y.toAdd) _ =
      adelicQuotientCharacter F x.toAdd _ * adelicQuotientCharacter F y.toAdd _
    simp only [adelicQuotientCharacter_mk, map_add, add_mul]
    rfl

private theorem adelicQuotientCharacter_trivial (q : Multiplicative (Q F))
    (h : ∀ x : F, adelicQuotientCharacter F x q = 1) : q = 1 := by
  obtain ⟨g, hg⟩ := QuotientAddGroup.mk_surjective q.toAdd
  have he : q = Multiplicative.ofAdd (QuotientAddGroup.mk g : Q F) :=
    (congrArg Multiplicative.ofAdd hg).symm
  obtain ⟨x, hx⟩ := (standardAdelicCharacter_annihilator F g).mp (fun x => by
    have hh := h x
    rw [he, adelicQuotientCharacter_mk, mul_comm] at hh
    exact Additive.toMul.injective hh)
  have hg₀ : (QuotientAddGroup.mk g : Q F) = 0 :=
    (QuotientAddGroup.eq_zero_iff g).mpr ⟨x, hx⟩
  exact he.trans (congrArg Multiplicative.ofAdd hg₀)

private theorem adelicQuotientCharacterIndex_injective :
    Injective (adelicQuotientCharacterIndex F) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hzero (a : Adeles F) : standardAdelicCharacter F (algebraMap F (Adeles F) x.toAdd * a) = 0 := by
    have h := DFunLike.congr_fun hx (Multiplicative.ofAdd (QuotientAddGroup.mk a : Q F))
    change adelicQuotientCharacter F x.toAdd _ = 1 at h
    rw [adelicQuotientCharacter_mk] at h
    exact Additive.toMul.injective h
  apply Multiplicative.toAdd.injective
  by_contra hn
  obtain ⟨a, ha⟩ := standardAdelicCharacter_ne_zero F
  apply ha
  have h := hzero (algebraMap F (Adeles F) x.toAdd⁻¹ * a)
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hn, map_one, one_mul] at h
  exact h

/-- Every character of the compact additive adelic quotient is indexed by a
unique diagonal field element. -/
theorem adelicQuotientCharacter_bijective : Bijective (adelicQuotientCharacter F) := by
  refine ⟨adelicQuotientCharacterIndex_injective F, ?_⟩
  letI : CompactSpace (Q F) := principalAdeles_quotient_compact (F := F)
  letI : T2Space (Q F) := principalAdeles_quotient_hausdorff (F := F)
  letI : CompactSpace (Multiplicative (Q F)) := inferInstanceAs (CompactSpace (Q F))
  letI : T2Space (Multiplicative (Q F)) := inferInstanceAs (T2Space (Q F))
  let D := PontryaginDual (Multiplicative (Q F))
  letI : DiscreteTopology D := inferInstance
  let J := (adelicQuotientCharacterIndex F).range
  let π : D →ₜ* (D ⧸ J) := ⟨QuotientGroup.mk' J, QuotientGroup.continuous_mk⟩
  intro ψ
  by_contra hψ
  have hne : π ψ ≠ 1 := fun h => hψ ((QuotientGroup.eq_one_iff ψ).mp h)
  obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one hne
  obtain ⟨q, hq⟩ := pontryaginBidualEval_surjective_of_compact (G := Multiplicative (Q F))
    (PontryaginDual.map π χ)
  have hq₁ : q = 1 := by
    apply adelicQuotientCharacter_trivial F q
    intro x
    have hx : π (adelicQuotientCharacter F x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨Multiplicative.ofAdd x, rfl⟩
    have h := DFunLike.congr_fun hq (adelicQuotientCharacter F x)
    rwa [pontryaginBidualEval_apply, PontryaginDual.map_apply, hx, map_one] at h
  apply hχ
  have h := DFunLike.congr_fun hq ψ
  rw [hq₁, pontryaginBidualEval_apply, map_one, PontryaginDual.map_apply] at h
  exact h.symm

end

end Masullo
