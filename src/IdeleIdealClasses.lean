import AdelicBounds
import ArchimedeanLogarithms
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.Factorization

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField RestrictedProduct nonZeroDivisors

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

private theorem finiteCoord_nonzero (a : Idele F) (v : Place F) : a.val.2 v ≠ 0 := by
  have h := congrArg (fun x : Adeles F => x.2 v) a.val_inv
  change a.val.2 v * a.inv.2 v = 1 at h
  exact left_ne_zero_of_mul_eq_one h

private theorem finiteCoord_valuation_ne_zero (a : Idele F) (v : Place F) :
    Valued.v (a.val.2 v) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (finiteCoord_nonzero F a v)

/-- The additive order at a finite place. Higher order means a smaller
valuation in the multiplicative valuation convention. -/
def ideleOrder (a : Idele F) (v : Place F) : ℤ :=
  -WithZero.log (Valued.v (a.val.2 v))

theorem ideleOrder_mul (a b : Idele F) (v : Place F) :
    ideleOrder F (a * b) v = ideleOrder F a v + ideleOrder F b v := by
  change -WithZero.log (Valued.v (a.val.2 v * b.val.2 v)) =
    -WithZero.log (Valued.v (a.val.2 v)) + -WithZero.log (Valued.v (b.val.2 v))
  rw [map_mul, WithZero.log_mul (finiteCoord_valuation_ne_zero F a v)
    (finiteCoord_valuation_ne_zero F b v), neg_add]

theorem ideleOrder_eq_zero_iff (a : Idele F) (v : Place F) :
    ideleOrder F a v = 0 ↔ Valued.v (a.val.2 v) = 1 := by
  change -WithZero.log (Valued.v (a.val.2 v)) = 0 ↔ _
  rw [neg_eq_zero]
  constructor
  · intro h
    have he := WithZero.exp_log (finiteCoord_valuation_ne_zero F a v)
    rw [h, WithZero.exp_zero] at he
    exact he.symm
  · intro h
    rw [h, WithZero.log_one]

theorem ideleOrder_finite_support (a : Idele F) :
    ∀ᶠ v in cofinite, ideleOrder F a v = 0 := by
  have ha := a.val.2.2
  have hb := a.inv.2.2
  filter_upwards [ha, hb] with v h₁ h₂
  apply (ideleOrder_eq_zero_iff F a v).2
  have ha' := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp h₁
  have hb' := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp h₂
  have he : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    have h := congrArg (fun x : Adeles F => x.2 v) a.val_inv
    change a.val.2 v * a.inv.2 v = 1 at h
    rw [← map_mul, h, map_one]
  exact le_antisymm ha' (he.symm.trans_le (mul_le_of_le_one_right zero_le hb'))

/-- The valuation divisor of an idele, with actual finite support. -/
def ideleDivisor : Idele F →* Multiplicative (Place F →₀ ℤ) where
  toFun a := Multiplicative.ofAdd
    (Finsupp.mk (ideleOrder_finite_support F a).toFinset (ideleOrder F a)
        (fun _ => (ideleOrder_finite_support F a).mem_toFinset))
  map_one' := by
    apply Finsupp.ext
    intro v
    change -(WithZero.log (Valued.v (1 : v.adicCompletion F))) = 0
    simp
  map_mul' a b := by
    apply Finsupp.ext
    intro v
    exact ideleOrder_mul F a b v

/-- Each finitely supported integer divisor has an idele with those orders. -/
theorem ideleDivisor_surjective : Surjective (ideleDivisor F) := by
  intro d
  let k := Multiplicative.toAdd d
  choose x hx using fun v : Place F => v.valuedAdicCompletion_surjective F (WithZero.exp (-k v))
  have hne (v : Place F) : x v ≠ 0 := by
    intro h
    have he := hx v
    rw [h, map_zero] at he
    exact WithZero.exp_ne_zero he.symm
  have hxR : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F := by
    filter_upwards [k.support.eventually_cofinite_notMem] with v hv
    apply (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr
    rw [hx v, Finsupp.notMem_support_iff.mp hv, neg_zero, WithZero.exp_zero]
  let X : FinAdeles F := ⟨x, hxR⟩
  have hU : IsUnit X := (FiniteAdeleRing.isUnit_iff).mpr ⟨hne, by
    filter_upwards [k.support.eventually_cofinite_notMem] with v hv
    rw [show X v = x v from rfl, hx v, Finsupp.notMem_support_iff.mp hv,
      neg_zero, WithZero.exp_zero]⟩
  let a : Idele F := MulEquiv.prodUnits.symm (1, hU.unit)
  refine ⟨a, ?_⟩
  apply Finsupp.ext
  intro v
  change ideleOrder F a v = k v
  unfold ideleOrder
  rw [show a.val.2 = X from hU.unit_spec, show X v = x v from rfl, hx v, WithZero.log_exp, neg_neg]

private abbrev Fractional := FractionalIdeal (𝓞 F)⁰ F

private theorem prime_zpow_ne_zero (v : Place F) (z : ℤ) :
    (v.asIdeal : Fractional F) ^ z ≠ 0 :=
  zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

private theorem prime_zpow_mulSupport_finite (d : Place F →₀ ℤ) :
    (fun v : Place F => (v.asIdeal : Fractional F) ^ d v).HasFiniteMulSupport := by
  refine d.support.finite_toSet.subset ?_
  intro v hv
  by_contra h
  exact hv (by simp [Finsupp.notMem_support_iff.mp h])

/-- The fractional ideal obtained by multiplying the indicated powers of
the finite primes. -/
def divisorFractionalIdeal : Multiplicative (Place F →₀ ℤ) →* (Fractional F)ˣ where
  toFun d := Units.mk0 (∏ᶠ v : Place F, (v.asIdeal : Fractional F) ^ Multiplicative.toAdd d v)
    (finprod_ne_zero fun v => prime_zpow_ne_zero F v (Multiplicative.toAdd d v))
  map_one' := by
    apply Units.ext
    change (∏ᶠ v : Place F, (v.asIdeal : Fractional F) ^ (0 : ℤ)) = 1
    simp
  map_mul' a b := by
    apply Units.ext
    change (∏ᶠ v : Place F, (v.asIdeal : Fractional F) ^
      (Multiplicative.toAdd a v + Multiplicative.toAdd b v)) =
      (∏ᶠ v : Place F, (v.asIdeal : Fractional F) ^ Multiplicative.toAdd a v) *
        (∏ᶠ v : Place F, (v.asIdeal : Fractional F) ^ Multiplicative.toAdd b v)
    have h (v : Place F) : (v.asIdeal : Fractional F) ^
        (Multiplicative.toAdd a v + Multiplicative.toAdd b v) =
        (v.asIdeal : Fractional F) ^ Multiplicative.toAdd a v *
          (v.asIdeal : Fractional F) ^ Multiplicative.toAdd b v :=
      zpow_add₀ (show (v.asIdeal : Fractional F) ≠ 0 from FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot) _ _
    simp_rw [h]
    exact finprod_mul_distrib (prime_zpow_mulSupport_finite F _) (prime_zpow_mulSupport_finite F _)

theorem divisorFractionalIdeal_surjective : Surjective (divisorFractionalIdeal F) := by
  intro J
  have h := FractionalIdeal.finite_factors J.val
  let d := Finsupp.mk h.toFinset (fun v : Place F => FractionalIdeal.count F v J.val)
    (fun _ => h.mem_toFinset)
  refine ⟨Multiplicative.ofAdd d, Units.ext ?_⟩
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization' F J.ne_zero

/-- The finite divisor map as a map to nonzero fractional ideals. -/
def ideleFractionalIdeal : Idele F →* (Fractional F)ˣ :=
  (divisorFractionalIdeal F).comp (ideleDivisor F)

theorem ideleFractionalIdeal_surjective : Surjective (ideleFractionalIdeal F) :=
  (divisorFractionalIdeal_surjective F).comp (ideleDivisor_surjective F)

theorem ideleFractionalIdeal_count (a : Idele F) (v : Place F) :
    FractionalIdeal.count F v (ideleFractionalIdeal F a).val = ideleOrder F a v :=
  FractionalIdeal.count_finprod F v (ideleOrder F a) (ideleOrder_finite_support F a)

private theorem intValuation_log (v : Place F) {r : 𝓞 F} (hr : r ≠ 0) :
    WithZero.log (v.intValuation r) =
      -((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal (𝓞 F))).factors : ℤ) := by
  rw [v.intValuation_if_neg hr, WithZero.log_exp]

theorem ideleFractionalIdeal_principal (t : Fˣ) :
    ideleFractionalIdeal F (principalIdele F t) = toPrincipalIdeal (𝓞 F) F t := by
  apply Units.ext
  obtain ⟨n, d, he⟩ := IsLocalization.exists_mk'_eq (𝓞 F)⁰ (t : F)
  have hn : n ≠ 0 := fun h => t.ne_zero (by
    rw [← he, h, IsFractionRing.mk'_eq_div, map_zero, zero_div])
  have hd : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hOrd (v : Place F) :
      ideleOrder F (principalIdele F t) v =
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal (𝓞 F))).factors : ℤ) -
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(d : 𝓞 F)} : Ideal (𝓞 F))).factors : ℤ) := by
    change -WithZero.log (Valued.v (algebraMap F (v.adicCompletion F) (t : F))) = _
    have hVal : Valued.v (algebraMap F (v.adicCompletion F) (t : F)) = v.valuation F (t : F) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (t : F)
    rw [hVal, ← he,
      v.valuation_of_mk', WithZero.log_div (v.intValuation_ne_zero n hn)
        (v.intValuation_ne_zero (d : 𝓞 F) hd), intValuation_log F v hn, intValuation_log F v hd]
    abel
  change (∏ᶠ v : Place F, (v.asIdeal : Fractional F) ^ ideleOrder F (principalIdele F t) v) = _
  rw [coe_toPrincipalIdeal, ← he]
  simp_rw [hOrd]
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction hn d

/-- Finite integrality in both directions characterizes the kernel of
the divisor map. -/
theorem ideleDivisor_ker_iff (a : Idele F) :
    a ∈ (ideleDivisor F).ker ↔
      (∀ v : Place F, a.val.2 v ∈ v.adicCompletionIntegers F) ∧
      (∀ v : Place F, a.inv.2 v ∈ v.adicCompletionIntegers F) := by
  have he (v : Place F) : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    have h := congrArg (fun x : Adeles F => x.2 v) a.val_inv
    change a.val.2 v * a.inv.2 v = 1 at h
    rw [← map_mul, h, map_one]
  change (ideleDivisor F a = 1) ↔ _
  have hD : ideleDivisor F a = 1 ↔ ∀ v : Place F, ideleOrder F a v = 0 := by
    constructor
    · intro h v
      exact congrArg (fun z : Multiplicative (Place F →₀ ℤ) => Multiplicative.toAdd z v) h
    · intro h
      exact Finsupp.ext h
  rw [hD]
  constructor
  · intro h
    have hv (v : Place F) : Valued.v (a.val.2 v) = 1 :=
      (ideleOrder_eq_zero_iff F a v).1 (h v)
    refine ⟨fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr (hv v).le, ?_⟩
    intro v
    have hi := he v
    rw [hv v, one_mul] at hi
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr hi.le
  · rintro ⟨h, h'⟩ v
    apply (ideleOrder_eq_zero_iff F a v).2
    have hr := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h v)
    have hi := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h' v)
    exact le_antisymm hr ((he v).symm.trans_le (mul_le_of_le_one_right zero_le hi))

/-- The integral finite-idele condition is open in the full idele group. -/
theorem ideleDivisor_ker_open : IsOpen ((ideleDivisor F).ker : Set (Idele F)) := by
  let S : Set (FinAdeles F) := {a | ∀ v : Place F, a v ∈ v.adicCompletionIntegers F}
  have ho : IsOpen S := RestrictedProduct.isOpen_forall_mem
    (fun v : Place F => Valued.isOpen_valuationSubring (v.adicCompletion F))
  have hEq : ((ideleDivisor F).ker : Set (Idele F)) =
      (fun a : Idele F => a.val.2) ⁻¹' S ∩ (fun a : Idele F => a.inv.2) ⁻¹' S := by
    exact Set.ext (ideleDivisor_ker_iff F)
  rw [hEq]
  have hc₁ : Continuous (fun a : Idele F => a.val.2) :=
    (Units.continuous_val : Continuous (fun a : Idele F => a.val)).snd
  have hc₂ : Continuous (fun a : Idele F => a.inv.2) :=
    (Units.continuous_coe_inv : Continuous (fun a : Idele F => a.inv)).snd
  exact (ho.preimage hc₁).inter (ho.preimage hc₂)

private theorem divisorFractionalIdeal_injective : Injective (divisorFractionalIdeal F) := by
  intro a b hab
  apply Finsupp.ext
  intro v
  let va := Multiplicative.toAdd a
  let vb := Multiplicative.toAdd b
  have ha (d : Place F →₀ ℤ) : ∀ᶠ v in cofinite, d v = 0 :=
    d.support.eventually_cofinite_notMem.mono fun _ h => Finsupp.notMem_support_iff.mp h
  have h := congrArg (fun J : (Fractional F)ˣ => FractionalIdeal.count F v J.val) hab
  change FractionalIdeal.count F v (∏ᶠ w : Place F, (w.asIdeal : Fractional F) ^ va w) =
    FractionalIdeal.count F v (∏ᶠ w : Place F, (w.asIdeal : Fractional F) ^ vb w) at h
  rw [FractionalIdeal.count_finprod F v va (ha va), FractionalIdeal.count_finprod F v vb (ha vb)] at h
  exact h

theorem ideleFractionalIdeal_ker_eq : (ideleFractionalIdeal F).ker = (ideleDivisor F).ker := by
  ext a
  change divisorFractionalIdeal F (ideleDivisor F a) = 1 ↔ ideleDivisor F a = 1
  rw [← map_one (divisorFractionalIdeal F), (divisorFractionalIdeal_injective F).eq_iff]

/-- The actual quotient homomorphism from ideles to ideal classes. -/
def ideleIdealClass : Idele F →* ClassGroup (𝓞 F) :=
  (ClassGroup.mk F).comp (ideleFractionalIdeal F)

theorem ideleIdealClass_surjective : Surjective (ideleIdealClass F) := by
  intro c
  refine ClassGroup.induction F (P := fun c : ClassGroup (𝓞 F) => ∃ g, ideleIdealClass F g = c) ?_ c
  intro J
  obtain ⟨g, hg⟩ := ideleFractionalIdeal_surjective F J
  exact ⟨g, congrArg (ClassGroup.mk F) hg⟩

theorem ideleIdealClass_ker_iff (a : Idele F) :
    a ∈ (ideleIdealClass F).ker ↔
      ∃ (t : Fˣ) (b : (ideleDivisor F).ker), a = principalIdele F t * b.val := by
  change ClassGroup.mk F (ideleFractionalIdeal F a) = 1 ↔ _
  constructor
  · intro h
    let J := (ideleFractionalIdeal F a : Submodule (𝓞 F) F)
    haveI : J.IsPrincipal := (ClassGroup.mk_eq_one_iff).mp h
    obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal J
    have hI : (ideleFractionalIdeal F a).val = FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
      apply Subtype.coe_injective
      change J = ((FractionalIdeal.spanSingleton (𝓞 F)⁰ x : Fractional F) : Submodule (𝓞 F) F)
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx
    have hx0 : x ≠ 0 := by
      intro hx0
      exact (ideleFractionalIdeal F a).ne_zero (by simp [hI, hx0])
    let t := Units.mk0 x hx0
    have ht : ideleFractionalIdeal F (principalIdele F t) = ideleFractionalIdeal F a := by
      rw [ideleFractionalIdeal_principal]
      exact (toPrincipalIdeal_eq_iff).mpr hI.symm
    let b := (principalIdele F t)⁻¹ * a
    have hb : b ∈ (ideleDivisor F).ker := by
      rw [← ideleFractionalIdeal_ker_eq F]
      change ideleFractionalIdeal F ((principalIdele F t)⁻¹ * a) = 1
      rw [map_mul, map_inv, ht, inv_mul_cancel]
    exact ⟨t, ⟨b, hb⟩, by simp [b]⟩
  · rintro ⟨t, b, rfl⟩
    have he (x : Idele F) : x ∈ (ideleDivisor F).ker → x ∈ (ideleFractionalIdeal F).ker := by
      rw [ideleFractionalIdeal_ker_eq F]
      exact id
    have hb : ideleFractionalIdeal F b.val = 1 := he b.val b.property
    rw [map_mul, hb, mul_one, ideleFractionalIdeal_principal]
    apply (ClassGroup.mk_eq_one_iff).mpr
    rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨(t : F), rfl⟩⟩

/-- Haar normalization is independent of the class-group map. Here the
class group is given its usual discrete topology. -/
theorem ideleIdealClass_continuous [TopologicalSpace (ClassGroup (𝓞 F))]
    [DiscreteTopology (ClassGroup (𝓞 F))] :
    Continuous (ideleIdealClass F) := by
  have hk : (ideleDivisor F).ker ≤ (ideleIdealClass F).ker := fun a ha => by
    have h : ideleFractionalIdeal F a = 1 :=
      (show a ∈ (ideleFractionalIdeal F).ker ↔ a ∈ (ideleDivisor F).ker by
        rw [ideleFractionalIdeal_ker_eq F]).mpr ha
    change ClassGroup.mk F (ideleFractionalIdeal F a) = 1
    rw [h, map_one]
  have hOpen : IsOpen ((ideleIdealClass F).ker : Set (Idele F)) :=
    Subgroup.isOpen_mono hk (ideleDivisor_ker_open F)
  apply continuous_of_continuousAt_one (ideleIdealClass F)
  change Tendsto (ideleIdealClass F) (𝓝 (1 : Idele F)) (𝓝 (ideleIdealClass F 1))
  rw [map_one, nhds_discrete (α := ClassGroup (𝓞 F)), tendsto_pure]
  exact hOpen.mem_nhds ((ideleIdealClass F).ker.one_mem)

private theorem ideleExpSection_finite_integral (t : Multiplicative ℝ) :
    ideleExpSection F t ∈ (ideleDivisor F).ker := by
  apply (ideleDivisor_ker_iff F _).mpr
  have h (v : Place F) : (ideleExpSection F t).val.2 v = 1 :=
    congrArg (fun x : FinAdeles F => x v) (ideleExpSection_components F t).2
  have hi (v : Place F) : (ideleExpSection F t).inv.2 v = 1 := by
    change ((ideleExpSection F t)⁻¹).val.2 v = 1
    rw [← map_inv]
    exact congrArg (fun x : FinAdeles F => x v) (ideleExpSection_components F t⁻¹).2
  exact ⟨fun v => h v ▸ one_mem _, fun v => hi v ▸ one_mem _⟩

/-- Every ideal class has a representative of norm one. -/
theorem ideleNormOne_idealClass_surjective :
    Surjective ((ideleIdealClass F).comp (ideleNorm F).ker.subtype) := by
  intro c
  obtain ⟨a, ha⟩ := ideleIdealClass_surjective F c
  let t := Multiplicative.ofAdd (-Real.log (ideleNorm F a))
  let u := ideleExpSection F t
  have hu : ideleNorm F u = (ideleNorm F a)⁻¹ := by
    rw [ideleNorm_expSection F t]
    change Real.exp (-Real.log (ideleNorm F a)) = _
    rw [Real.exp_neg, Real.exp_log (ideleNorm_pos F a)]
  have hNorm : a * u ∈ (ideleNorm F).ker := by
    change ideleNorm F (a * u) = 1
    rw [map_mul, hu, mul_inv_cancel₀ (ideleNorm_pos F a).ne']
  have huClass : ideleIdealClass F u = 1 := by
    have h : ideleFractionalIdeal F u = 1 :=
      (show u ∈ (ideleFractionalIdeal F).ker ↔ u ∈ (ideleDivisor F).ker by
        rw [ideleFractionalIdeal_ker_eq F]).mpr (ideleExpSection_finite_integral F t)
    change ClassGroup.mk F (ideleFractionalIdeal F u) = 1
    rw [h, map_one]
  refine ⟨⟨a * u, hNorm⟩, ?_⟩
  change ideleIdealClass F (a * u) = c
  rw [map_mul, huClass, mul_one, ha]

def integralUnitToField : (𝓞 F)ˣ →* Fˣ :=
  Units.map (algebraMap (𝓞 F) F)

theorem integralUnitToField_injective : Injective (integralUnitToField F) := by
  intro x y h
  apply Units.ext
  exact (IsFractionRing.injective (𝓞 F) F) (congrArg Units.val h)

/-- A principal idele has integral unit coordinates at every finite place
exactly when it comes from a global integral unit. -/
theorem principalIdele_integral_iff (t : Fˣ) :
    principalIdele F t ∈ (ideleDivisor F).ker ↔
      ∃ u : (𝓞 F)ˣ, integralUnitToField F u = t := by
  rw [ideleDivisor_ker_iff]
  constructor
  · rintro ⟨h, h'⟩
    obtain ⟨x, hx⟩ := (diagonal_finiteAdeles_integral_iff (t : F)).mp h
    have hinv : ∀ v : Place F, (algebraMap F (FinAdeles F) (↑t⁻¹ : F)) v ∈ v.adicCompletionIntegers F := by
      intro v
      change (principalIdele F t⁻¹).val.2 v ∈ v.adicCompletionIntegers F
      rw [map_inv]
      exact h' v
    obtain ⟨y, hy⟩ := (diagonal_finiteAdeles_integral_iff (↑t⁻¹ : F)).mp hinv
    have he : x * y = 1 := (IsFractionRing.injective (𝓞 F) F) (by rw [map_mul, hx, hy, map_one]; exact t.val_inv)
    exact ⟨⟨x, y, he, mul_comm x y ▸ he⟩, Units.ext hx⟩
  · rintro ⟨u, rfl⟩
    constructor
    · exact (diagonal_finiteAdeles_integral_iff _).mpr ⟨u.val, rfl⟩
    · intro v
      change ((principalIdele F (integralUnitToField F u))⁻¹).val.2 v ∈ v.adicCompletionIntegers F
      have h : (principalIdele F (integralUnitToField F u))⁻¹ =
          principalIdele F (integralUnitToField F u⁻¹) := by rw [map_inv, map_inv]
      rw [h]
      exact (diagonal_finiteAdeles_integral_iff _).mpr ⟨u.inv, rfl⟩ v

/-- The first arrow in (A.2.3.22), with the inverse in the second
component so that the multiplication map kills a diagonal unit. -/
def integralUnitDiagonal : (𝓞 F)ˣ →* Fˣ × (ideleDivisor F).ker where
  toFun u := (integralUnitToField F u, ⟨(principalIdele F (integralUnitToField F u))⁻¹, by
    apply Subgroup.inv_mem
    exact (principalIdele_integral_iff F _).mpr ⟨u, rfl⟩⟩)
  map_one' := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp
  map_mul' u v := by
    apply Prod.ext
    · exact map_mul (integralUnitToField F) u v
    · apply Subtype.ext
      change (principalIdele F (integralUnitToField F (u * v)))⁻¹ = _
      rw [map_mul, map_mul, mul_inv_rev, mul_comm]
      rfl

private theorem principal_class_trivial (t : Fˣ) : principalIdele F t ∈ (ideleIdealClass F).ker :=
  (ideleIdealClass_ker_iff F _).mpr ⟨t, 1, by simp⟩

private def integralIntoClassKer : (ideleDivisor F).ker →* (ideleIdealClass F).ker :=
  ((ideleDivisor F).ker.subtype).codRestrict (ideleIdealClass F).ker fun a =>
    (ideleIdealClass_ker_iff F a.val).mpr ⟨1, a, by simp⟩

private def principalIntoClassKer : Fˣ →* (ideleIdealClass F).ker :=
  (principalIdele F).codRestrict (ideleIdealClass F).ker (principal_class_trivial F)

/-- Multiplication of principal ideles and ideles integral at the finite
places, with the image equal to the kernel of the ideal-class map. -/
def principalIntegralMultiply : Fˣ × (ideleDivisor F).ker →* (ideleIdealClass F).ker :=
  (principalIntoClassKer F).coprod (integralIntoClassKer F)

theorem principalIntegral_exact :
    Injective (integralUnitDiagonal F) ∧ Surjective (principalIntegralMultiply F) ∧
    (principalIntegralMultiply F).ker = (integralUnitDiagonal F).range := by
  refine ⟨fun u v h => integralUnitToField_injective F (congrArg Prod.fst h), ?_, ?_⟩
  · intro a
    obtain ⟨t, b, hb⟩ := (ideleIdealClass_ker_iff F a.val).mp a.property
    exact ⟨(t, b), Subtype.ext hb.symm⟩
  · ext p
    rcases p with ⟨t, b⟩
    have hp : (t, b) ∈ (principalIntegralMultiply F).ker ↔
        principalIdele F t * b.val = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hp]
    change principalIdele F t * b.val = 1 ↔ ∃ u, integralUnitDiagonal F u = (t, b)
    constructor
    · intro h
      have hb : (principalIdele F t)⁻¹ = b.val := inv_eq_of_mul_eq_one_right h
      have hbi : (principalIdele F t)⁻¹ ∈ (ideleDivisor F).ker := by
        rw [hb]
        exact b.property
      have ht : principalIdele F t ∈ (ideleDivisor F).ker := by
        simpa only [inv_inv] using (ideleDivisor F).ker.inv_mem hbi
      obtain ⟨u, hu⟩ := (principalIdele_integral_iff F t).mp ht
      refine ⟨u, Prod.ext hu (Subtype.ext ?_)⟩
      change (principalIdele F (integralUnitToField F u))⁻¹ = b.val
      rwa [hu]
    · rintro ⟨u, hu⟩
      have h₁ := congrArg Prod.fst hu
      have h₂ := congrArg (fun p : Fˣ × (ideleDivisor F).ker => p.2.val) hu
      change integralUnitToField F u = t at h₁
      change (principalIdele F (integralUnitToField F u))⁻¹ = b.val at h₂
      rw [h₁] at h₂
      rw [← h₂, mul_inv_cancel]

private theorem integralIntoClassKer_openEmbedding :
    IsOpenEmbedding (integralIntoClassKer F) := by
  let H := (ideleDivisor F).ker
  let K := (ideleIdealClass F).ker
  have he : range (integralIntoClassKer F) =
      (Subtype.val : K → Idele F) ⁻¹' (H : Set (Idele F)) := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
  have h₀ : IsEmbedding (Subtype.val : H → Idele F) := IsEmbedding.subtypeVal
  have h₁ : IsEmbedding (Subtype.val : K → Idele F) := IsEmbedding.subtypeVal
  have hc : IsEmbedding ((Subtype.val : K → Idele F) ∘ integralIntoClassKer F) := h₀
  exact ⟨h₁.of_comp_iff.mp hc, he ▸ (ideleDivisor_ker_open F).preimage continuous_subtype_val⟩

/-- The first sequence has a topological embedding on the left and a
continuous open quotient on the right. Arithmetic unit groups carry the
discrete topology in this sequence. -/
theorem principalIntegral_strict
    [TopologicalSpace Fˣ] [DiscreteTopology Fˣ]
    [TopologicalSpace (𝓞 F)ˣ] [DiscreteTopology (𝓞 F)ˣ] :
    IsEmbedding (integralUnitDiagonal F) ∧
      IsOpenMap (principalIntegralMultiply F) ∧ Continuous (principalIntegralMultiply F) := by
  have hi : IsOpenEmbedding (integralUnitToField F) :=
    isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
      ⟨continuous_of_discreteTopology, integralUnitToField_injective F,
        fun s _ => isOpen_discrete _⟩
  refine ⟨IsEmbedding.of_comp continuous_of_discreteTopology continuous_fst hi.isEmbedding, ?_, ?_⟩
  · intro U hU
    let W (t : Fˣ) := (fun b : (ideleDivisor F).ker => (t, b)) ⁻¹' U
    have hEq : principalIntegralMultiply F '' U =
      ⋃ t : Fˣ, (Homeomorph.mulLeft (principalIntoClassKer F t)) ''
        (integralIntoClassKer F '' W t) := by
      ext c
      constructor
      · rintro ⟨⟨t, b⟩, hb, rfl⟩
        exact mem_iUnion.mpr ⟨t, ⟨integralIntoClassKer F b, ⟨b, hb, rfl⟩, rfl⟩⟩
      · intro h
        obtain ⟨t, b, ⟨a, ha, rfl⟩, rfl⟩ := mem_iUnion.mp h
        exact ⟨(t, a), ha, rfl⟩
    rw [hEq]
    exact isOpen_iUnion fun t => (Homeomorph.mulLeft (principalIntoClassKer F t)).isOpenMap _
      ((integralIntoClassKer_openEmbedding F).isOpenMap _
        (hU.preimage (continuous_const.prodMk continuous_id)))
  · exact ((continuous_of_discreteTopology (f := principalIntoClassKer F)).comp continuous_fst).mul
      ((integralIntoClassKer_openEmbedding F).continuous.comp continuous_snd)

theorem ideleNorm_eq_arch_of_finite_integral (a : Idele F) (ha : a ∈ (ideleDivisor F).ker) :
    ideleNorm F a = ‖a.val.1‖ := by
  have h₀ := ((ideleDivisor_ker_iff F a).mp ha).1
  have h₁ := ((ideleDivisor_ker_iff F a).mp ha).2
  have hval (v : Place F) : Valued.v (a.val.2 v) = 1 := by
    have hr := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h₀ v)
    have hi := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp (h₁ v)
    have he := congrArg (fun x : Adeles F => x.2 v) a.val_inv
    change a.val.2 v * a.inv.2 v = 1 at he
    have hm : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by rw [← map_mul, he, map_one]
    exact le_antisymm hr (hm.symm.trans_le (mul_le_of_le_one_right zero_le hi))
  have hn (v : Place F) : ‖a.val.2 v‖ = 1 := by
    rw [FinitePlace.norm_def, hval v]
    simp
  change ‖a.val.1‖ * (∏ᶠ v : Place F, ‖a.val.2 v‖) = ‖a.val.1‖
  simp [hn]

/-- The kernel on norm-one ideles is generated by principal ideles and
the product of norm-one Archimedean ideles with finite integral units. -/
theorem ideleNormOne_idealClass_ker_iff (a : (ideleNorm F).ker) :
    ((ideleIdealClass F).comp (ideleNorm F).ker.subtype) a = 1 ↔
      ∃ (t : Fˣ) (b : (ideleDivisor F).ker), ‖b.val.val.1‖ = 1 ∧
        a.val = principalIdele F t * b.val := by
  change a.val ∈ (ideleIdealClass F).ker ↔ _
  rw [ideleIdealClass_ker_iff F a.val]
  constructor
  · rintro ⟨t, b, h⟩
    have hn : ideleNorm F a.val = 1 := a.property
    rw [h, map_mul, ideleNorm_principal, one_mul, ideleNorm_eq_arch_of_finite_integral F _ b.property] at hn
    exact ⟨t, b, hn, h⟩
  · rintro ⟨t, b, _, h⟩
    exact ⟨t, b, h⟩

/-- Proposition A.2.3.9. The two class-group maps are continuous open
surjections with the indicated kernels. The ideal-class group is finite. -/
theorem ideleIdealClass_exact
    [TopologicalSpace (ClassGroup (𝓞 F))] [DiscreteTopology (ClassGroup (𝓞 F))] :
    Surjective (ideleIdealClass F) ∧ Continuous (ideleIdealClass F) ∧ IsOpenMap (ideleIdealClass F) ∧
      Surjective ((ideleIdealClass F).comp (ideleNorm F).ker.subtype) ∧
      Continuous ((ideleIdealClass F).comp (ideleNorm F).ker.subtype) ∧
      IsOpenMap ((ideleIdealClass F).comp (ideleNorm F).ker.subtype) ∧ Finite (ClassGroup (𝓞 F)) := by
  exact ⟨ideleIdealClass_surjective F, ideleIdealClass_continuous F, fun U _ => isOpen_discrete _,
    ideleNormOne_idealClass_surjective F, (ideleIdealClass_continuous F).comp continuous_subtype_val,
    fun U _ => isOpen_discrete _, inferInstance⟩

/-- All arrows in the first exact sequence use the indicated intrinsic
group topologies. The injection has closed image and the surjection is a
quotient map. -/
theorem principalIntegral_strict_exact
    [TopologicalSpace Fˣ] [DiscreteTopology Fˣ]
    [TopologicalSpace (𝓞 F)ˣ] [DiscreteTopology (𝓞 F)ˣ] :
    IsClosedEmbedding (integralUnitDiagonal F) ∧
      IsQuotientMap (principalIntegralMultiply F) ∧
      (principalIntegralMultiply F).ker = (integralUnitDiagonal F).range := by
  obtain ⟨he, ho, hc⟩ := principalIntegral_strict F
  obtain ⟨_, hsurj, hker⟩ := principalIntegral_exact F
  letI : T2Space (Idele F) := ideles_hausdorff
  have hcl : IsClosed ((principalIntegralMultiply F).ker : Set (Fˣ × (ideleDivisor F).ker)) :=
    isClosed_eq hc continuous_const
  refine ⟨⟨he, ?_⟩, ho.isQuotientMap hc hsurj, hker⟩
  change IsClosed ((integralUnitDiagonal F).range : Set (Fˣ × (ideleDivisor F).ker))
  rwa [← hker]


/-- The integral block is the product of the full Archimedean unit
group and the units of the finite integral block. -/
theorem ideleDivisor_ker_iff_prodUnits (a : Idele F) :
    a ∈ (ideleDivisor F).ker ↔
      (Homeomorph.prodUnits a).2 ∈ (finiteIntegralSubmonoid F).units := by
  rw [ideleDivisor_ker_iff]
  change ((∀ v : Place F, a.val.2 v ∈ v.adicCompletionIntegers F) ∧
      (∀ v : Place F, a.inv.2 v ∈ v.adicCompletionIntegers F)) ↔
    ((∀ v : Place F, v ∉ (∅ : Finset (Place F)) → a.val.2 v ∈ v.adicCompletionIntegers F) ∧
      (∀ v : Place F, v ∉ (∅ : Finset (Place F)) → a.inv.2 v ∈ v.adicCompletionIntegers F))
  simp

/-- The integral-block identification respects the idelic topology. -/
def ideleDivisorKernelHomeomorph :
    (ideleDivisor F).ker ≃ₜ
      (InfiniteAdeleRing F)ˣ × (finiteIntegralSubmonoid F).units where
  toFun a := ((Homeomorph.prodUnits a.val).1,
    ⟨(Homeomorph.prodUnits a.val).2, (ideleDivisor_ker_iff_prodUnits F a.val).mp a.property⟩)
  invFun p := ⟨Homeomorph.prodUnits.symm (p.1, p.2.val),
    (ideleDivisor_ker_iff_prodUnits F _).mpr (by
      rw [Homeomorph.apply_symm_apply]
      exact p.2.property)⟩
  left_inv a := Subtype.ext (Homeomorph.prodUnits.symm_apply_apply a.val)
  right_inv p := by
    have h := (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FinAdeles F)).apply_symm_apply
      (p.1, p.2.val)
    apply Prod.ext
    · change (Homeomorph.prodUnits (Homeomorph.prodUnits.symm (p.1, p.2.val))).1 = p.1
      exact congrArg Prod.fst h
    · apply Subtype.ext
      change (Homeomorph.prodUnits (Homeomorph.prodUnits.symm (p.1, p.2.val))).2 = p.2.val
      exact congrArg Prod.snd h
  continuous_toFun := by
    have h : Continuous (fun a : (ideleDivisor F).ker =>
        (Homeomorph.prodUnits (α := InfiniteAdeleRing F) (β := FinAdeles F)) a.val) :=
      Homeomorph.prodUnits.continuous.comp continuous_subtype_val
    exact h.fst.prodMk (h.snd.subtype_mk _)
  continuous_invFun :=
    (Homeomorph.prodUnits.symm.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _


/-- The groups appearing as subgroups in A.2.3.9 have their locally
compact Hausdorff subgroup topologies. -/
theorem ideleIdealClass_subgroups_locallyCompactHausdorff
    [TopologicalSpace (ClassGroup (𝓞 F))] [DiscreteTopology (ClassGroup (𝓞 F))] :
    LocallyCompactSpace (ideleDivisor F).ker ∧ T2Space (ideleDivisor F).ker ∧
    LocallyCompactSpace (ideleIdealClass F).ker ∧ T2Space (ideleIdealClass F).ker ∧
    LocallyCompactSpace (ideleNorm F).ker ∧ T2Space (ideleNorm F).ker ∧
    LocallyCompactSpace ((ideleIdealClass F).comp (ideleNorm F).ker.subtype).ker ∧
      T2Space ((ideleIdealClass F).comp (ideleNorm F).ker.subtype).ker := by
  letI : LocallyCompactSpace (Idele F) := ideles_locallyCompact
  letI : T2Space (Idele F) := ideles_hausdorff
  have hclass : IsClosed ((ideleIdealClass F).ker : Set (Idele F)) :=
    isClosed_eq (ideleIdealClass_continuous F) continuous_const
  have hnorm : IsClosed ((ideleNorm F).ker : Set (Idele F)) :=
    isClosed_eq (ideleNorm_continuous F) continuous_const
  letI : LocallyCompactSpace (ideleNorm F).ker := hnorm.locallyCompactSpace
  have hclassNorm : IsClosed
      (((ideleIdealClass F).comp (ideleNorm F).ker.subtype).ker : Set (ideleNorm F).ker) :=
    hclass.preimage continuous_subtype_val
  exact ⟨(ideleDivisor_ker_open F).locallyCompactSpace, inferInstance,
    hclass.locallyCompactSpace, inferInstance, inferInstance, inferInstance,
    hclassNorm.locallyCompactSpace, inferInstance⟩

end

end Masullo
