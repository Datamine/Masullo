import FinitePrincipalValue
import CompactCharacterCompleteness
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

open Filter Function MeasureTheory Set Topology
open scoped NumberField BigOperators NNReal ENNReal

namespace Masullo

noncomputable section

section FiniteOrbit

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup E] [Module ℂ E]
  (ρ : G →* (E →ₗ[ℂ] E)) (ν : Measure G) [IsFiniteMeasure ν]

omit [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem orbitScalar_continuous (f : E) (h : IsLocallyConstant fun a => ρ a f)
    (ℓ : E →ₗ[ℂ] ℂ) : Continuous (fun a => ℓ (ρ a f)) :=
  (h.comp ℓ).continuous

/-- Integrate each vector in a finite compact orbit with the weight of its fiber. -/
private def orbitAverage (w : G → ℂ) (f : E) (h : IsLocallyConstant fun a => ρ a f) : E :=
  ∑ x ∈ h.range_finite.toFinset, (∫ a in (fun a => ρ a f) ⁻¹' {x}, w a ∂ν) • x

omit [IsTopologicalGroup G] [T2Space G] in
private theorem orbitAverage_apply (w : G → ℂ) (hw : Continuous w) (f : E)
    (h : IsLocallyConstant fun a => ρ a f) (ℓ : E →ₗ[ℂ] ℂ) :
    ℓ (orbitAverage ρ ν w f h) = ∫ a, w a * ℓ (ρ a f) ∂ν := by
  classical
  let s := h.range_finite.toFinset
  let fiber (x : E) := (fun a => ρ a f) ⁻¹' {x}
  have hm (x : E) : MeasurableSet (fiber x) := (h.isOpen_fiber x).measurableSet
  have hi : Integrable w ν := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : (fun a => w a * ℓ (ρ a f)) =
      fun a => ∑ x ∈ s, (fiber x).indicator (fun a => w a * ℓ x) a := by
    funext a
    symm
    refine (Finset.sum_eq_single_of_mem (ρ a f)
      (h.range_finite.mem_toFinset.mpr (mem_range_self a)) ?_).trans ?_
    · intro x _ hx
      exact indicator_of_notMem (show a ∉ fiber x from fun hx' => hx hx'.symm) _
    · exact indicator_of_mem (show a ∈ fiber (ρ a f) from rfl) _
  rw [hsum, integral_finsetSum s (fun x _ => (hi.mul_const _).indicator (hm x))]
  simp only [orbitAverage, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_indicator (hm x), integral_mul_const]

private theorem orbitDual_ext {f g : E} (h : ∀ ℓ : E →ₗ[ℂ] ℂ, ℓ f = ℓ g) : f = g := by
  by_contra hne
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hne)
  exact hℓ (by rw [map_sub, h ℓ, sub_self])

private def orbitCharacterWeight (χ : PontryaginDual G) (a : G) : ℂ := ↑((χ a)⁻¹)

omit [IsTopologicalGroup G] [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem continuous_orbitCharacterWeight (χ : PontryaginDual G) :
    Continuous (orbitCharacterWeight χ) :=
  continuous_subtype_val.comp χ.continuous.inv

private def orbitIsotype (χ : PontryaginDual G) : Submodule ℂ E where
  carrier := {f | ∀ g, ρ g f = (χ g : ℂ) • f}
  zero_mem' := fun g => by simp
  add_mem' hf hg g := by simp only [map_add, hf g, hg g, smul_add]
  smul_mem' c f hf g := by rw [map_smul, hf g, smul_comm]

omit [T2Space G] in
private theorem orbitAverage_mem_isotype [ν.IsMulLeftInvariant] (χ : PontryaginDual G)
    (f : E) (h : IsLocallyConstant fun a => ρ a f) :
    orbitAverage ρ ν (orbitCharacterWeight χ) f h ∈ orbitIsotype ρ χ := by
  intro g
  apply orbitDual_ext
  intro ℓ
  rw [map_smul, orbitAverage_apply _ _ _ (continuous_orbitCharacterWeight χ) _ _ ℓ]
  change (ℓ.comp (ρ g)) (orbitAverage ρ ν (orbitCharacterWeight χ) f h) = _
  rw [orbitAverage_apply _ _ _ (continuous_orbitCharacterWeight χ)]
  have hm (a b : G) : ρ a (ρ b f) = ρ (a * b) f := by rw [map_mul]; rfl
  simp only [LinearMap.comp_apply, hm, smul_eq_mul]
  rw [← integral_const_mul]
  conv_rhs => rw [← integral_mul_left_eq_self _ g]
  apply integral_congr_ae
  filter_upwards with a
  have hc : (χ g : ℂ) * orbitCharacterWeight χ (g * a) = orbitCharacterWeight χ a := by
    simp only [orbitCharacterWeight, map_mul, mul_inv_rev, Circle.coe_mul]
    rw [mul_left_comm]
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, mul_one]
  rw [← mul_assoc, hc]

private theorem iSup_orbitIsotype_eq_top [ν.IsHaarMeasure] [ν.WeaklyRegular]
    (h : ∀ f : E, IsLocallyConstant fun a => ρ a f) :
    (⨆ χ : PontryaginDual G, orbitIsotype ρ χ) = ⊤ := by
  let P := ⨆ χ : PontryaginDual G, orbitIsotype ρ χ
  apply top_unique
  intro f _
  by_contra hf
  obtain ⟨ℓ, hne, hℓ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (p := P) hf inferInstance
  have hcont := orbitScalar_continuous ρ f (h f) ℓ
  have hzero (χ : PontryaginDual G) : ∫ a, star (χ a : ℂ) * ℓ (ρ a f) ∂ν = 0 := by
    have he : (fun a => star (χ a : ℂ) * ℓ (ρ a f)) =
        fun a => orbitCharacterWeight χ a * ℓ (ρ a f) :=
      funext fun a => congrArg (· * ℓ (ρ a f)) (Circle.coe_inv_eq_conj (χ a)).symm
    rw [he, ← orbitAverage_apply _ _ _ (continuous_orbitCharacterWeight χ) _ (h f)]
    have hm := Submodule.mem_map_of_mem (f := ℓ)
      (le_iSup (orbitIsotype ρ) χ (orbitAverage_mem_isotype ρ ν χ f (h f)))
    rwa [hℓ, Submodule.mem_bot] at hm
  have hae := ae_eq_zero_of_character_integral_eq_zero ν (hcont.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) hzero
  have heq := (hcont.ae_eq_iff_eq ν continuous_const).mp hae
  have hone : ℓ (ρ 1 f) = (0 : ℂ) := congrFun heq 1
  rw [map_one] at hone
  exact hne hone

omit [IsTopologicalGroup G] [T2Space G] in
private theorem orbitAverage_one_apply (f : E) (h : IsLocallyConstant fun a => ρ a f)
    (ℓ : E →ₗ[ℂ] ℂ) :
    ℓ (orbitAverage ρ ν 1 f h) = ∫ a, ℓ (ρ a f) ∂ν := by
  simpa only [Pi.one_apply, one_mul] using
    orbitAverage_apply ρ ν 1 (show Continuous (1 : G → ℂ) from continuous_const) f h ℓ

/-- Average a locally constant orbit under a finite measure on a compact group. -/
def fixedOrbitAverage (h : ∀ f : E, IsLocallyConstant fun a => ρ a f) : E →ₗ[ℂ] E where
  toFun f := orbitAverage ρ ν 1 f (h f)
  map_add' f g := by
    apply orbitDual_ext
    intro ℓ
    rw [map_add]
    simp only [orbitAverage_one_apply, map_add]
    exact integral_add
      ((orbitScalar_continuous ρ f (h f) _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((orbitScalar_continuous ρ g (h g) _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  map_smul' c f := by
    apply orbitDual_ext
    intro ℓ
    rw [RingHom.id_apply, map_smul]
    simp only [orbitAverage_one_apply, map_smul, integral_smul]

omit [IsTopologicalGroup G] [T2Space G] in
theorem fixedOrbitAverage_apply (h : ∀ f : E, IsLocallyConstant fun a => ρ a f)
    (f : E) (ℓ : E →ₗ[ℂ] ℂ) :
    ℓ (fixedOrbitAverage ρ ν h f) = ∫ a, ℓ (ρ a f) ∂ν := by
  exact orbitAverage_one_apply ρ ν f (h f) ℓ

omit [IsTopologicalGroup G] [T2Space G] in
/-- Scaling a finite averaging measure scales the averaged test. -/
theorem fixedOrbitAverage_smul_measure (r : ℝ≥0)
    (h : ∀ f : E, IsLocallyConstant fun a => ρ a f) (f : E) :
    letI : IsFiniteMeasure ((r : ℝ≥0∞) • ν) := ν.smul_finite ENNReal.coe_ne_top
    fixedOrbitAverage ρ ((r : ℝ≥0∞) • ν) h f =
      ((r : ℝ) : ℂ) • fixedOrbitAverage ρ ν h f := by
  letI : IsFiniteMeasure ((r : ℝ≥0∞) • ν) := ν.smul_finite ENNReal.coe_ne_top
  apply orbitDual_ext
  intro l
  rw [map_smul, fixedOrbitAverage_apply, fixedOrbitAverage_apply, integral_smul_measure]
  rfl

omit [T2Space G] in
theorem fixedOrbitAverage_fixed [ν.IsMulLeftInvariant]
    (h : ∀ f : E, IsLocallyConstant fun a => ρ a f) (f : E) :
    ∀ a, ρ a (fixedOrbitAverage ρ ν h f) = fixedOrbitAverage ρ ν h f := by
  have hx := orbitAverage_mem_isotype ρ ν 1 f (h f)
  intro a
  have h₁ : orbitCharacterWeight (1 : PontryaginDual G) = 1 := by
    funext a
    simp [orbitCharacterWeight]
  change ρ a (orbitAverage ρ ν 1 f (h f)) = orbitAverage ρ ν 1 f (h f)
  simpa only [h₁, PontryaginDual.one_apply, Circle.coe_one, one_smul] using hx a

omit [IsTopologicalGroup G] [T2Space G] in
theorem fixedOrbitAverage_of_fixed (h : ∀ f : E, IsLocallyConstant fun a => ρ a f)
    (hν : ν univ = 1) (f : E) (hf : ∀ a, ρ a f = f) : fixedOrbitAverage ρ ν h f = f := by
  apply orbitDual_ext
  intro ℓ
  rw [fixedOrbitAverage_apply]
  simp only [hf, integral_const, measureReal_def, hν, ENNReal.toReal_one, one_smul]

omit [T2Space G] in
private theorem fixedOrbitAverage_of_nontrivial [ν.IsMulLeftInvariant]
    (h : ∀ f : E, IsLocallyConstant fun a => ρ a f) (χ : PontryaginDual G) (hχ : χ ≠ 1)
    (f : E) (hf : f ∈ orbitIsotype ρ χ) : fixedOrbitAverage ρ ν h f = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, χ a ≠ 1 := by
    by_contra! he
    exact hχ (ContinuousMonoidHom.ext he)
  apply orbitDual_ext
  intro ℓ
  rw [fixedOrbitAverage_apply, map_zero]
  let F (g : G) := ℓ (ρ g f)
  have he (g : G) : F (a * g) = (χ a : ℂ) * F g := by
    change ℓ (ρ (a * g) f) = _
    rw [mul_comm a g, map_mul]
    change ℓ (ρ g (ρ a f)) = _
    rw [hf a, map_smul, map_smul, smul_eq_mul]
  have hInt := integral_mul_left_eq_self (μ := ν) F a
  simp_rw [he] at hInt
  rw [integral_const_mul] at hInt
  by_contra hn
  exact ha (Circle.coe_injective (by
    apply mul_right_cancel₀ hn
    simpa only [one_mul, Circle.coe_one] using hInt))

/-- The algebraic coinvariant relations for an action on tests. -/
def orbitDifferenceSpan : Submodule ℂ E :=
  Submodule.span ℂ {x | ∃ (g : G) (f : E), f - ρ g f = x}

omit [IsTopologicalGroup G] [T2Space G] in
/-- Averaging a finite orbit preserves its class in algebraic coinvariants. -/
theorem fixedOrbitAverage_mkQ
    (h : ∀ f : E, IsLocallyConstant fun a => ρ a f)
    (hν : ν univ = 1) (f : E) :
    (orbitDifferenceSpan ρ).mkQ (fixedOrbitAverage ρ ν h f) =
      (orbitDifferenceSpan ρ).mkQ f := by
  let N := orbitDifferenceSpan ρ
  apply orbitDual_ext
  intro l
  change (l.comp N.mkQ) (fixedOrbitAverage ρ ν h f) = l (N.mkQ f)
  rw [fixedOrbitAverage_apply]
  have he (g : G) : N.mkQ (ρ g f) = N.mkQ f := by
    apply (sub_eq_zero.mp ?_).symm
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨g, f, rfl⟩)
  simp only [LinearMap.comp_apply, he, integral_const, measureReal_def, hν, ENNReal.toReal_one,
    one_smul]

omit [T2Space G] in
/-- The averaging kernel consists exactly of the algebraic coinvariant relations. -/
theorem fixedOrbitAverage_ker [ν.IsMulLeftInvariant]
    (h : ∀ f : E, IsLocallyConstant fun a => ρ a f)
    (hν : ν univ = 1) : (fixedOrbitAverage ρ ν h).ker = orbitDifferenceSpan ρ := by
  apply le_antisymm
  · intro f hf
    have he := fixedOrbitAverage_mkQ ρ ν h hν f
    change fixedOrbitAverage ρ ν h f = 0 at hf
    rw [hf, map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero _).mp he.symm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, f, rfl⟩
    change fixedOrbitAverage ρ ν h (f - ρ g f) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply orbitDual_ext
    intro l
    rw [fixedOrbitAverage_apply, fixedOrbitAverage_apply]
    let a (x : G) := l (ρ x f)
    have he (x : G) : l (ρ x (ρ g f)) = a (g * x) := by
      rw [mul_comm g x]
      change l (ρ x (ρ g f)) = l (ρ (x * g) f)
      rw [map_mul]
      rfl
    simp_rw [he]
    exact (integral_mul_left_eq_self a g).symm

end FiniteOrbit

section FiniteCompletion

open IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private abbrev K := v.adicCompletion F
private abbrev Test := locallyConstantTests (K F v)

/-- The compact group of integral units, in multiplicative local coordinates. -/
def principalIntegralUnits : Subgroup (K F v)ˣ where
  carrier := {g | ‖g.val‖ = 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change ‖a.val‖ = 1 at ha
    change ‖b.val‖ = 1 at hb
    change ‖(a * b).val‖ = 1
    rw [Units.val_mul, norm_mul, ha, hb, one_mul]
  inv_mem' {a} ha := by
    change ‖a.val‖ = 1 at ha
    change ‖a⁻¹.val‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, ha, inv_one]

private abbrev U := ↥(principalIntegralUnits F v)

theorem principalIntegralUnits_compactSpace : CompactSpace (U F v) := by
  apply isCompact_iff_compactSpace.mp
  have he : (principalIntegralUnits F v : Set (K F v)ˣ) =
      ((v.adicCompletionIntegers F).toSubmonoid.units : Set (K F v)ˣ) := by
    ext u
    exact (finiteCompletion_norm_eq_one_iff F v u).trans
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).symm
  rw [he]
  exact Submonoid.units_isCompact (finitePlaceIntegral_compact F v)

private instance : CompactSpace (U F v) := principalIntegralUnits_compactSpace F v

private instance : MeasurableSpace (U F v) := borel _
private instance : BorelSpace (U F v) := ⟨rfl⟩

def principalUnitHaar : Measure (U F v) := Measure.haarMeasure ⊤
instance : (principalUnitHaar F v).IsHaarMeasure := by
  unfold principalUnitHaar
  infer_instance
private instance : (principalUnitHaar F v).WeaklyRegular := by
  unfold principalUnitHaar
  infer_instance

theorem principalUnitHaar_univ : principalUnitHaar F v univ = 1 :=
  Measure.haarMeasure_self (K₀ := ⊤)

/-- The action by pullback along inverse multiplication by an integral unit. -/
def principalUnitAction : U F v →* (Test F v →ₗ[ℂ] Test F v) where
  toFun u := locallyConstantTestTranslate (K F v) (u : (K F v)ˣ)
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    change f.val ((1 : (K F v)ˣ)⁻¹ • x) = f.val x
    simp)
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    change f.val (((a.val * b.val)⁻¹ : (K F v)ˣ) • x) =
      f.val (b.val⁻¹ • a.val⁻¹ • x)
    rw [mul_inv_rev, mul_smul])

theorem principalUnitAction_orbit (f : Test F v) :
    IsLocallyConstant fun a => principalUnitAction F v a f :=
  (locallyConstantTestTranslate_orbit_locallyConstant (K F v) f).comp_continuous continuous_subtype_val

/-- The integral-unit character isotype of the local Schwartz–Bruhat space. -/
def principalUnitIsotype (χ : PontryaginDual (U F v)) : Submodule ℂ (Test F v) :=
  orbitIsotype (principalUnitAction F v) χ

def principalUnitAverage : Test F v →ₗ[ℂ] Test F v :=
  fixedOrbitAverage (principalUnitAction F v) (principalUnitHaar F v)
    (principalUnitAction_orbit F v)

theorem principalUnitAverage_apply (f : Test F v) (ℓ : Test F v →ₗ[ℂ] ℂ) :
    ℓ (principalUnitAverage F v f) =
      ∫ u, ℓ (principalUnitAction F v u f) ∂principalUnitHaar F v :=
  fixedOrbitAverage_apply _ _ _ _ _

private theorem principalUnitAverage_fixed (f : Test F v) :
    principalUnitAverage F v f ∈ principalUnitIsotype F v 1 := by
  intro a
  rw [PontryaginDual.one_apply, Circle.coe_one, one_smul]
  exact fixedOrbitAverage_fixed _ _ _ _ a

private theorem principalUnitAverage_of_fixed (f : Test F v)
    (hf : f ∈ principalUnitIsotype F v 1) : principalUnitAverage F v f = f :=
  fixedOrbitAverage_of_fixed _ _ _ (principalUnitHaar_univ F v) f (by
    intro a
    simpa only [PontryaginDual.one_apply, Circle.coe_one, one_smul] using hf a)

private theorem principalUnitAverage_of_nontrivial (χ : PontryaginDual (U F v)) (hχ : χ ≠ 1)
    (f : Test F v) (hf : f ∈ principalUnitIsotype F v χ) :
    principalUnitAverage F v f = 0 :=
  fixedOrbitAverage_of_nontrivial _ _ _ χ hχ f hf

/-- Compact unit orbits lie in the algebraic span of their character isotypes. -/
theorem principalUnitIsotype_span :
    (⨆ χ : PontryaginDual (U F v), principalUnitIsotype F v χ) = ⊤ :=
  iSup_orbitIsotype_eq_top (principalUnitAction F v) (principalUnitHaar F v)
    (principalUnitAction_orbit F v)

private theorem principalUnitIsotype_one_iff_radial (f : Test F v) :
    f ∈ principalUnitIsotype F v 1 ↔
      ∀ x y : K F v, ‖x‖ = ‖y‖ → f.val x = f.val y := by
  rw [locallyConstantTests_radial_iff]
  constructor
  · intro hf u hu x
    let a : U F v := ⟨u, hu⟩
    have h := hf a⁻¹
    rw [PontryaginDual.one_apply, Circle.coe_one, one_smul] at h
    have hx := congrArg (fun g : Test F v => g.val x) h
    change f.val ((u⁻¹)⁻¹ • x) = f.val x at hx
    rwa [inv_inv] at hx
  · intro hf a
    rw [show (1 : PontryaginDual (U F v)) a = 1 from rfl, Circle.coe_one, one_smul]
    apply Subtype.ext
    funext x
    change f.val (a.val⁻¹.val * x) = f.val x
    exact hf a.val⁻¹ (a⁻¹).property x

/-- Averaging over integral units produces a test constant on each norm shell. -/
theorem principalUnitAverage_radial (f : Test F v) :
    ∀ x y : K F v, ‖x‖ = ‖y‖ → (principalUnitAverage F v f).val x = (principalUnitAverage F v f).val y :=
  (principalUnitIsotype_one_iff_radial F v _).mp (principalUnitAverage_fixed F v f)

private theorem principalUnitAverage_eval_zero (f : Test F v) :
    (principalUnitAverage F v f).val 0 = f.val 0 := by
  let ev : Test F v →ₗ[ℂ] ℂ :=
    { toFun := fun g => g.val 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  change ev (principalUnitAverage F v f) = ev f
  rw [principalUnitAverage_apply]
  have he (a : U F v) : ev (principalUnitAction F v a f) = f.val 0 := by
    change f.val (a.val⁻¹.val * 0) = _
    rw [mul_zero]
  simp only [he, integral_const, measureReal_def, principalUnitHaar_univ,
    ENNReal.toReal_one, one_smul]
  rfl

private def weilPrincipalValueFor (π : (K F v)ˣ) : Test F v →ₗ[ℂ] Test F v :=
  LinearMap.id - (locallyConstantTestTranslate (K F v) π).comp (principalUnitAverage F v)

/-- Weil's local operator from Definition 5.3.1.2, using the normalized
unit projection. Only the trivial isotype is acted on by the dilation difference. -/
def weilPrincipalValue : Test F v →ₗ[ℂ] Test F v :=
  weilPrincipalValueFor F v (chosenFiniteUniformizer F v)

private theorem weilPrincipalValueFor_of_fixed (π : (K F v)ˣ) (f : Test F v)
    (hf : f ∈ principalUnitIsotype F v 1) :
    weilPrincipalValueFor F v π f = finitePrincipalValue π f := by
  change f - locallyConstantTestTranslate _ π (principalUnitAverage F v f) =
    f - locallyConstantTestTranslate _ π f
  rw [principalUnitAverage_of_fixed F v f hf]

private theorem weilPrincipalValueFor_of_nontrivial (π : (K F v)ˣ) (χ : PontryaginDual (U F v))
    (hχ : χ ≠ 1) (f : Test F v) (hf : f ∈ principalUnitIsotype F v χ) :
    weilPrincipalValueFor F v π f = f := by
  change f - locallyConstantTestTranslate _ π (principalUnitAverage F v f) = f
  rw [principalUnitAverage_of_nontrivial F v χ hχ f hf, map_zero, sub_zero]

private theorem weilPrincipalValueFor_fixed (π : (K F v)ˣ) (f : Test F v)
    (hf : f ∈ principalUnitIsotype F v 1) :
    weilPrincipalValueFor F v π f ∈ principalUnitIsotype F v 1 := by
  rw [weilPrincipalValueFor_of_fixed F v π f hf, principalUnitIsotype_one_iff_radial]
  exact finitePrincipalValue_radial π f ((principalUnitIsotype_one_iff_radial F v f).mp hf)

private theorem weilPrincipalValueFor_injective (π : (K F v)ˣ) (hπ : ‖π.val‖ < 1) :
    Injective (weilPrincipalValueFor F v π) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hp := LinearMap.mem_ker.mp hf
  change f - locallyConstantTestTranslate _ π (principalUnitAverage F v f) = 0 at hp
  have hRad := (principalUnitIsotype_one_iff_radial F v (principalUnitAverage F v f)).mp
    (principalUnitAverage_fixed F v f)
  have hfRad : f ∈ principalUnitIsotype F v 1 := by
    rw [principalUnitIsotype_one_iff_radial]
    intro x y hxy
    rw [sub_eq_zero.mp hp]
    apply hRad
    change ‖π⁻¹.val * x‖ = ‖π⁻¹.val * y‖
    rw [norm_mul, norm_mul, hxy]
  have hz : finitePrincipalValue π f = 0 :=
    (weilPrincipalValueFor_of_fixed F v π f hfRad).symm.trans (LinearMap.mem_ker.mp hf)
  exact finitePrincipalValue_injective π hπ (hz.trans (map_zero _).symm)

/-- The operator agrees with the radial difference for every choice of
uniformizer on the trivial unit isotype, and fixes every other isotype. -/
theorem weilPrincipalValue_characterization (π : (K F v)ˣ) (hπ : Valued.v.IsUniformizer π.val) :
    (∀ f ∈ principalUnitIsotype F v 1, weilPrincipalValue F v f = finitePrincipalValue π f) ∧
    (∀ χ : PontryaginDual (U F v), χ ≠ 1 →
      ∀ f ∈ principalUnitIsotype F v χ, weilPrincipalValue F v f = f) := by
  constructor
  · intro f hf
    rw [weilPrincipalValue, weilPrincipalValueFor_of_fixed F v _ f hf]
    exact (finiteCompletion_principalValue F v _ π (chosenFiniteUniformizer_spec F v) hπ).2.1 f
      ((principalUnitIsotype_one_iff_radial F v f).mp hf)
  · exact fun χ hχ f hf => weilPrincipalValueFor_of_nontrivial F v _ χ hχ f hf

/-- The stated isotype actions determine the operator on the whole test space. -/
theorem weilPrincipalValue_unique (L : Test F v →ₗ[ℂ] Test F v)
    (h₁ : ∀ f ∈ principalUnitIsotype F v 1,
      L f = finitePrincipalValue (chosenFiniteUniformizer F v) f)
    (hχ : ∀ χ : PontryaginDual (U F v), χ ≠ 1 → ∀ f ∈ principalUnitIsotype F v χ, L f = f) :
    L = weilPrincipalValue F v := by
  have h := weilPrincipalValue_characterization F v _ (chosenFiniteUniformizer_spec F v)
  have hker : (⨆ χ : PontryaginDual (U F v), principalUnitIsotype F v χ) ≤
      (L - weilPrincipalValue F v).ker := by
    apply iSup_le
    intro χ f hf
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    by_cases he : χ = 1
    · subst χ
      exact (h₁ f hf).trans (h.1 f hf).symm
    · exact (hχ χ he f hf).trans (h.2 χ he f hf).symm
  rw [principalUnitIsotype_span] at hker
  ext f : 1
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := f))))

/-- Lemma 5.3.1.3, p. 241. The local operator is a continuous linear embedding
with closed range and preserves every integral-unit isotype. -/
theorem weilPrincipalValue_embedding :
    letI : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
    Continuous (weilPrincipalValue F v) ∧ IsEmbedding (weilPrincipalValue F v) ∧
      IsClosed (range (weilPrincipalValue F v)) ∧
      ∀ χ : PontryaginDual (U F v), MapsTo (weilPrincipalValue F v)
        (principalUnitIsotype F v χ) (principalUnitIsotype F v χ) := by
  letI : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
  letI : PolynormableSpace ℂ (Test F v) := (finest_withSeminorms _).toPolynormableSpace
  let T := weilPrincipalValue F v
  have hπ : ‖(chosenFiniteUniformizer F v).val‖ < 1 := by
    rw [norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hj : Injective T := weilPrincipalValueFor_injective F v _ hπ
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hLeft : LeftInverse L T := fun f => DFunLike.congr_fun hL f
  have hc : Continuous T := finest_linear_continuous T
  refine ⟨hc, hLeft.isEmbedding (finest_linear_continuous L) hc,
    (finest_submodule_quotient T.range).2.1, ?_⟩
  intro χ f hf
  by_cases he : χ = 1
  · subst χ
    exact weilPrincipalValueFor_fixed F v _ f hf
  · rwa [(weilPrincipalValue_characterization F v _ (chosenFiniteUniformizer_spec F v)).2 χ he f hf]

/-- The repaired operator has range exactly the tests vanishing at the origin. -/
theorem weilPrincipalValue_range :
    range (weilPrincipalValue F v) = {f : Test F v | f.val 0 = 0} := by
  ext f
  let π := chosenFiniteUniformizer F v
  let A := principalUnitAverage F v
  let D := locallyConstantTestTranslate (K F v) π
  let radial (g : Test F v) := ∀ x y : K F v, ‖x‖ = ‖y‖ → g.val x = g.val y
  have hRad : radial (A f) := (principalUnitIsotype_one_iff_radial F v _).mp
    (principalUnitAverage_fixed F v f)
  constructor
  · rintro ⟨g, rfl⟩
    change g.val 0 - (A g).val (π⁻¹.val * 0) = 0
    rw [mul_zero, principalUnitAverage_eval_zero, sub_self]
  · intro hf
    have h0 : (A f).val 0 = 0 := (principalUnitAverage_eval_zero F v f).trans hf
    obtain ⟨g, hg, hgg⟩ := (finiteCompletion_principalValue F v π π
      (chosenFiniteUniformizer_spec F v) (chosenFiniteUniformizer_spec F v)).2.2 (A f)
      |>.mpr ⟨hRad, h0⟩
    have hAg : A g = g := principalUnitAverage_of_fixed F v g
      ((principalUnitIsotype_one_iff_radial F v g).mpr hg)
    have hAAf : A (A f) = A f :=
      principalUnitAverage_of_fixed F v (A f) (principalUnitAverage_fixed F v f)
    have hpre : A (g + f - A f) = g := by
      rw [map_sub, map_add, hAg, hAAf, add_sub_cancel_right]
    refine ⟨g + f - A f, ?_⟩
    change g + f - A f - D (A (g + f - A f)) = f
    rw [hpre]
    change g - D g = A f at hgg
    calc
      _ = (g - D g) + f - A f := by abel
      _ = f := by rw [hgg, add_comm (A f) f, add_sub_cancel_right]

private theorem principalUnitAction_commute (a : U F v) (r : (K F v)ˣ) (f : Test F v) :
    principalUnitAction F v a (locallyConstantTestTranslate (K F v) r f) =
      locallyConstantTestTranslate (K F v) r (principalUnitAction F v a f) := by
  apply Subtype.ext
  funext x
  change f.val (r⁻¹ • a.val⁻¹ • x) = f.val (a.val⁻¹ • r⁻¹ • x)
  rw [← mul_smul, ← mul_smul, mul_comm]

private theorem principalUnitAverage_commute (r : (K F v)ˣ) (f : Test F v) :
    principalUnitAverage F v (locallyConstantTestTranslate (K F v) r f) =
      locallyConstantTestTranslate (K F v) r (principalUnitAverage F v f) := by
  apply orbitDual_ext
  intro ℓ
  rw [principalUnitAverage_apply]
  change _ = (ℓ.comp (locallyConstantTestTranslate (K F v) r)) (principalUnitAverage F v f)
  rw [principalUnitAverage_apply]
  simp_rw [principalUnitAction_commute F v, LinearMap.comp_apply]

/-- Weil's operator commutes with the full multiplicative local action. -/
theorem weilPrincipalValue_commute (r : (K F v)ˣ) (f : Test F v) :
    weilPrincipalValue F v (locallyConstantTestTranslate (K F v) r f) =
      locallyConstantTestTranslate (K F v) r (weilPrincipalValue F v f) := by
  let π := chosenFiniteUniformizer F v
  let A := principalUnitAverage F v
  let T := locallyConstantTestTranslate (K F v) r
  let D := locallyConstantTestTranslate (K F v) π
  change T f - D (A (T f)) = T (f - D (A f))
  rw [principalUnitAverage_commute, map_sub]
  congr 1
  apply Subtype.ext
  funext x
  change (A f).val (r⁻¹ • π⁻¹ • x) = (A f).val (π⁻¹ • r⁻¹ • x)
  rw [← mul_smul, ← mul_smul, mul_comm]

/-- The dual multiplier of the principal-value operator. A translation
eigendistribution is multiplied by the missing Euler factor on the unramified
component. On a ramified component the operator fixes it. -/
theorem weilPrincipalValue_eigenfunctional
    (L : Test F v →ₗ[ℂ] ℂ) (c : (K F v)ˣ → ℂ)
    (he : ∀ r f, L (locallyConstantTestTranslate (K F v) r f) = c r * L f)
    (f : Test F v) :
    letI : Decidable (∀ a : U F v, c a.val = 1) := Classical.propDecidable _
    L (weilPrincipalValue F v f) =
      (if ∀ a : U F v, c a.val = 1 then 1 - c (chosenFiniteUniformizer F v) else 1) * L f := by
  classical
  let π := chosenFiniteUniformizer F v
  let A := principalUnitAverage F v
  change L (f - locallyConstantTestTranslate _ π (A f)) =
    (if ∀ a : U F v, c a.val = 1 then 1 - c π else 1) * L f
  rw [map_sub, he]
  by_cases h : ∀ a : U F v, c a.val = 1
  · have hA : L (A f) = L f := by
      dsimp [A]
      rw [principalUnitAverage_apply]
      have hg (a : U F v) : L (principalUnitAction F v a f) = L f := by
        change L (locallyConstantTestTranslate _ a.val f) = L f
        rw [he, h a, one_mul]
      simp only [hg, integral_const, measureReal_def, principalUnitHaar_univ,
        ENNReal.toReal_one, one_smul]
    rw [ite_eq_left h, hA, sub_mul, one_mul]
  · push Not at h
    obtain ⟨u, hu⟩ := h
    have hp := principalUnitAverage_fixed F v f u
    rw [PontryaginDual.one_apply, Circle.coe_one, one_smul] at hp
    have ha : c u.val * L (A f) = L (A f) := by
      rw [← he]
      exact congrArg L hp
    have hz : L (A f) = 0 := by
      by_contra hn
      apply hu
      apply mul_right_cancel₀ hn
      simpa only [one_mul] using ha
    have h' : ¬∀ a : U F v, c a.val = 1 := fun hh => hu (hh u)
    rw [ite_eq_right h', hz, mul_zero, sub_zero, one_mul]

end FiniteCompletion

end
end Masullo
