import WeilPrincipalValue
import LocallyConstantFiniteTensor
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped BigOperators BoundedContinuousFunction Classical ENNReal NNReal NumberField TensorProduct

namespace Masullo

noncomputable section

section Coinvariants

variable {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup E] [Module ℂ E]
  (ρ : G →* (E →ₗ[ℂ] E)) (ν : Measure G) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]

/-- The algebraic fixed subspace of a representation on tests. -/
def orbitFixedTests : Submodule ℂ E where
  carrier := {x | ∀ g : G, ρ g x = x}
  zero_mem' := fun _ => map_zero _
  add_mem' hx hy g := by rw [map_add, hx g, hy g]
  smul_mem' c x hx g := by rw [map_smul, hx g]

omit [T2Space G] in
/-- For a finest-topology test space, probability averaging identifies the
algebraic coinvariant quotient with the fixed subspace, in their actual topologies. -/
theorem exists_orbitCoinvariantAverage
    (h : ∀ f : E, IsLocallyConstant fun a => ρ a f) (hν : ν univ = 1) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    IsClosed (orbitDifferenceSpan ρ : Set E) ∧
      ∃ e : (E ⧸ orbitDifferenceSpan ρ) ≃L[ℂ] orbitFixedTests ρ, ∀ f,
        (e ((orbitDifferenceSpan ρ).mkQ f)).val = fixedOrbitAverage ρ ν h f := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  let W := finest_withSeminorms E
  letI : IsTopologicalAddGroup E := W.topologicalAddGroup
  let V := orbitDifferenceSpan ρ
  let I := orbitFixedTests ρ
  let L := fixedOrbitAverage ρ ν h
  let L' : E →ₗ[ℂ] I := L.codRestrict I (fixedOrbitAverage_fixed ρ ν h)
  have hker : V ≤ L'.ker := by
    intro f hf
    apply Subtype.ext
    change f ∈ L.ker
    exact (fixedOrbitAverage_ker ρ ν h hν).symm ▸ hf
  let e := V.liftQ L' hker
  let i := V.mkQ.comp I.subtype
  have he (f : E) : e (V.mkQ f) = L' f := rfl
  have hli : LeftInverse i e := by
    rintro ⟨f⟩
    change V.mkQ (L f) = V.mkQ f
    exact fixedOrbitAverage_mkQ ρ ν h hν f
  have hri : RightInverse i e := by
    intro f
    change e (V.mkQ f.val) = f
    rw [he]
    apply Subtype.ext
    exact fixedOrbitAverage_of_fixed ρ ν h hν f.val f.property
  letI : PolynormableSpace ℂ E := W.toPolynormableSpace
  have hc : Continuous e := by
    apply V.isQuotientMap_mkQ.continuous_iff.mpr
    change Continuous L'
    exact (finest_linear_continuous L).subtype_mk _
  let eq : (E ⧸ V) ≃L[ℂ] I :=
    ⟨LinearEquiv.ofLinear e i (LinearMap.ext hri) (LinearMap.ext hli),
      hc, V.isQuotientMap_mkQ.continuous.comp continuous_subtype_val⟩
  exact ⟨(finest_submodule_quotient V).2.1, eq, fun f => rfl⟩

omit [ν.IsMulLeftInvariant] in
/-- A different Haar normalization scales the induced map by a nonzero scalar. -/
theorem exists_orbitCoinvariantAverage_haar [SecondCountableTopology G] [ν.IsHaarMeasure]
    (h : ∀ f : E, IsLocallyConstant fun a => ρ a f) :
    letI : TopologicalSpace E := finestLocallyConvexTopology E
    (fixedOrbitAverage ρ ν h).ker = orbitDifferenceSpan ρ ∧
      ∃ e : (E ⧸ orbitDifferenceSpan ρ) ≃L[ℂ] orbitFixedTests ρ, ∀ f,
        (e ((orbitDifferenceSpan ρ).mkQ f)).val = fixedOrbitAverage ρ ν h f := by
  letI : TopologicalSpace E := finestLocallyConvexTopology E
  letI : ContinuousSMul ℂ E := (finest_withSeminorms E).continuousSMul
  let η : Measure G := Measure.haarMeasure ⊤
  letI : η.IsHaarMeasure := by dsimp [η]; infer_instance
  have hη : η univ = 1 := Measure.haarMeasure_self (K₀ := ⊤)
  obtain ⟨_, e, he⟩ := exists_orbitCoinvariantAverage ρ η h hη
  let r := Measure.haarScalarFactor ν η
  have hr : 0 < r := Measure.haarScalarFactor_pos_of_isHaarMeasure ν η
  have hν : ν = (r : ℝ≥0∞) • η := Measure.isMulLeftInvariant_eq_smul ν η
  let c : ℂ := (r : ℝ)
  have hc : c ≠ 0 := by
    change ((r : ℝ) : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.mpr (by exact_mod_cast hr.ne')
  have hs (f : E) : fixedOrbitAverage ρ ν h f = c • fixedOrbitAverage ρ η h f := by
    have H (σ : Measure G) [IsFiniteMeasure σ] (hσ : σ = (r : ℝ≥0∞) • η) :
        fixedOrbitAverage ρ σ h f = c • fixedOrbitAverage ρ η h f := by
      subst σ
      exact fixedOrbitAverage_smul_measure ρ η r h f
    exact H ν hν
  refine ⟨?_, e.trans (ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := orbitFixedTests ρ)
    (Units.mk0 c hc)), ?_⟩
  · ext f
    rw [LinearMap.mem_ker, hs, smul_eq_zero, or_iff_right hc,
      ← LinearMap.mem_ker, fixedOrbitAverage_ker ρ η h hη]
  · intro f
    change c • (e ((orbitDifferenceSpan ρ).mkQ f)).val = _
    rw [he, hs]

end Coinvariants

private theorem principalIntegralUnits_secondCountable (F : Type*) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology ↥(principalIntegralUnits F v) := by
  letI := (finitePlace_locallyConstantTests_context F v).2
  letI : SecondCountableTopology (v.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  exact IsEmbedding.subtypeVal.secondCountableTopology

/-- Compactly supported continuous functions with the uniform norm. -/
def uniformCompactTests (X : Type*) [TopologicalSpace X] :
    Submodule ℂ (X →ᵇ ℂ) where
  carrier := {f | HasCompactSupport f}
  zero_mem' := HasCompactSupport.zero
  add_mem' hf hg := hf.add hg
  smul_mem' _ _ hf := hf.smul_left

/-- Regard a locally constant test as a compactly supported continuous function. -/
def locallyConstantToUniform {X : Type*} [TopologicalSpace X] :
    locallyConstantTests X →ₗ[ℂ] uniformCompactTests X where
  toFun f := ⟨ofCompactSupport f.val f.property.1.continuous f.property.2,
    f.property.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact BoundedContinuousFunction.ext fun x => rfl
  map_smul' c f := by
    apply Subtype.ext
    exact BoundedContinuousFunction.ext fun x => rfl

section Local

variable (F : Type*) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))
private abbrev K := v.adicCompletion F
private abbrev Test := locallyConstantTests (K F v)
private abbrev U := ↥(principalIntegralUnits F v)
local instance : CompactSpace (U F v) := principalIntegralUnits_compactSpace F v
local instance : SecondCountableTopology (U F v) := principalIntegralUnits_secondCountable F v
local instance : MeasurableSpace (U F v) := borel _
local instance : BorelSpace (U F v) := ⟨rfl⟩
local instance : (principalUnitHaar F v).Regular := by unfold principalUnitHaar; infer_instance

private theorem principalUnitAverage_eval_haar (μ : Measure (U F v)) [μ.IsHaarMeasure]
    (f : Test F v) (x : K F v) :
    (fixedOrbitAverage (principalUnitAction F v) μ (principalUnitAction_orbit F v) f).val x =
      ∫ u : U F v, f.val (x * u.val.val) ∂μ := by
  let ev := (LinearMap.proj x).comp (Test F v).subtype
  change ev (fixedOrbitAverage (principalUnitAction F v) μ (principalUnitAction_orbit F v) f) = _
  rw [fixedOrbitAverage_apply]
  let a (u : U F v) := f.val (x * u.val.val)
  have he (u : U F v) : ev (principalUnitAction F v u f) = a u⁻¹ := by
    change f.val (u⁻¹.val.val * x) = f.val (x * u⁻¹.val.val)
    rw [mul_comm]
  simp_rw [he]
  exact integral_inv_eq_self a μ

/-- The local average has the manuscript's positive-argument Haar integral. -/
theorem principalUnitAverage_eval (f : Test F v) (x : K F v) :
    (principalUnitAverage F v f).val x =
      ∫ u : U F v, f.val (x * u.val.val) ∂principalUnitHaar F v :=
  principalUnitAverage_eval_haar F v (principalUnitHaar F v) f x

/-- Lemma 6.1.2.4(1)–(2). The difference span is closed. Normalized
Haar averaging has that kernel and induces the invariant-space isomorphism. -/
theorem finitePlace_coinvariant_average :
    letI : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
    let V := orbitDifferenceSpan (principalUnitAction F v)
    IsClosed (V : Set (Test F v)) ∧ (principalUnitAverage F v).ker = V ∧
      Continuous (principalUnitAverage F v) ∧
      Continuous ((locallyConstantToUniform (X := K F v)).comp (principalUnitAverage F v)) ∧
      ∃ e : (Test F v ⧸ V) ≃L[ℂ] orbitFixedTests (principalUnitAction F v), ∀ f,
        (e (V.mkQ f)).val = principalUnitAverage F v f := by
  letI : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
  letI : PolynormableSpace ℂ (Test F v) := (finest_withSeminorms _).toPolynormableSpace
  let ρ := principalUnitAction F v
  let h := principalUnitAction_orbit F v
  let ν := principalUnitHaar F v
  have hν := principalUnitHaar_univ F v
  obtain ⟨hc, e, he⟩ := exists_orbitCoinvariantAverage ρ ν h hν
  refine ⟨hc, fixedOrbitAverage_ker ρ ν h hν, finest_linear_continuous _, ?_, e, he⟩
  exact finest_linear_continuous ((locallyConstantToUniform (X := K F v)).comp (principalUnitAverage F v))

/-- Taking the closure of the local relations yields the same coinvariants. -/
theorem finitePlace_coinvariant_relations_closure :
    letI : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
    let V : Set (Test F v) := orbitDifferenceSpan (principalUnitAction F v)
    closure V = V := by
  letI : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
  exact (finitePlace_coinvariant_average F v).1.closure_eq

/-- The same coinvariant isomorphism is induced by the local integral for any
Haar normalization on the integral units. -/
theorem finitePlace_coinvariant_average_haar (μ : Measure (U F v)) [μ.IsHaarMeasure] :
    letI : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
    let V := orbitDifferenceSpan (principalUnitAction F v)
    let A := fixedOrbitAverage (principalUnitAction F v) μ (principalUnitAction_orbit F v)
    A.ker = V ∧ Continuous A ∧ Continuous ((locallyConstantToUniform (X := K F v)).comp A) ∧
    ∃ e : (Test F v ⧸ V) ≃L[ℂ] orbitFixedTests (principalUnitAction F v), ∀ (f : Test F v) (x : K F v),
      (e (V.mkQ f)).val.val x = ∫ u : U F v, f.val (x * u.val.val) ∂μ := by
  letI : TopologicalSpace (Test F v) := finestLocallyConvexTopology _
  letI : PolynormableSpace ℂ (Test F v) := (finest_withSeminorms _).toPolynormableSpace
  obtain ⟨hker, e, he⟩ := exists_orbitCoinvariantAverage_haar (principalUnitAction F v) μ
    (principalUnitAction_orbit F v)
  refine ⟨hker, finest_linear_continuous _, finest_linear_continuous _, e, fun f x => ?_⟩
  rw [he]
  exact principalUnitAverage_eval_haar F v μ f x

end Local

section Product

variable (F : Type*) [Field F] [NumberField F]
variable (D : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev FieldProduct := (w : D) → w.val.adicCompletion F
private abbrev UnitProduct := (w : D) → ↥(principalIntegralUnits F w.val)
private abbrev ProductTest := locallyConstantTests (FieldProduct F D)

local instance (w : D) : CompactSpace ↥(principalIntegralUnits F w.val) :=
  principalIntegralUnits_compactSpace F w.val
local instance (w : D) : SecondCountableTopology ↥(principalIntegralUnits F w.val) :=
  principalIntegralUnits_secondCountable F w.val
local instance (w : D) : MeasurableSpace ↥(principalIntegralUnits F w.val) := borel _
local instance (w : D) : BorelSpace ↥(principalIntegralUnits F w.val) := ⟨rfl⟩
local instance (w : D) : (principalUnitHaar F w.val).Regular := by
  unfold principalUnitHaar
  infer_instance

private def productUnitEmbedding : UnitProduct F D →* (FieldProduct F D)ˣ :=
  ContinuousMulEquiv.piUnits.symm.toMonoidHom.comp
    { toFun := fun u w => (u w).val
      map_one' := rfl
      map_mul' _ _ := rfl }

private theorem productUnitEmbedding_continuous : Continuous (productUnitEmbedding F D) :=
  ContinuousMulEquiv.piUnits.symm.continuous.comp
    (continuous_pi fun w => continuous_subtype_val.comp (continuous_apply w))

/-- Pull back tests along multiplication by the inverse unit tuple. -/
def productUnitAction : UnitProduct F D →* (ProductTest F D →ₗ[ℂ] ProductTest F D) where
  toFun u := locallyConstantTestTranslate (FieldProduct F D) (productUnitEmbedding F D u)
  map_one' := by
    rw [map_one]
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change f.val ((1 : (FieldProduct F D)ˣ)⁻¹ • x) = f.val x
    simp
  map_mul' a b := by
    rw [map_mul]
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    let e := productUnitEmbedding F D
    change f.val ((e a * e b)⁻¹ • x) = f.val ((e b)⁻¹ • (e a)⁻¹ • x)
    rw [mul_inv_rev, mul_smul]

private theorem productUnitAction_orbit (f : ProductTest F D) :
    IsLocallyConstant fun u => productUnitAction F D u f :=
  (locallyConstantTestTranslate_orbit_locallyConstant (FieldProduct F D) f).comp_continuous
    (productUnitEmbedding_continuous F D)

/-- Product of the normalized local Haar measures on the integral unit groups. -/
def productUnitHaar : Measure (UnitProduct F D) := Measure.pi fun w => principalUnitHaar F w.val

local instance : (productUnitHaar F D).IsHaarMeasure := by unfold productUnitHaar; infer_instance

local instance : IsFiniteMeasure (productUnitHaar F D) := by unfold productUnitHaar; infer_instance

theorem productUnitHaar_univ : productUnitHaar F D univ = 1 := by
  rw [productUnitHaar, Measure.pi_univ]
  simp only [principalUnitHaar_univ, Finset.prod_const_one]

def productUnitAverage : ProductTest F D →ₗ[ℂ] ProductTest F D :=
  fixedOrbitAverage (productUnitAction F D) (productUnitHaar F D) (productUnitAction_orbit F D)

private theorem productUnitAverage_eval_haar (μ : Measure (UnitProduct F D)) [μ.IsHaarMeasure]
    (f : ProductTest F D) (x : FieldProduct F D) :
    (fixedOrbitAverage (productUnitAction F D) μ (productUnitAction_orbit F D) f).val x =
      ∫ u : UnitProduct F D, f.val (fun w => x w * (u w).val.val) ∂μ := by
  let e (u : UnitProduct F D) := f.val (fun w => x w * (u w).val.val)
  let ev := (LinearMap.proj x).comp (ProductTest F D).subtype
  change ev (fixedOrbitAverage (productUnitAction F D) μ
    (productUnitAction_orbit F D) f) = _
  rw [fixedOrbitAverage_apply]
  have he (u : UnitProduct F D) : ev (productUnitAction F D u f) = e u⁻¹ := by
    change f.val (fun w => ((u w)⁻¹).val.val * x w) =
      f.val (fun w => x w * ((u w)⁻¹).val.val)
    exact congrArg f.val (funext fun w => mul_comm _ _)
  simp_rw [he]
  exact integral_inv_eq_self e μ

/-- The average on the finite product is the actual product Haar integral. -/
theorem productUnitAverage_eval (f : ProductTest F D) (x : FieldProduct F D) :
    (productUnitAverage F D f).val x =
      ∫ u : UnitProduct F D, f.val (fun w => x w * (u w).val.val) ∂productUnitHaar F D :=
  productUnitAverage_eval_haar F D (productUnitHaar F D) f x

set_option maxHeartbeats 600000 in
/-- On elementary products the averaging map is the tensor of the local averages. -/
theorem productUnitAverage_piProduct (g : ∀ w : D, locallyConstantTests (w.val.adicCompletion F)) :
    productUnitAverage F D (locallyConstantTestPiProduct (X := fun w : D => w.val.adicCompletion F) g) =
      locallyConstantTestPiProduct (X := fun w : D => w.val.adicCompletion F)
        (fun w => principalUnitAverage F w.val (g w)) := by
  apply Subtype.ext
  funext x
  rw [productUnitAverage_eval, locallyConstantTestPiProduct_apply]
  simp_rw [locallyConstantTestPiProduct_apply, principalUnitAverage_eval]
  exact integral_fintype_prod_eq_prod (fun w (u : ↥(principalIntegralUnits F w.val)) =>
    (g w).val (x w * u.val.val))

/-- Lemma 6.1.2.4(3). Product averaging factors through the closed
coinvariant relations and identifies the quotient with the fixed tests. -/
theorem productUnit_coinvariant_average :
    letI : TopologicalSpace (ProductTest F D) := finestLocallyConvexTopology _
    let V := orbitDifferenceSpan (productUnitAction F D)
    IsClosed (V : Set (ProductTest F D)) ∧ (productUnitAverage F D).ker = V ∧
      ∃ e : (ProductTest F D ⧸ V) ≃L[ℂ] orbitFixedTests (productUnitAction F D), ∀ f,
        (e (V.mkQ f)).val = productUnitAverage F D f := by
  obtain ⟨hc, e, he⟩ := exists_orbitCoinvariantAverage
    (productUnitAction F D) (productUnitHaar F D)
    (productUnitAction_orbit F D) (productUnitHaar_univ F D)
  exact ⟨hc, fixedOrbitAverage_ker _ _ _ (productUnitHaar_univ F D), e, he⟩

theorem productUnit_fixedTests_closed :
    letI : TopologicalSpace (ProductTest F D) := finestLocallyConvexTopology _
    IsClosed (orbitFixedTests (productUnitAction F D) : Set (ProductTest F D)) := by
  letI : TopologicalSpace (ProductTest F D) := finestLocallyConvexTopology _
  exact (finest_submodule_quotient (orbitFixedTests (productUnitAction F D))).2.1

/-- The product map on coinvariants allows independent Haar normalizations
at the constituent places. -/
theorem productUnit_coinvariant_average_haar
    (μ : (w : D) → Measure ↥(principalIntegralUnits F w.val)) [∀ w, (μ w).IsHaarMeasure] :
    letI : TopologicalSpace (ProductTest F D) := finestLocallyConvexTopology _
    let V := orbitDifferenceSpan (productUnitAction F D)
    ∃ e : (ProductTest F D ⧸ V) ≃L[ℂ] orbitFixedTests (productUnitAction F D),
      (∀ (f : ProductTest F D) (x : FieldProduct F D),
        (e (V.mkQ f)).val.val x =
          ∫ u : UnitProduct F D, f.val (fun w => x w * (u w).val.val) ∂Measure.pi μ) ∧
      (∀ (g : ∀ w : D, locallyConstantTests (w.val.adicCompletion F)) (x : FieldProduct F D),
        (e (V.mkQ (locallyConstantTestPiProduct
          (X := fun w : D => w.val.adicCompletion F) g))).val.val x =
          ∏ w, ∫ u : ↥(principalIntegralUnits F w.val), (g w).val (x w * u.val.val) ∂μ w) := by
  letI : TopologicalSpace (ProductTest F D) := finestLocallyConvexTopology _
  haveI : (Measure.pi μ).IsHaarMeasure := Measure.pi.isHaarMeasure μ
  obtain ⟨_, e, he⟩ := exists_orbitCoinvariantAverage_haar (productUnitAction F D)
    (Measure.pi μ) (productUnitAction_orbit F D)
  have h (f : ProductTest F D) (x : FieldProduct F D) :
      (e ((orbitDifferenceSpan (productUnitAction F D)).mkQ f)).val.val x =
        ∫ u : UnitProduct F D, f.val (fun w => x w * (u w).val.val) ∂Measure.pi μ := by
    rw [he]
    exact productUnitAverage_eval_haar F D (Measure.pi μ) f x
  refine ⟨e, h, fun g x => ?_⟩
  rw [h]
  simp_rw [locallyConstantTestPiProduct_apply]
  exact integral_fintype_prod_eq_prod (fun w (u : ↥(principalIntegralUnits F w.val)) =>
    (g w).val (x w * u.val.val))

end Product

end
end Masullo
