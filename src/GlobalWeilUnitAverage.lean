import SLocalFinitePlaceTranslation
import SLocalPrincipalValue

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField SchwartzMap

namespace Masullo
noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev U (v : Place F) := ↥(principalIntegralUnits F v)
private abbrev Arch := 𝓢(mixedEmbedding.mixedSpace F, ℂ)
private abbrev Local (v : Place F) := locallyConstantTests (v.adicCompletion F)

local instance testUnitCompactSpaceOnUnits (v : Place F) : CompactSpace (U F v) := principalIntegralUnits_compactSpace F v
local instance testUnitMeasurableSpaceOnUnits (v : Place F) : MeasurableSpace (U F v) := borel _
local instance testUnitBorelSpaceOnUnits (v : Place F) : BorelSpace (U F v) := ⟨rfl⟩

/-- Average the test at the selected finite integral-unit coordinate. -/
def globalFiniteUnitAverage (v : Place F) : GlobalBruhat F →L[ℂ] GlobalBruhat F :=
  globalBruhatCoordinateMap F v (principalUnitAverage F v)

private def insertPiTestFactor {S : Finset (Place F)} (v : S) (k : ∀ w : S, Local F w.val) :
    Local F v.val →ₗ[ℂ] locallyConstantTests (∀ w : S, w.val.adicCompletion F) := by
  let P (a : Local F v.val) := locallyConstantTestPiProduct (update k v a)
  have hP (a : Local F v.val) (x : ∀ w : S, w.val.adicCompletion F) :
      (P a).val x = (∏ w ∈ Finset.univ.erase v, (k w).val (x w)) * a.val (x v) := by
    rw [show P a = locallyConstantTestPiProduct (update k v a) from rfl,
      locallyConstantTestPiProduct_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ v), update_self]
    congr 1
    exact Finset.prod_congr rfl fun w hw => by rw [update_of_ne (Finset.ne_of_mem_erase hw)]
  exact
    { toFun := P
      map_add' := fun a b => Subtype.ext (funext fun x => by
        change (P (a + b)).val x = (P a).val x + (P b).val x
        rw [hP, hP, hP]
        exact mul_add _ _ _)
      map_smul' := fun c a => Subtype.ext (funext fun x => by
        change (P (c • a)).val x = c * (P a).val x
        rw [hP, hP]
        exact mul_left_comm _ _ _) }

private theorem average_pure (S : Finset (Place F)) (v : S) (φ : Arch F)
    (k : ∀ w : S, Local F w.val) :
    globalFiniteUnitAverage F v.val (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val =
      (sLocalBruhatPure F S φ
        (locallyConstantTestPiProduct (update k v (principalUnitAverage F v.val (k v))))).val := by
  rw [globalFiniteUnitAverage, globalBruhatCoordinateMap_stage F v.val _ S v.property]
  change (sLocalBruhatFiniteMap F S (sLocalCoordinateMap F S v (principalUnitAverage F v.val))
    (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k))).val = _
  rw [sLocalBruhatFiniteMap_pure, sLocalCoordinateMap_piProduct]

private theorem translate_pure (S : Finset (Place F)) (v : S) (a : (v.val.adicCompletion F)ˣ)
    (φ : Arch F) (k : ∀ w : S, Local F w.val) :
    GlobalBruhat.leftTranslate F (singleFiniteIdele F v.val a)
      (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val =
      (sLocalBruhatPure F S φ (locallyConstantTestPiProduct
        (update k v (locallyConstantTestTranslate _ a (k v))))).val := by
  rw [← sLocalFiniteZetaInsert_embed_eq_singleFiniteIdele F S v a]
  exact congrArg Subtype.val (sLocalBruhatLeftTranslate_finiteInsert_piProduct F S v a φ k)

private theorem averageLinear_pure (S : Finset (Place F)) (v : S) (φ : Arch F)
    (k : ∀ w : S, Local F w.val) (ℓ : GlobalBruhat F →ₗ[ℂ] ℂ) :
    let f := (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val
    let A (u : U F v.val) := ℓ (GlobalBruhat.leftTranslate F (singleFiniteIdele F v.val u.val) f)
    Integrable A (principalUnitHaar F v.val) ∧
      ℓ (globalFiniteUnitAverage F v.val f) = ∫ u, A u ∂principalUnitHaar F v.val := by
  let J := (ℓ.comp (sLocalBruhatImage F S).subtype).comp
    ((sLocalBruhatPure F S φ).comp (insertPiTestFactor F v k))
  intro f A
  have hA : A = fun u => J (principalUnitAction F v.val u (k v)) := by
    funext u
    change ℓ (GlobalBruhat.leftTranslate F (singleFiniteIdele F v.val u.val)
      (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val) = _
    rw [translate_pure]
    rfl
  rw [hA]
  refine ⟨(((principalUnitAction_orbit F v.val (k v)).comp J).continuous
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  change ℓ (globalFiniteUnitAverage F v.val
    (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val) = _
  rw [average_pure]
  exact principalUnitAverage_apply F v.val (k v) J

/-- Separated tests on stages carrying a fixed place span the global tests. -/
private theorem mem_of_stage_piProduct (v : Place F) (M : Submodule ℂ (GlobalBruhat F))
    (hM : ∀ (S : Finset (Place F)), v ∈ S → ∀ (φ : Arch F) (k : ∀ w : S, Local F w.val),
      (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val ∈ M)
    (f : GlobalBruhat F) : f ∈ M := by
  obtain ⟨S₀, hS₀⟩ := sLocalBruhat_bounded_subset F {f} (Bornology.isVonNBounded_singleton f)
  let S := insert v S₀
  have hw : v ∈ S := Finset.mem_insert_self _ _
  have hf : f ∈ sLocalBruhatImage F S := sLocalBruhatImage_mono F
    (Finset.subset_insert v S₀) (hS₀ (mem_singleton f))
  let J := (sLocalBruhatImage F S).subtype
  have hG : (⊤ : Submodule ℂ (sLocalBruhatImage F S)) ≤ M.comap J := by
    rw [← sLocalBruhatPure_span F S]
    apply Submodule.span_le.mpr
    rintro _ ⟨φ, ψ, rfl⟩
    have hGφ : (⊤ : Submodule ℂ (locallyConstantTests (∀ v : S, v.val.adicCompletion F))) ≤
        (M.comap J).comap (sLocalBruhatPure F S φ) := by
      rw [← locallyConstantTest_span_piProduct]
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact hM S hw φ k
    exact hGφ Submodule.mem_top
  exact hG (show (⟨f, hf⟩ : sLocalBruhatImage F S) ∈ ⊤ from Submodule.mem_top)

set_option maxHeartbeats 1000000 in
/-- Scalar pairing with the global test average agrees with Haar integration
of the corresponding adelic translations, for arbitrary coupled tests. -/
theorem globalFiniteUnitAverage_pairing (v : Place F) (f : GlobalBruhat F)
    (ℓ : GlobalBruhat F →ₗ[ℂ] ℂ) :
    let A (u : U F v) := ℓ (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) f)
    Integrable A (principalUnitHaar F v) ∧
      ℓ (globalFiniteUnitAverage F v f) = ∫ u, A u ∂principalUnitHaar F v := by
  let A (g : GlobalBruhat F) (u : U F v) := ℓ (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) g)
  let B := ℓ.comp (globalFiniteUnitAverage F v).toLinearMap
  let Good : Submodule ℂ (GlobalBruhat F) :=
    { carrier := {g | Integrable (A g) (principalUnitHaar F v) ∧ B g = ∫ u, A g u ∂principalUnitHaar F v}
      zero_mem' := by
        change Integrable (A 0) _ ∧ B 0 = _
        have h : A 0 = 0 := funext fun u => by simp [A]
        simp [h]
      add_mem' := fun {g h} hg hh => by
        change Integrable (A g) _ ∧ B g = _ at hg
        change Integrable (A h) _ ∧ B h = _ at hh
        change Integrable (A (g + h)) _ ∧ B (g + h) = _
        have he : A (g + h) = fun u => A g u + A h u := funext fun u => by simp [A]
        rw [he, map_add, integral_add hg.1 hh.1, hg.2, hh.2]
        exact ⟨hg.1.add hh.1, rfl⟩
      smul_mem' := fun c g hg => by
        change Integrable (A g) _ ∧ B g = _ at hg
        change Integrable (A (c • g)) _ ∧ B (c • g) = _
        have he : A (c • g) = fun u => c • A g u := funext fun u => by simp [A]
        rw [he, map_smul, integral_smul, hg.2]
        exact ⟨hg.1.smul c, rfl⟩ }
  change f ∈ Good
  apply mem_of_stage_piProduct F v Good _ f
  intro S hv φ k
  exact averageLinear_pure F S ⟨v, hv⟩ φ k ℓ

set_option maxHeartbeats 1000000 in
/-- The glued Weil operator is identity minus uniformizer translation
after the global finite-unit average. -/
theorem globalWeilPrincipalValue_eq_unitAverage (v : Place F) (f : GlobalBruhat F) :
    globalWeilPrincipalValue F v f = f - GlobalBruhat.leftTranslate F
      (singleFiniteIdele F v (chosenFiniteUniformizer F v)) (globalFiniteUnitAverage F v f) := by
  let P := (globalWeilPrincipalValue F v).toLinearMap
  let D := GlobalBruhat.leftTranslate F (singleFiniteIdele F v (chosenFiniteUniformizer F v))
  let P' := LinearMap.id - D.toLinearMap.comp (globalFiniteUnitAverage F v).toLinearMap
  let N := (P - P').ker
  apply sub_eq_zero.mp
  change f ∈ N
  apply mem_of_stage_piProduct F v N _ f
  intro S hv φ k
  let w : S := ⟨v, hv⟩
  let H := ((sLocalBruhatImage F S).subtype.comp (sLocalBruhatPure F S φ)).comp
    (insertPiTestFactor F w k)
  let x := (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k)).val
  have hx : H (k w) = x := by
    change (sLocalBruhatPure F S φ (locallyConstantTestPiProduct (update k w (k w)))).val = x
    rw [update_eq_self]
  change P x - P' x = 0
  apply sub_eq_zero.mpr
  change globalWeilPrincipalValue F v x = x - D (globalFiniteUnitAverage F v x)
  rw [show globalWeilPrincipalValue F v x =
    (sLocalWeilPrincipalValue F S w (sLocalBruhatPure F S φ (locallyConstantTestPiProduct k))).val
    from globalWeilPrincipalValue_stage F S w _, sLocalWeilPrincipalValue,
    sLocalBruhatFiniteMap_pure, sLocalCoordinateMap_piProduct]
  change H (weilPrincipalValue F v (k w)) = x - D (globalFiniteUnitAverage F v x)
  rw [show globalFiniteUnitAverage F v x =
    (sLocalBruhatPure F S φ (locallyConstantTestPiProduct
      (update k w (principalUnitAverage F v (k w))))).val from average_pure F S w φ k]
  change H (weilPrincipalValue F v (k w)) = x - GlobalBruhat.leftTranslate F
    (singleFiniteIdele F v (chosenFiniteUniformizer F v)) _
  rw [translate_pure F S w (chosenFiniteUniformizer F v) φ
    (update k w (principalUnitAverage F v (k w)))]
  rw [← hx]
  change H (k w - locallyConstantTestTranslate _ (chosenFiniteUniformizer F v)
    (principalUnitAverage F v (k w))) = _
  rw [map_sub, update_idem, update_self]
  rfl

private theorem dual_separates {f g : GlobalBruhat F}
    (h : ∀ L : GlobalBruhat F →ₗ[ℂ] ℂ, L f = L g) : f = g := by
  by_contra hn
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hn)
  exact hL (by rw [map_sub, h L, sub_self])

theorem globalBruhatLeftTranslate_mul (g h : Idele F) (f : GlobalBruhat F) :
    GlobalBruhat.leftTranslate F g (GlobalBruhat.leftTranslate F h f) =
      GlobalBruhat.leftTranslate F (g * h) f := by
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F g
    (GlobalBruhat.leftTranslate F h f)) =
      GlobalBruhat.evaluation F x (GlobalBruhat.leftTranslate F (g * h) f)
  rw [GlobalBruhat.leftTranslate_apply, GlobalBruhat.leftTranslate_apply,
    GlobalBruhat.leftTranslate_apply, mul_inv_rev, Units.val_mul, mul_assoc]

/-- Integral-unit averaging commutes with translation on the global test space. -/
theorem globalFiniteUnitAverage_leftTranslate (v : Place F) (g : Idele F) (f : GlobalBruhat F) :
    globalFiniteUnitAverage F v (GlobalBruhat.leftTranslate F g f) =
      GlobalBruhat.leftTranslate F g (globalFiniteUnitAverage F v f) := by
  apply dual_separates F
  intro L
  rw [(globalFiniteUnitAverage_pairing F v (GlobalBruhat.leftTranslate F g f) L).2]
  let M := L.comp (GlobalBruhat.leftTranslate F g).toLinearMap
  change _ = M (globalFiniteUnitAverage F v f)
  rw [(globalFiniteUnitAverage_pairing F v f M).2]
  apply integral_congr_ae
  exact .of_forall fun u => by
    change L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) (GlobalBruhat.leftTranslate F g f)) =
      L (GlobalBruhat.leftTranslate F g (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val) f))
    rw [globalBruhatLeftTranslate_mul, globalBruhatLeftTranslate_mul, mul_comm g]

theorem globalFiniteUnitAverage_idempotent (v : Place F) (f : GlobalBruhat F) :
    globalFiniteUnitAverage F v (globalFiniteUnitAverage F v f) = globalFiniteUnitAverage F v f := by
  have hu (u : U F v) : GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val)
      (globalFiniteUnitAverage F v f) = globalFiniteUnitAverage F v f := by
    apply dual_separates F
    intro L
    let M := L.comp (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val)).toLinearMap
    change M (globalFiniteUnitAverage F v f) = _
    rw [(globalFiniteUnitAverage_pairing F v f M).2, (globalFiniteUnitAverage_pairing F v f L).2]
    let A (w : U F v) := L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v w.val) f)
    calc
      _ = ∫ w : U F v, A (u * w) ∂principalUnitHaar F v := by
        apply integral_congr_ae
        exact .of_forall fun w => by
          change L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u.val)
            (GlobalBruhat.leftTranslate F (singleFiniteIdele F v w.val) f)) =
              L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v (u.val * w.val)) f)
          rw [globalBruhatLeftTranslate_mul, singleFiniteIdele_mul]
      _ = _ := integral_mul_left_eq_self (μ := principalUnitHaar F v) A u
  apply dual_separates F
  intro L
  rw [(globalFiniteUnitAverage_pairing F v (globalFiniteUnitAverage F v f) L).2]
  simp_rw [hu, integral_const, measureReal_def, principalUnitHaar_univ, ENNReal.toReal_one, one_smul]

end
end Masullo
