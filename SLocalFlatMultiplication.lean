import SLocalFlatTestMellin
import ArchimedeanFlatMultiplication
import FiniteFlatQuasiCharacter

open Function IsDedekindDomain NumberField Set Topology
open scoped Classical SchwartzMap NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev P := sLocalPolarFreeTestSubspace F S
private abbrev Arch := archimedeanFlatTestSubspace F
private abbrev L (v : S) := v.val.adicCompletion F
private abbrev G (v : S) := finiteFlatTests F v.val
private abbrev Test := sLocalBruhatImage F S

private def flatPure (a : Arch F) (g : ∀ v : S, G F S v) : P F S :=
  sLocalPolarFreePure F S a (fun v ↦ (g v).val) (fun v ↦ (g v).property)

private theorem flatInduction (p : P F S → Prop)
    (hp : ∀ a g, p (flatPure F S a g)) (hz : p 0)
    (ha : ∀ x y, p x → p y → p (x + y)) (hs : ∀ (c : ℂ) x, p x → p (c • x))
    (f : P F S) : p f := by
  exact sLocalPolarFree_induction F S p (fun a g hg ↦ hp a (fun v ↦ ⟨g v, hg v⟩))
    hz ha hs f

private theorem exists_sLocalPolarFree_finiteSingleCLM (v : S)
    (M : G F S v →ₗ[ℂ] G F S v) :
    ∃ N : P F S →L[ℂ] P F S,
      ∀ (a : Arch F) (g : ∀ w : S, G F S w),
        N (flatPure F S a g) = flatPure F S a (Function.update g v (M (g v))) := by
  obtain ⟨Q, hQ⟩ := (G F S v).exists_isCompl
  let π := (G F S v).projectionOnto Q hQ
  let T := (G F S v).subtype.comp (M.comp π)
  let K := sLocalBruhatFiniteMap F S (sLocalCoordinateMap F S v T)
  have hPure (a : Arch F) (g : ∀ w : S, G F S w) :
      K (flatPure F S a g).val = (flatPure F S a (Function.update g v (M (g v)))).val := by
    change sLocalBruhatFiniteMap F S (sLocalCoordinateMap F S v T)
        (sLocalBruhatPure F S a.val (locallyConstantTestPiProduct fun w ↦ (g w).val)) = _
    rw [sLocalBruhatFiniteMap_pure, sLocalCoordinateMap_piProduct]
    congr 2
    funext w
    by_cases hw : w = v
    · subst w
      rw [Function.update_self, Function.update_self]
      change (M (π (g v).val)).val = (M (g v)).val
      have he : π (g v).val = g v := Submodule.projectionOnto_apply_left hQ (g v)
      rw [he]
    · rw [Function.update_of_ne hw, Function.update_of_ne hw]
  have hK (f : Test F S) (hf : f ∈ P F S) : K f ∈ P F S := by
    induction hf using Submodule.span_induction with
    | mem f h =>
      obtain ⟨a, g, ha, hg, rfl⟩ := h
      let a' : Arch F := ⟨a, ha⟩
      let g' : ∀ w : S, G F S w := fun w ↦ ⟨g w, hg w⟩
      change K (flatPure F S a' g').val ∈ P F S
      rw [hPure]
      exact (flatPure F S a' (Function.update g' v (M (g' v)))).property
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  exact ⟨(K.comp (P F S).subtypeL).codRestrict _ (fun f ↦ hK f.val f.property),
    fun a g ↦ Subtype.ext (hPure a g)⟩

/-- The continuous lift of finitely many independent changes to the flat
finite-place factors of S-local tests. -/
private theorem exists_sLocalPolarFree_finiteCLM (M : ∀ v : S, G F S v →ₗ[ℂ] G F S v)
    (T : Finset S) :
    ∃ N : P F S →L[ℂ] P F S, ∀ (a : Arch F) (g : ∀ w : S, G F S w),
      N (flatPure F S a g) =
        flatPure F S a (fun w ↦ if w ∈ T then M w (g w) else g w) := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨ContinuousLinearMap.id ℂ _, fun a g ↦ ?_⟩
    simp
  | insert v T hv ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨Q, hQ⟩ := exists_sLocalPolarFree_finiteSingleCLM F S v (M v)
    refine ⟨Q.comp N, fun a g ↦ ?_⟩
    change Q (N (flatPure F S a g)) = _
    rw [hN, hQ]
    congr 1
    funext w
    by_cases hw : w = v
    · subst w
      rw [Function.update_self, ite_eq_right hv, ite_eq_left (Finset.mem_insert_self _ _)]
    · rw [Function.update_of_ne hw]
      simp only [Finset.mem_insert, hw, false_or]

private abbrev U := (SAdeles F S)ˣ

private def archInsert : (InfiniteAdeleRing F)ˣ →ₜ* U F S :=
  ⟨{ toFun := sLocalArchZetaInsert F S,
     map_one' := by simp [sLocalArchZetaInsert],
     map_mul' := fun a b ↦ by simp [sLocalArchZetaInsert, ← map_mul, Prod.mk_mul_mk] },
    (sLocalZetaIdeleCoordinates F S).symm.continuous.comp (continuous_id.prodMk continuous_const)⟩

private def finiteInsert (v : S) : (L F S v)ˣ →ₜ* U F S :=
  ⟨{ toFun := sLocalFiniteZetaInsert F S v,
     map_one' := by simp [sLocalFiniteZetaInsert],
     map_mul' := fun a b ↦ by simp [sLocalFiniteZetaInsert, ← map_mul, Prod.mk_mul_mk, Pi.mulSingle_mul] },
    (sLocalZetaIdeleCoordinates F S).symm.continuous.comp
      (continuous_const.prodMk (continuous_mulSingle (A := fun w : S ↦ (L F S w)ˣ) v))⟩

private theorem character_factor (χ : U F S →ₜ* ℂˣ)
    (p : (InfiniteAdeleRing F)ˣ × (∀ v : S, (L F S v)ˣ)) :
    (χ (archInsert F S p.1) : ℂ) * (∏ v : S, (χ (finiteInsert F S v (p.2 v)) : ℂ)) =
      (χ ((sLocalZetaIdeleCoordinates F S).symm p) : ℂ) := by
  have he : archInsert F S p.1 * (∏ v : S, finiteInsert F S v (p.2 v)) =
      (sLocalZetaIdeleCoordinates F S).symm p := by
    apply (sLocalZetaIdeleCoordinates F S).injective
    simp only [map_mul, map_prod]
    change (sLocalZetaIdeleCoordinates F S) ((sLocalZetaIdeleCoordinates F S).symm (p.1, 1)) *
      (∏ v : S, (sLocalZetaIdeleCoordinates F S)
        ((sLocalZetaIdeleCoordinates F S).symm (1, Pi.mulSingle v (p.2 v)))) = _
    simp only [ContinuousMulEquiv.apply_symm_apply]
    have hp : (∏ v : S, ((1 : (InfiniteAdeleRing F)ˣ), Pi.mulSingle v (p.2 v))) = (1, p.2) := by
      apply Prod.ext
      · change (MonoidHom.fst _ _) (∏ v : S, ((1 : (InfiniteAdeleRing F)ˣ), Pi.mulSingle v (p.2 v))) = _
        rw [map_prod]
        exact Finset.prod_const_one
      · change (MonoidHom.snd _ _) (∏ v : S, ((1 : (InfiniteAdeleRing F)ˣ), Pi.mulSingle v (p.2 v))) = _
        rw [map_prod]
        exact Finset.univ_prod_mulSingle p.2
    rw [hp, Prod.mk_mul_mk, mul_one, one_mul]
  let f : U F S →* ℂ := {
    toFun := fun u ↦ (χ u : ℂ)
    map_one' := by simp
    map_mul' := fun a b ↦ by simp }
  change f (archInsert F S p.1) * (∏ v : S, f (finiteInsert F S v (p.2 v))) = _
  rw [← map_prod, ← map_mul, he]
  rfl

private def ev (x : SAdeles F S) : P F S →ₗ[ℂ] ℂ :=
  (LinearMap.proj (R := ℂ) x).comp ((sLocalBruhatRestriction F S).comp
    ((Test F S).subtype.comp (P F S).subtype))

private theorem ev_flatPure (x : SAdeles F S) (a : Arch F) (g : ∀ v : S, G F S v) :
    ev F S x (flatPure F S a g) =
      a.val (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * ∏ v : S, (g v).val.val (x.2 v) := by
  change sLocalBruhatRestriction F S
    (sLocalBruhatPure F S a.val (locallyConstantTestPiProduct fun v ↦ (g v).val)).val x = _
  rw [sLocalBruhatPure_restrict, locallyConstantTestPiProduct_apply]

private theorem exists_quasiCharacter_mulCLM (χ : U F S →ₜ* ℂˣ) :
    ∃ M : P F S →L[ℂ] P F S, ∀ f : P F S, ∀ u : U F S,
      ev F S u.val (M f) = (χ u : ℂ) * ev F S u.val f := by
  obtain ⟨A, hA⟩ := exists_archimedeanQuasiCharacter_mulEquiv F (χ.comp (archInsert F S))
  obtain ⟨M, hM⟩ := exists_sLocalPolarFree_archMulCLM F S A
  let m (v : S) : G F S v →ₗ[ℂ] G F S v :=
    letI : TopologicalSpace (locallyConstantTests (L F S v)) := finestLocallyConvexTopology _
    (finiteFlatQuasiCharacterEquiv F v.val (χ.comp (finiteInsert F S v))).toLinearEquiv.toLinearMap
  obtain ⟨N, hN⟩ := exists_sLocalPolarFree_finiteCLM F S m Finset.univ
  have hN' (a : Arch F) (g : ∀ v : S, G F S v) :
      N (flatPure F S a g) = flatPure F S a (fun v ↦ m v (g v)) := by
    simpa only [Finset.mem_univ, ite_true] using hN a g
  have hM' (a : Arch F) (g : ∀ v : S, G F S v) :
      M (flatPure F S a g) = flatPure F S (A a) g :=
    hM a (fun v ↦ (g v).val) (fun v ↦ (g v).property)
  let K := N.comp M
  refine ⟨K, fun f u ↦ ?_⟩
  induction f using flatInduction F S with
  | hp a g =>
    obtain ⟨p, rfl⟩ := (sLocalZetaIdeleCoordinates F S).symm.surjective u
    change ev F S _ (N (M (flatPure F S a g))) = _
    rw [hM', hN', ev_flatPure, ev_flatPure]
    let x := InfiniteAdeleRing.ringEquiv_mixedSpace F p.1.val
    change (A a).val x * (∏ v : S, (m v (g v)).val.val (p.2 v).val) =
      (χ ((sLocalZetaIdeleCoordinates F S).symm p) : ℂ) *
        (a.val x * (∏ v : S, (g v).val.val (p.2 v).val))
    have ha := hA a p.1
    change (A a).val x = (χ (archInsert F S p.1) : ℂ) * a.val x at ha
    rw [ha]
    have hf (v : S) : (m v (g v)).val.val (p.2 v).val =
        (χ (finiteInsert F S v (p.2 v)) : ℂ) * (g v).val.val (p.2 v).val :=
      finiteFlatQuasiCharacterEquiv_apply_units F v.val (χ.comp (finiteInsert F S v)) (g v) (p.2 v)
    simp_rw [hf, Finset.prod_mul_distrib]
    rw [← character_factor F S χ p]
    ring
  | hz => rw [map_zero, map_zero, mul_zero]
  | ha x y hx hy => rw [map_add, map_add, map_add, hx, hy, mul_add]
  | hs c x hx => rw [map_smul, map_smul, map_smul, hx]; simp only [smul_eq_mul, mul_left_comm]

private theorem ev_eq_zero_of_nonunit (x : SAdeles F S)
    (hx : ∀ u : U F S, u.val ≠ x) (f : P F S) : ev F S x f = 0 := by
  induction f using flatInduction F S with
  | hp a g =>
    rw [ev_flatPure]
    by_contra h0
    let y := InfiniteAdeleRing.ringEquiv_mixedSpace F x.1
    have hJ : a.val y ≠ 0 := fun h ↦ h0 (by rw [show a.val _ = 0 from h, zero_mul])
    have hFlat (hy : y ∈ {x | (∃ v : {v : InfinitePlace F // v.IsReal}, x.1 v = 0) ∨
        ∃ v : {v : InfinitePlace F // v.IsComplex}, x.2 v = 0}) : a.val y = 0 := by
      have h := (mem_schwartzFlatSubspace _ _).mp a.property y hy 0
      exact norm_eq_zero.mp (by simpa only [norm_iteratedFDeriv_zero, norm_zero] using congrArg norm h)
    have hr (v : {v : InfinitePlace F // v.IsReal}) : y.1 v ≠ 0 :=
      fun h ↦ hJ (hFlat (Or.inl ⟨v, h⟩))
    have hc (v : {v : InfinitePlace F // v.IsComplex}) : y.2 v ≠ 0 :=
      fun h ↦ hJ (hFlat (Or.inr ⟨v, h⟩))
    have hf (v : S) : x.2 v ≠ 0 := by
      intro h
      apply h0
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (by
        rw [h]
        exact (g v).property), mul_zero]
    let arch := (infiniteAdeleUnitsCoordinates F).symm
      (fun v ↦ Units.mk0 (y.1 v) (hr v), fun v ↦ Units.mk0 (y.2 v) (hc v))
    apply hx ((sLocalZetaIdeleCoordinates F S).symm
      (arch, fun v ↦ Units.mk0 (x.2 v) (hf v)))
    change (arch.val, x.2) = x
    refine Prod.ext ?_ rfl
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    apply Prod.ext
    · funext v
      rw [← infiniteAdeleUnitsCoordinates_real_val F arch v]
      change (((infiniteAdeleUnitsCoordinates F) ((infiniteAdeleUnitsCoordinates F).symm _)).1 v).val = _
      rw [ContinuousMulEquiv.apply_symm_apply]
      rfl
    · funext v
      rw [← infiniteAdeleUnitsCoordinates_complex_val F arch v]
      change (((infiniteAdeleUnitsCoordinates F) ((infiniteAdeleUnitsCoordinates F).symm _)).2 v).val = _
      rw [ContinuousMulEquiv.apply_symm_apply]
      rfl
  | hz => exact map_zero _
  | ha x y hx hy => rw [map_add, hx, hy, add_zero]
  | hs c x hx => rw [map_smul, hx, smul_zero]

private theorem flat_ext_of_units (f g : P F S)
    (h : ∀ u : U F S, ev F S u.val f = ev F S u.val g) : f = g := by
  have he (x : SAdeles F S) : ev F S x f = ev F S x g := by
    by_cases hx : ∃ u : U F S, u.val = x
    · obtain ⟨u, rfl⟩ := hx
      exact h u
    · have hn (u : U F S) : u.val ≠ x := fun hu ↦ hx ⟨u, hu⟩
      rw [ev_eq_zero_of_nonunit F S x hn f, ev_eq_zero_of_nonunit F S x hn g]
  apply Subtype.ext
  apply Subtype.ext
  apply (GlobalBruhat.algebraicEquiv F).injective
  apply Subtype.ext
  funext x
  change GlobalBruhat.evaluation F x f.val.val = GlobalBruhat.evaluation F x g.val.val
  rw [sLocalBruhatRestriction_reconstruct, sLocalBruhatRestriction_reconstruct]
  exact congrArg (· * _) (he (sAdelesProjection F S x))

/-- Lemma 5.3.4.2(3). Multiplication by a continuous S-idelic
quasi-character acts by a continuous linear automorphism on polar-free
Schwartz–Bruhat tests, through zero extension to the additive space. -/
theorem exists_sLocalPolarFree_quasiCharacter_mulEquiv (χ : U F S →ₜ* ℂˣ) :
    ∃ M : P F S ≃L[ℂ] P F S, ∀ f : P F S, ∀ u : U F S,
      sLocalBruhatRestriction F S (M f).val.val u.val =
        (χ u : ℂ) * sLocalBruhatRestriction F S f.val.val u.val := by
  obtain ⟨M, hM⟩ := exists_quasiCharacter_mulCLM F S χ
  obtain ⟨N, hN⟩ := exists_quasiCharacter_mulCLM F S χ⁻¹
  have hl (f : P F S) : N (M f) = f := by
    apply flat_ext_of_units F S
    intro u
    rw [hN, hM]
    change (↑((χ u)⁻¹) : ℂ) * ((χ u : ℂ) * ev F S u.val f) = _
    rw [← mul_assoc, Units.inv_mul, one_mul]
  have hr (f : P F S) : M (N f) = f := by
    apply flat_ext_of_units F S
    intro u
    rw [hM, hN]
    change (χ u : ℂ) * ((↑((χ u)⁻¹) : ℂ) * ev F S u.val f) = _
    rw [← mul_assoc, Units.mul_inv, one_mul]
  exact ⟨⟨{ M.toLinearMap with invFun := N, left_inv := hl, right_inv := hr },
    M.continuous, N.continuous⟩, hM⟩

/-- In particular, the action in Lemma 5.3.4.2(3) is defined for each
quasi-character on the S-idele class group. -/
theorem exists_sLocalPolarFree_classQuasiCharacter_mulEquiv
    (χ : SIdeleQuotient F S →ₜ* ℂˣ) :
    ∃ M : P F S ≃L[ℂ] P F S, ∀ f : P F S, ∀ u : U F S,
      sLocalBruhatRestriction F S (M f).val.val u.val =
        (χ (QuotientGroup.mk u) : ℂ) * sLocalBruhatRestriction F S f.val.val u.val :=
  exists_sLocalPolarFree_quasiCharacter_mulEquiv F S
    (χ.comp ⟨QuotientGroup.mk' (sUnitImage F S), QuotientGroup.continuous_mk⟩)

/-- The S-idele class quasi-character acts by its zero extension at every
point of the additive S-adele space. -/
theorem exists_sLocalPolarFree_zeroExtendedClassQuasiCharacter_mulEquiv
    (χ : SIdeleQuotient F S →ₜ* ℂˣ) :
    ∃ M : P F S ≃L[ℂ] P F S, ∀ (f : P F S) (x : SAdeles F S),
      sLocalBruhatRestriction F S (M f).val.val x =
        if hx : IsUnit x then
          (χ (QuotientGroup.mk hx.unit) : ℂ) * sLocalBruhatRestriction F S f.val.val x
        else 0 := by
  obtain ⟨M, hM⟩ := exists_sLocalPolarFree_classQuasiCharacter_mulEquiv F S χ
  refine ⟨M, fun f x ↦ ?_⟩
  by_cases hx : IsUnit x
  · rw [dite_eq_left hx]
    have h := hM f hx.unit
    rwa [hx.unit_spec] at h
  · rw [dite_eq_right hx]
    exact ev_eq_zero_of_nonunit F S x (fun u hu ↦ hx ⟨u, hu⟩) (M f)

end

end Masullo
