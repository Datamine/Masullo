/-
The lattice quotient, divisible splitting, and elementary presentations adapt the
Apache-2.0 RiemannMasullo project at 3b4b2cd6915a243a5299a26001ca6b1c1a2ed037.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import TorusLocalCharts
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.ZMod

open Filter Function Module Set Topology TopologicalSpace
open scoped DirectSum

namespace Masullo

noncomputable section

universe u

/-- The product model for an elementary abelian Lie group. -/
abbrev ElementaryLCAModel (m n r : ℕ) (F : Type*) :=
  EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × F

/-- A discrete integral submodule of a finite-dimensional real normed space is the kernel of
an open quotient map to a product of a Euclidean space and a finite-dimensional torus. -/
theorem exists_euclidean_torus_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ (m n : ℕ) (q : E →+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ))),
      IsOpenQuotientMap q ∧ q.ker = L.toAddSubgroup := by
  classical
  let W := Submodule.span ℝ (L : Set E)
  let M : Submodule ℤ W := L.comap (W.subtype.restrictScalars ℤ)
  let toL : M → L := fun x ↦ ⟨x.val.val, x.property⟩
  have : DiscreteTopology M := DiscreteTopology.of_continuous_injective
    (f := toL) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    (fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun y : L ↦ (y : E)) h)))
  have hRange : (M : Set W) = range (L.inclusionSpan ℝ) := by
    ext x
    exact ⟨fun hx ↦ ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.property⟩
  have : IsZLattice ℝ M := ⟨hRange ▸ L.span_range_inclusionSpan ℝ⟩
  obtain ⟨V, hVW⟩ := W.exists_isCompl
  let m := finrank ℝ V
  let n := finrank ℤ M
  let b := (finBasis ℤ M).ofZLatticeBasis ℝ
  let eV : V ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (finBasis ℝ V).equivFun.toContinuousLinearEquiv.trans (EuclideanSpace.equiv _ ℝ).symm
  let eW : W ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let split := (V.prodEquivOfIsCompl W hVW.symm).toContinuousLinearEquiv
  let circle := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))
  let qW := AddMonoidHom.pi (fun i : Fin n ↦ circle.comp (Pi.evalAddMonoidHom (fun _ ↦ ℝ) i))
  have hCircle : IsOpenQuotientMap circle := QuotientAddGroup.isOpenQuotientMap_mk
  have hqW : IsOpenQuotientMap qW :=
    ⟨Function.Surjective.piMap (fun _ ↦ hCircle.surjective),
      continuous_pi (fun i ↦ hCircle.continuous.comp (continuous_apply i)),
      IsOpenMap.piMap (fun _ ↦ hCircle.isOpenMap) (Filter.Eventually.of_forall fun _ ↦
        hCircle.surjective)⟩
  let coords := split.symm.trans (ContinuousLinearEquiv.prodCongr eV eW)
  let q := ((AddMonoidHom.id _).prodMap qW).comp coords.toLinearEquiv.toAddEquiv.toAddMonoidHom
  refine ⟨m, n, q, ?_, ?_⟩
  · exact (IsOpenQuotientMap.id.prodMap hqW).comp coords.toHomeomorph.isOpenQuotientMap
  · have hW (w : W) : qW (eW w) = 0 ↔ w ∈ M := by
      rw [← (finBasis ℤ M).ofZLatticeBasis_span ℝ, b.mem_span_iff_repr_mem ℤ]
      rw [funext_iff]
      change (∀ i, ((b.repr w i : ℝ) : AddCircle (1 : ℝ)) = 0) ↔ _
      simp only [AddCircle.coe_eq_zero_iff, zsmul_one, Set.mem_range]
      rfl
    ext x
    change (eV (split.symm x).1, qW (eW (split.symm x).2)) = (0, 0) ↔ x ∈ L
    rw [Prod.mk.injEq, hW, ← eV.map_zero, eV.injective.eq_iff]
    constructor
    · rintro ⟨hV, hM⟩
      have hx := split.apply_symm_apply x
      change (split.symm x).1.val + (split.symm x).2.val = x at hx
      rw [hV, Submodule.coe_zero, zero_add] at hx
      exact hx ▸ hM
    · intro hx
      let w : W := ⟨x, Submodule.subset_span hx⟩
      have hsplit : split.symm x = (0, w) :=
        V.prodEquivOfIsCompl_symm_apply_right W hVW.symm w
      rw [hsplit]
      exact ⟨rfl, hx⟩

/-- An open divisible subgroup of an abelian topological group splits off as a
topological direct factor, with discrete complementary factor given by the quotient. -/
theorem exists_continuousAddEquiv_prod_quotient_of_open {A : Type*} [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] (H : AddSubgroup A)
    (hH : IsOpen (H : Set A)) [DivisibleBy H ℤ] :
    Nonempty (A ≃ₜ+ H × (A ⧸ H)) := by
  have := QuotientAddGroup.discreteTopology hH
  have := (Module.Baer.of_divisible H).injective
  obtain ⟨rₗ, hrₗ⟩ := Module.Injective.out H.subtype.toIntLinearMap
    Subtype.val_injective (LinearMap.id : H →ₗ[ℤ] H)
  let r := rₗ.toAddMonoidHom
  have hr (x : H) : r x.val = x := hrₗ x
  have hCont : Continuous r := by
    refine continuous_of_continuousAt_zero r (ContinuousOn.continuousAt ?_ (hH.mem_nhds H.zero_mem))
    rw [continuousOn_iff_continuous_domRestrict]
    have hId : (H : Set A).domRestrict r = id := funext hr
    rw [hId]
    exact continuous_id
  let s := QuotientAddGroup.lift H (AddMonoidHom.id A - H.subtype.comp r) (by
    intro x hx
    change x - (r x).val = 0
    rw [hr ⟨x, hx⟩, sub_self])
  have hs (x : A) : s (QuotientAddGroup.mk x) = x - (r x).val := rfl
  refine ⟨{
    toFun := fun x ↦ (r x, QuotientAddGroup.mk x)
    invFun := fun y ↦ y.1.val + s y.2
    left_inv := fun x ↦ by
      change (r x).val + s (QuotientAddGroup.mk x) = x
      rw [hs, add_comm, sub_add_cancel]
    right_inv := ?_
    map_add' := fun x y ↦ Prod.ext (map_add r x y) (map_add (QuotientAddGroup.mk' H) x y)
    continuous_toFun := hCont.prodMk QuotientAddGroup.continuous_mk
    continuous_invFun := (continuous_subtype_val.comp continuous_fst).add
      (continuous_of_discreteTopology.comp continuous_snd) }⟩
  rintro ⟨y, q⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  change (r (y.val + s (QuotientAddGroup.mk x)), (QuotientAddGroup.mk' H) _) = _
  rw [hs]
  apply Prod.ext
  · simp [map_add, map_sub, hr]
  · have hzero (z : H) : (QuotientAddGroup.mk' H) z.val = 0 :=
      (QuotientAddGroup.eq_zero_iff z.val).2 z.property
    change (QuotientAddGroup.mk' H) (y.val + (x - (r x).val)) = (QuotientAddGroup.mk' H) x
    simp only [map_add, map_sub, hzero, sub_zero, zero_add]

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

/-- Paper: (D.1.4.2), p. 757. A presentation identifies a group topologically
with a product of real, torus, free discrete and finite discrete abelian factors. -/
structure ElementaryLCAPresentation (G : Type*) [CommGroup G] [TopologicalSpace G] where
  realDim : ℕ
  torusDim : ℕ
  latticeRank : ℕ
  finiteFactor : Type
  [finiteGroup : AddCommGroup finiteFactor]
  [finiteFintype : Fintype finiteFactor]
  [finiteTopology : TopologicalSpace finiteFactor]
  [finiteDiscrete : DiscreteTopology finiteFactor]
  equiv : G ≃ₜ* Multiplicative (ElementaryLCAModel realDim torusDim latticeRank finiteFactor)

attribute [instance] ElementaryLCAPresentation.finiteGroup ElementaryLCAPresentation.finiteFintype
  ElementaryLCAPresentation.finiteTopology ElementaryLCAPresentation.finiteDiscrete


variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean LCA group is a product
of real and torus factors and a discrete abelian group. -/
theorem lca_equiv_real_torus_discrete (hG : IsLocallyEuclidean G) :
    ∃ (m n : ℕ) (D : Type u) (_ : AddCommGroup D) (_ : TopologicalSpace D)
      (_ : DiscreteTopology D),
      Nonempty (G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin m) ×
        (Fin n → AddCircle (1 : ℝ)) × D)) := by
  let A := Additive G
  have : T2Space A := ‹T2Space G›
  have : LocallyCompactSpace A := ‹LocallyCompactSpace G›
  let H := AddSubgroup.connectedComponentOfZero A
  obtain ⟨k, ⟨charts⟩⟩ := hG
  let : ChartedSpace (EuclideanSpace ℝ (Fin k)) A := charts
  have : LocallyConnectedSpace A := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin k)) A
  have hH : IsOpen (H : Set A) := isOpen_connectedComponent
  have : ConnectedSpace H := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : LocallyCompactSpace H := hH.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin k)) H :=
    TopologicalSpace.Opens.instChartedSpace (⟨H, hH⟩ : TopologicalSpace.Opens A)
  letI : T2Space (Multiplicative H) := inferInstanceAs (T2Space H)
  letI : LocallyCompactSpace (Multiplicative H) := inferInstanceAs (LocallyCompactSpace H)
  obtain ⟨d, F, hFc, hFo, hFk⟩ := exists_euclidean_openHom (G := Multiplicative H)
    ⟨k, ⟨inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin k)) H)⟩⟩
  let f : EuclideanSpace ℝ (Fin d) →+ H := F.toAdditive
  have hRange : IsOpen (f.range : Set H) := by
    rw [AddMonoidHom.coe_range, ← Set.image_univ]
    exact hFo _ isOpen_univ
  let U : OpenAddSubgroup H := ⟨f.range, hRange⟩
  have hSurj : Function.Surjective f := by
    have hTop := U.isClopen.eq_univ ⟨0, U.zero_mem⟩
    exact Set.range_eq_univ.mp (by
      change (f.range : Set H) = Set.univ at hTop
      simpa only [AddMonoidHom.coe_range] using hTop)
  have hF : IsOpenQuotientMap f := ⟨hSurj, hFc, hFo⟩
  have hKer : DiscreteTopology f.ker := hFk
  let : DivisibleBy H ℤ := divisibleByOfSMulRightSurj H ℤ (fun {z} hz y ↦ by
    obtain ⟨x, rfl⟩ := hSurj y
    have hzR : (z : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hz
    refine ⟨f ((z : ℝ)⁻¹ • x), ?_⟩
    change z • f ((z : ℝ)⁻¹ • x) = f x
    rw [← map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, mul_inv_cancel₀ hzR, one_smul])
  have : DiscreteTopology f.ker.toIntSubmodule := hKer
  -- Both quotient maps have the same kernel, so they induce a topological isomorphism.
  obtain ⟨m, n, q, hQ, hQker⟩ := exists_euclidean_torus_quotient f.ker.toIntSubmodule
  have hSameKer : f.ker = q.ker := hQker.symm
  let eF := QuotientAddGroup.quotientKerEquivOfSurjective f hF.surjective
  let eQ := QuotientAddGroup.quotientKerEquivOfSurjective q hQ.surjective
  let eKer := QuotientAddGroup.quotientAddEquivOfEq hSameKer
  let e := eF.symm.trans (eKer.trans eQ)
  have he (x : EuclideanSpace ℝ (Fin d)) : e (f x) = q x := by
    have hfmk : eF (QuotientAddGroup.mk x) = f x := rfl
    rw [← hfmk]
    change eQ (eKer (eF.symm (eF _))) = _
    rw [eF.symm_apply_apply]
    rfl
  have eH : H ≃ₜ+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) :=
    { e with
      continuous_toFun := hF.continuous_comp_iff.mp
        (show Continuous (e ∘ f) from (funext he : e ∘ f = q) ▸ hQ.continuous)
      continuous_invFun := hQ.continuous_comp_iff.mp
        (show Continuous (e.symm ∘ q) from
          (funext fun x ↦ e.symm_apply_eq.mpr (he x).symm : e.symm ∘ q = f) ▸ hF.continuous) }
  obtain ⟨split⟩ := exists_continuousAddEquiv_prod_quotient_of_open H hH
  let D := A ⧸ H
  have : DiscreteTopology D := QuotientAddGroup.discreteTopology hH
  let product := split.toAddEquiv.trans (AddEquiv.prodCongr eH.toAddEquiv (AddEquiv.refl D))
  let assoc := Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ)) D
  refine ⟨m, n, D, inferInstance, inferInstance, inferInstance, ⟨{
    AddEquiv.toMultiplicativeRight (product.trans AddEquiv.prodAssoc) with
    continuous_toFun := assoc.continuous.comp
      ((eH.continuous_toFun.prodMap continuous_id).comp split.continuous_toFun)
    continuous_invFun := split.continuous_invFun.comp
      ((eH.continuous_invFun.prodMap continuous_id).comp assoc.symm.continuous) }⟩⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The real, torus and discrete factors of an elementary presentation give product charts. -/
private theorem locallyEuclidean_of_elementaryPresentation
    (e : ElementaryLCAPresentation G) : IsLocallyEuclidean G := by
  let R := Fin e.realDim → ℝ
  let T := ModelPi (fun _ : Fin e.torusDim ↦ ℝ)
  let D := (Fin e.latticeRank → ℤ) × e.finiteFactor
  let : ChartedSpace R (EuclideanSpace ℝ (Fin e.realDim)) :=
    (PiLp.homeomorph 2 (fun _ : Fin e.realDim ↦ ℝ)).symm.chartedSpace
  let : ChartedSpace ℝ (AddCircle (1 : ℝ)) :=
    (AddCircle.isLocalHomeomorph_coe (1 : ℝ)).chartedSpace QuotientAddGroup.mk_surjective
  let : ChartedSpace PUnit.{1} D := ChartedSpace.ofDiscreteTopology
  let M := ModelProd R (ModelProd T PUnit.{1})
  let charts : ChartedSpace M
      (ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    prodChartedSpace _ _ _ _
  let : ChartedSpace M
      (Multiplicative (ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor)) := charts
  let : ChartedSpace M G := e.equiv.toHomeomorph.symm.chartedSpace
  let h : M ≃ₜ EuclideanSpace ℝ (Fin (e.realDim + e.torusDim)) :=
    (Homeomorph.prodCongr (Homeomorph.refl R) (Homeomorph.prodUnique T PUnit)).trans
      ((Fin.appendHomeomorph e.realDim e.torusDim).trans (PiLp.homeomorph 2 _).symm)
  let : ChartedSpace (EuclideanSpace ℝ (Fin (e.realDim + e.torusDim))) M := h.symm.chartedSpace
  exact ⟨e.realDim + e.torusDim, ⟨ChartedSpace.comp _ M G⟩⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- An elementary presentation gives a compact generating neighborhood. -/
private theorem compactlyGenerated_of_elementaryPresentation
    (e : ElementaryLCAPresentation G) : IsCompactlyGeneratedGroup G := by
  let R := EuclideanSpace ℝ (Fin e.realDim)
  let T := Fin e.torusDim → AddCircle (1 : ℝ)
  let D := (Fin e.latticeRank → ℤ) × e.finiteFactor
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (0 : R)
  have hKgen : AddSubgroup.closure K = ⊤ := by
    let H := AddSubgroup.closure K
    have hH := H.isOpen_of_mem_nhds (mem_of_superset hKnhds AddSubgroup.subset_closure)
    exact SetLike.coe_injective ((OpenAddSubgroup.mk H hH).isClopen.eq_univ ⟨0, H.zero_mem⟩)
  obtain ⟨S, hSgen, hS⟩ := AddGroup.fg_iff.mp (inferInstance : AddGroup.FG D)
  let U : Set (ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    K ×ˢ ((univ : Set T) ×ˢ insert 0 S)
  have hD : insert 0 S ∈ 𝓝 (0 : D) := (isOpen_discrete _).mem_nhds (mem_insert _ _)
  have hU : U ∈ 𝓝 0 := prod_mem_nhds hKnhds (prod_mem_nhds univ_mem hD)
  have hUc : IsCompact U := hK.prod (isCompact_univ.prod (hS.insert 0).isCompact)
  have hUgen : AddSubgroup.closure U = ⊤ := by
    change AddSubgroup.closure (K ×ˢ ((univ : Set T) ×ˢ insert 0 S)) = ⊤
    rw [AddSubgroup.closure_prod (mem_of_mem_nhds hKnhds) (by simp),
      AddSubgroup.closure_prod (mem_univ (0 : T)) (mem_insert 0 S), hKgen,
      AddSubgroup.closure_univ, AddSubgroup.closure_insert_zero, hSgen,
      AddSubgroup.top_prod_top, AddSubgroup.top_prod_top]
  let f := e.equiv.symm.toMulEquiv.toMonoidHom
  let V : Set (Multiplicative (ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor)) :=
    Multiplicative.toAdd ⁻¹' U
  have hV : V ∈ 𝓝 1 := hU
  refine ⟨f '' V, ?_, hUc.image e.equiv.symm.continuous, ?_⟩
  · have h := e.equiv.symm.toHomeomorph.isOpenMap.image_mem_nhds hV
    change f '' V ∈ 𝓝 (f 1) at h
    rwa [map_one] at h
  · have hVgen : Subgroup.closure V = ⊤ := by
      rw [← AddSubgroup.toSubgroup_closure, hUgen]
      rfl
    rw [← MonoidHom.map_closure, hVgen,
      Subgroup.map_top_of_surjective f e.equiv.symm.surjective]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- In a real–torus–discrete decomposition of a compactly generated group, the discrete
factor is finitely generated and splits as a free abelian group times a finite group. -/
private theorem elementaryPresentation_of_compactlyGenerated
    {m n : ℕ} {D : Type*} [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D]
    (hG : IsCompactlyGeneratedGroup G)
    (e : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) × D)) :
    Nonempty (ElementaryLCAPresentation G) := by
  classical
  obtain ⟨U, _, hUc, hUgen⟩ := hG
  let R := EuclideanSpace ℝ (Fin m)
  let T := Fin n → AddCircle (1 : ℝ)
  let eA := MulEquiv.toAdditiveLeft e.toMulEquiv
  let p := ((AddMonoidHom.snd T D).comp (AddMonoidHom.snd R (T × D))).comp eA.toAddMonoidHom
  have hp : Function.Surjective p := fun d ↦
    ⟨eA.symm (0, 0, d), congrArg (fun a : R × T × D ↦ a.2.2) (eA.apply_symm_apply _)⟩
  have hpc : Continuous p := (continuous_snd.comp continuous_snd).comp e.continuous
  let V : Set (Additive G) := Additive.toMul ⁻¹' U
  have hVgen : AddSubgroup.closure V = ⊤ := by
    rw [← Subgroup.toAddSubgroup_closure, hUgen]
    rfl
  have : AddGroup.FG D := AddGroup.fg_iff.mpr
    ⟨p '' V, by
      rw [← AddMonoidHom.map_closure, hVgen,
        AddSubgroup.map_top_of_surjective p hp],
      (hUc.image hpc).finite DiscreteTopology.isDiscrete⟩
  obtain ⟨r, ι, _, q, hq, k, ⟨d⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod D
  let F := (i : ι) → ZMod (q i ^ k i)
  let (i : ι) : NeZero (q i ^ k i) := ⟨pow_ne_zero _ (hq i).ne_zero⟩
  let : Fintype F := inferInstanceAs (Fintype ((i : ι) → ZMod (q i ^ k i)))
  let : TopologicalSpace F := ⊥
  let : DiscreteTopology F := ⟨rfl⟩
  let d' : D ≃+ (Fin r → ℤ) × F :=
    d.trans (AddEquiv.prodCongr Finsupp.addEquivFunOnFinite (DirectSum.addEquivProd _))
  let e' := AddEquiv.toMultiplicativeRight
    (eA.trans (AddEquiv.prodCongr (AddEquiv.refl R) (AddEquiv.prodCongr (AddEquiv.refl T) d')))
  refine ⟨{ realDim := m, torusDim := n, latticeRank := r, finiteFactor := F
            equiv := ?_ }⟩
  exact { e' with
    continuous_toFun := (continuous_id.prodMap
      (continuous_id.prodMap (continuous_of_discreteTopology (f := d')))).comp e.continuous
    continuous_invFun := e.symm.continuous.comp (continuous_id.prodMap
      (continuous_id.prodMap (continuous_of_discreteTopology (f := d'.symm)))) }

/-- Paper: Theorem D.1.4.3(2), p. 757. An LCA group has an elementary presentation
exactly when it is compactly generated and locally Euclidean. -/
theorem lca_elementary_iff :
    (IsCompactlyGeneratedGroup G ∧ IsLocallyEuclidean G) ↔
      Nonempty (ElementaryLCAPresentation G) := by
  constructor
  · rintro ⟨hCompact, hEuclidean⟩
    obtain ⟨m, n, D, _, _, _, ⟨e⟩⟩ := lca_equiv_real_torus_discrete hEuclidean
    exact elementaryPresentation_of_compactlyGenerated hCompact e
  · rintro ⟨e⟩
    exact ⟨compactlyGenerated_of_elementaryPresentation e,
      locallyEuclidean_of_elementaryPresentation e⟩

omit [T2Space G] [LocallyCompactSpace G] in
/-- In the elementary model the connected component quotient is the discrete
lattice times the finite factor. -/
theorem ElementaryLCAPresentation.componentGroup_fg (e : ElementaryLCAPresentation G) :
    Group.FG (G ⧸ Subgroup.connectedComponentOfOne G) := by
  let R := EuclideanSpace ℝ (Fin e.realDim)
  let T := Fin e.torusDim → AddCircle (1 : ℝ)
  let D := (Fin e.latticeRank → ℤ) × e.finiteFactor
  let p₀ : R × T × D →+ D :=
    (AddMonoidHom.snd T D).comp (AddMonoidHom.snd R (T × D))
  let p := p₀.toMultiplicative.comp e.equiv.toMulEquiv.toMonoidHom
  have hp : Continuous p := (continuous_snd.comp continuous_snd).comp e.equiv.continuous
  have hpSurj : Surjective p := by
    intro d
    refine ⟨e.equiv.symm (Multiplicative.ofAdd (0, 0, d.toAdd)), ?_⟩
    change p₀.toMultiplicative (e.equiv (e.equiv.symm _)) = _
    rw [e.equiv.apply_symm_apply]
    rfl
  let q : R × T → G := fun v ↦ e.equiv.symm (Multiplicative.ofAdd (v.1, v.2, (0 : D)))
  have hq : Continuous q :=
    e.equiv.symm.continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  have hq0 : q 0 = 1 := map_one e.equiv.symm
  have hKer : p.ker = Subgroup.connectedComponentOfOne G := by
    ext x
    change p x = 1 ↔ x ∈ connectedComponent (1 : G)
    constructor
    · intro hx
      let v : R × T × D := (e.equiv x).toAdd
      have hv : v.2.2 = 0 := hx
      have hEq : (v.1, v.2.1, (0 : D)) = v := Prod.ext rfl (Prod.ext rfl hv.symm)
      have hqv : q (v.1, v.2.1) = x := by
        change e.equiv.symm (Multiplicative.ofAdd (v.1, v.2.1, (0 : D))) = x
        rw [hEq]
        exact e.equiv.symm_apply_apply x
      have h := hq.mapsTo_connectedComponent (0 : R × T)
      rw [PreconnectedSpace.connectedComponent_eq_univ, hq0] at h
      exact hqv ▸ h (mem_univ (v.1, v.2.1))
    · intro hx
      have h := hp.image_connectedComponent_eq_singleton (1 : G)
      have hy : p x ∈ p '' connectedComponent (1 : G) := mem_image_of_mem p hx
      rw [h, map_one] at hy
      exact mem_singleton_iff.mp hy
  let iso := (QuotientGroup.quotientMulEquivOfEq hKer.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective p hpSurj)
  letI : Group.FG (Multiplicative D) :=
    AddGroup.fg_iff_mul_fg.mp (inferInstanceAs (AddGroup.FG D))
  exact Group.fg_of_surjective (f := iso.symm.toMonoidHom) iso.symm.surjective

/-- Evaluation on an open subgroup of the dual is an open quotient map. -/
private theorem exists_open_evaluation_on_dualSubgroup (H : Subgroup (PontryaginDual G))
    (hH : IsOpen (H : Set (PontryaginDual G))) :
    ∃ f : G →ₜ* PontryaginDual H, IsOpenQuotientMap f ∧
      ∀ x (χ : H), f x χ = χ.val x := by
  obtain ⟨b, hb⟩ := pontryaginDual_bidual (G := G)
  obtain ⟨e, he⟩ := lcaDualQuotient_equiv_subgroupDual H (H.isClosed_of_isOpen hH)
  let q : PontryaginDual (PontryaginDual G) →ₜ* _ :=
    ⟨QuotientGroup.mk' (lcaAnnihilator H), QuotientGroup.continuous_mk⟩
  let f := (ContinuousMonoidHom.toContinuousMonoidHom e).comp
    (q.comp (ContinuousMonoidHom.toContinuousMonoidHom b))
  exact ⟨f, e.toHomeomorph.isOpenQuotientMap.comp
    (QuotientGroup.isOpenQuotientMap_mk.comp b.toHomeomorph.isOpenQuotientMap),
    fun x χ ↦ (he (b x) χ).trans (hb x χ.val)⟩

/-- Every quotient occurring in the inverse system of an open compactly generated
subgroup admits an elementary presentation. -/
theorem lca_openSubgroup_quotient_elementary (J : OpenCompactlyGeneratedSubgroups G)
    (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :
    Nonempty (ElementaryLCAPresentation
      (J.val ⧸ (lcaDualAnnihilator H.val).comap J.val.subtype)) := by
  letI : LocallyCompactSpace J.val := J.property.1.locallyCompactSpace
  letI : LocallyCompactSpace H.val := H.property.1.locallyCompactSpace
  obtain ⟨f, hf, hEval⟩ := exists_open_evaluation_on_dualSubgroup H.val H.property.1
  let g : J.val →ₜ* PontryaginDual H.val := f.comp ⟨J.val.subtype, continuous_subtype_val⟩
  have hg : IsOpenMap g := hf.isOpenMap.comp J.property.1.isOpenEmbedding_subtypeVal.isOpenMap
  let K := (lcaDualAnnihilator H.val).comap J.val.subtype
  let S := g.toMonoidHom.range
  have hS : IsOpen (S : Set (PontryaginDual H.val)) := by
    rw [MonoidHom.coe_range, ← Set.image_univ]
    exact hg _ isOpen_univ
  let r : J.val →* S := g.toMonoidHom.rangeRestrict
  have hr : IsOpenQuotientMap r :=
    ⟨fun ⟨x, y, h⟩ ↦ ⟨y, Subtype.ext h⟩,
     g.continuous.subtype_mk _, hg.codRestrict _⟩
  have hKer : r.ker = K := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, mem_lcaDualAnnihilator_iff]
    constructor
    · intro h χ
      exact (hEval x.val χ).symm.trans (congrArg (fun y : S ↦ y.val χ) h)
    · intro h
      apply Subtype.ext
      exact PontryaginDual.ext fun χ ↦ (hEval x.val χ).trans (h χ)
  let e₀ := (QuotientGroup.quotientMulEquivOfEq hKer.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective r hr.surjective)
  have hcomp : (fun x : J.val ↦ e₀ (QuotientGroup.mk x)) = r := by
    funext x
    exact rfl
  let e : (J.val ⧸ K) ≃ₜ* S := e₀.toContinuousMulEquiv fun U ↦ by
    rw [← (QuotientGroup.isQuotientMap_mk K).isCoinducing.isOpen_preimage, preimage_preimage, hcomp]
    exact hr.isQuotientMap.isCoinducing.isOpen_preimage
  have hK : IsClosed (K : Set J.val) := by
    rw [← hKer]
    exact isClosed_eq hr.continuous continuous_const
  letI : T1Space (J.val ⧸ K) := QuotientGroup.t1Space_iff.mpr hK
  letI : LocallyCompactSpace (J.val ⧸ K) :=
    (QuotientGroup.isOpenQuotientMap_mk (N := K)).locallyCompactSpace
  obtain ⟨d, ⟨charts⟩⟩ := isLocallyEuclidean_dual_of_compactlyGenerated H.property.2
  letI : ChartedSpace (EuclideanSpace ℝ (Fin d)) (PontryaginDual H.val) := charts
  letI : ChartedSpace (EuclideanSpace ℝ (Fin d)) S :=
    TopologicalSpace.Opens.instChartedSpace (⟨S, hS⟩ : TopologicalSpace.Opens (PontryaginDual H.val))
  exact lca_elementary_iff.mp
    ⟨isCompactlyGeneratedGroup_quotient J.property.2 K hK,
      ⟨d, ⟨e.toHomeomorph.symm.chartedSpace⟩⟩⟩

/-- Corrected D.1.4.7. The canonical inverse limit uses elementary groups with
finitely generated component groups. Its topology is the compatible-family subspace topology. -/
theorem lca_openSubgroup_elementaryInverseLimit (J : OpenCompactlyGeneratedSubgroups G) :
    let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
      lcaDualAnnihilator H.val ≤ J.val}
    let K (H : I) := (lcaDualAnnihilator H.val.val).comap J.val.subtype
    let Q (H : I) := J.val ⧸ K H
    let δ : J.val → (H : I) → Q H := fun x _ ↦ QuotientGroup.mk x
    Nonempty I ∧ IsDirectedOrder I ∧
      (∀ H : I, Nonempty (ElementaryLCAPresentation (Q H)) ∧
        Group.FG (Q H ⧸ Subgroup.connectedComponentOfOne (Q H))) ∧
      ∃ (B : Subgroup ((H : I) → Q H)) (e : J.val ≃ₜ* B),
        (B : Set ((H : I) → Q H)) = {a | ∀ H H' : I, H ≤ H' →
          ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'} ∧
        ∀ x H, (e x).val H = δ x H := by
  let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
    lcaDualAnnihilator H.val ≤ J.val}
  let K (H : I) := (lcaDualAnnihilator H.val.val).comap J.val.subtype
  let Q (H : I) := J.val ⧸ K H
  let δ : J.val →ₜ* ((H : I) → Q H) :=
    { toFun := fun x _ ↦ QuotientGroup.mk x
      map_one' := funext fun H ↦ QuotientGroup.mk_one (N := K H)
      map_mul' := fun x y ↦ funext fun H ↦ QuotientGroup.mk_mul (K H) x y
      continuous_toFun := continuous_pi fun H ↦ QuotientGroup.continuous_mk }
  obtain ⟨hI, hDirected, hEmb, hRange⟩ := lca_openSubgroup_inverseLimit J
  let B := δ.toMonoidHom.range
  let f : J.val →ₜ* B := ⟨δ.toMonoidHom.rangeRestrict, δ.continuous.subtype_mk _⟩
  have hf : IsEmbedding f := hEmb.codRestrict B (fun x ↦ ⟨x, rfl⟩)
  have hSurj : Function.Surjective f := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  let e := MulEquiv.ofBijective f.toMonoidHom ⟨hf.injective, hSurj⟩
  have hOpen := hf.isInducing.isOpenMap (by rw [hSurj.range_eq]; exact isOpen_univ)
  have hQ (H : I) : Nonempty (ElementaryLCAPresentation (Q H)) ∧
      Group.FG (Q H ⧸ Subgroup.connectedComponentOfOne (Q H)) := by
    obtain ⟨p⟩ := lca_openSubgroup_quotient_elementary J H.val
    exact ⟨⟨p⟩, p.componentGroup_fg⟩
  exact ⟨hI, hDirected, hQ, B,
    e.toContinuousMulEquiv (fun _ ↦
      (hOpen.isQuotientMap f.continuous hSurj).isCoinducing.isOpen_preimage), hRange,
    fun _ _ ↦ rfl⟩

/-- The identifications with the inverse limits transport the open-subgroup
colimit. Its inclusions are open embeddings, and the topology is final. -/
theorem lca_elementaryInverseLimits_colimit
    {L : OpenCompactlyGeneratedSubgroups G → Type*}
    [∀ J, CommGroup (L J)] [∀ J, TopologicalSpace (L J)]
    (e : ∀ J, J.val ≃ₜ* L J) :
    let j (J : OpenCompactlyGeneratedSubgroups G) (y : L J) : G := (e J).symm y
    let transition (J K : OpenCompactlyGeneratedSubgroups G) (h : J ≤ K) (y : L J) : L K :=
      e K (Subgroup.inclusion h ((e J).symm y))
    IsDirectedOrder (OpenCompactlyGeneratedSubgroups G) ∧
      (∀ J, IsOpenEmbedding (j J)) ∧
      (∀ J K h, IsOpenEmbedding (transition J K h) ∧ j K ∘ transition J K h = j J) ∧
      (∀ x : G, ∃ J y, j J y = x) ∧
      (∀ U : Set G, IsOpen U ↔ ∀ J, IsOpen (j J ⁻¹' U)) := by
  let I := OpenCompactlyGeneratedSubgroups G
  let j (J : I) (y : L J) : G := (e J).symm y
  let transition (J K : I) (h : J ≤ K) (y : L J) : L K :=
    e K (Subgroup.inclusion h ((e J).symm y))
  obtain ⟨hDir, hCover, hFinal⟩ := openCompactlyGeneratedSubgroups_colimit (G := G)
  have hInc (J : I) : IsOpenEmbedding (j J) :=
    J.property.1.isOpenEmbedding_subtypeVal.comp (e J).symm.toHomeomorph.isOpenEmbedding
  refine ⟨hDir, hInc, ?_, ?_, ?_⟩
  · intro J K h
    let i : J.val → K.val := Subgroup.inclusion h
    have hi : IsOpenEmbedding i := .of_continuous_injective_isOpenMap
      (continuous_subtype_val.subtype_mk _)
      (fun _ _ hij ↦ Subtype.ext (congrArg (fun z : K.val ↦ (z : G)) hij))
      (J.property.1.isOpenEmbedding_subtypeVal.isOpenMap.codRestrict (fun x ↦ h x.property))
    refine ⟨(e K).toHomeomorph.isOpenEmbedding.comp
      (hi.comp (e J).symm.toHomeomorph.isOpenEmbedding), ?_⟩
    funext y
    show ((e K).symm (e K (i ((e J).symm y))) : G) = ((e J).symm y : G)
    rw [ContinuousMulEquiv.symm_apply_apply]
    rfl
  · intro x
    obtain ⟨J, hx⟩ := hCover x
    exact ⟨J, e J ⟨x, hx⟩, congrArg Subtype.val ((e J).symm_apply_apply ⟨x, hx⟩)⟩
  · intro U
    rw [hFinal U]
    apply forall_congr'
    intro J
    exact (e J).symm.toHomeomorph.isQuotientMap.isCoinducing.isOpen_preimage.symm

end
end Masullo
