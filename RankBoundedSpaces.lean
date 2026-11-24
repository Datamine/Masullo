import SmallSpaces
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.FixedPoint

open Cardinal CategoryTheory CategoryTheory.Limits Function Order Set Topology TopologicalSpace
open scoped Cardinal Ordinal

namespace Masullo

universe u

/-- The carriers from the von Neumann stage, shrunk to the carrier universe. -/
abbrev RankCarrier (α : Ordinal.{u}) := Shrink.{u} (ZFSet.vonNeumann α)

noncomputable def rankCarrierCode {α : Ordinal.{u}} (x : RankCarrier α) : ZFSet.{u} :=
  ((equivShrink (ZFSet.vonNeumann α)).symm x).val

/-- An actual set of CGWH objects on the carriers in (V_α). -/
structure RankSpace (α : Ordinal.{u}) where
  code : RankCarrier α
  topology : TopologicalSpace (Shrink.{u} (rankCarrierCode code))
  cg : @CompactlyGeneratedSpace _ topology
  wh : @WeaklyHausdorff _ topology

def RankSpace.space {α : Ordinal.{u}} (X : RankSpace α) : CGWH.{u} :=
  @CGWH.of _ X.topology X.cg X.wh

instance {α : Ordinal.{u}} : Category.{u} (RankSpace α) := inferInstanceAs (Category (InducedCategory CGWH.{u} (@RankSpace.space α)))

abbrev rankSpaceInclusion (α : Ordinal.{u}) : RankSpace α ⥤ CGWH.{u} :=
  inducedFunctor RankSpace.space

def rankSpaceInclusionFullyFaithful (α : Ordinal.{u}) :
    (rankSpaceInclusion α).FullyFaithful :=
  fullyFaithfulInducedFunctor (@RankSpace.space α)

instance (α : Ordinal.{u}) : (rankSpaceInclusion α).Full :=
  (rankSpaceInclusionFullyFaithful α).full

instance (α : Ordinal.{u}) : (rankSpaceInclusion α).Faithful :=
  (rankSpaceInclusionFullyFaithful α).faithful

private theorem mk_shrink_zfset (s : ZFSet.{u}) : #(Shrink.{u} s) = ZFSet.card s := by
  apply Cardinal.lift_inj.mp
  rw [← ZFSet.cardinalMk_coe_sort]
  rw [← Cardinal.lift_id'.{u, u + 1} (#↥s)]
  exact Cardinal.lift_mk_shrink' ↥s

theorem RankSpace.code_mem {α : Ordinal.{u}} (X : RankSpace α) :
    rankCarrierCode X.code ∈ ZFSet.vonNeumann α :=
  ((equivShrink (ZFSet.vonNeumann α)).symm X.code).property

theorem RankSpace.carrier_lt {α : Ordinal.{u}}
    (X : RankSpace α) : #((X.space.obj : Type u)) < preBeth α := by
  have hr : ZFSet.rank (rankCarrierCode X.code) < α :=
    ZFSet.mem_vonNeumann.mp X.code_mem
  change #(Shrink.{u} (rankCarrierCode X.code)) < preBeth α
  rw [mk_shrink_zfset]
  calc
    _ ≤ ZFSet.card (ZFSet.vonNeumann (rankCarrierCode X.code).rank) :=
      ZFSet.card_mono (ZFSet.subset_vonNeumann.mpr le_rfl)
    _ < _ := by rw [ZFSet.card_vonNeumann]; exact preBeth_strictMono hr

private def rankInducedHomeo {Y : Type u} (X : CGWH.{u}) (e : Y ≃ X.obj) :
    @Homeomorph Y X.obj (TopologicalSpace.induced e inferInstance) inferInstance := by
  letI : TopologicalSpace Y := TopologicalSpace.induced e inferInstance
  exact ⟨e, continuous_induced_dom, continuous_induced_rng.mpr <| by
    have h : (e : Y → X.obj) ∘ e.symm = id := funext e.apply_symm_apply
    change Continuous ((e : Y → X.obj) ∘ e.symm)
    rw [h]
    exact continuous_id⟩

private noncomputable def rankSpaceOn {α : Ordinal.{u}} (X : CGWH.{u})
    (c : RankCarrier α) (e : Shrink.{u} (rankCarrierCode c) ≃ X.obj) : RankSpace α := by
  let t := TopologicalSpace.induced e inferInstance
  letI := t
  let h := rankInducedHomeo X e
  refine ⟨c, t, ?_, ?_⟩
  · exact compactlyGeneratedSpace_of_coinduced h.symm.continuous h.symm.isQuotientMap.isCoinducing.eq_coinduced
  · intro K f
    have hc := X.property K ⟨h ∘ f, h.continuous.comp f.continuous⟩
    change IsClosed (range (h ∘ f)) at hc
    rw [range_comp] at hc
    have he : h ⁻¹' (h '' range f) = range f := preimage_image_eq _ h.injective
    exact he ▸ hc.preimage h.continuous

private noncomputable def rankSpaceOnHomeo {α : Ordinal.{u}} (X : CGWH.{u})
    (c : RankCarrier α) (e : Shrink.{u} (rankCarrierCode c) ≃ X.obj) :
    (rankSpaceOn X c e).space.obj ≃ₜ X.obj :=
  rankInducedHomeo X e

private theorem rankSpaceOn_set {α : Ordinal.{u}} (X : CGWH.{u}) (s : ZFSet.{u})
    (hs : s ∈ ZFSet.vonNeumann α) (hc : ZFSet.card s = #(X.obj : Type u)) :
    ∃ Y : RankSpace α, rankCarrierCode Y.code = s ∧ Nonempty (Y.space.obj ≃ₜ X.obj) := by
  let c : RankCarrier α := equivShrink _ ⟨s, hs⟩
  have h : rankCarrierCode c = s := by
    unfold rankCarrierCode c
    rw [Equiv.symm_apply_apply]
  have he : #(Shrink.{u} (rankCarrierCode c)) = #(X.obj : Type u) := by
    rw [mk_shrink_zfset, h, hc]
  let e := (Cardinal.eq.mp he).some
  exact ⟨rankSpaceOn X c e, h, ⟨rankSpaceOnHomeo X c e⟩⟩

theorem rankSpace_representative {α : Ordinal.{u}} (hα : preBeth α = α.card)
    (X : CGWH.{u}) (hX : #(X.obj : Type u) < preBeth α) :
    ∃ Y : RankSpace α, Nonempty (Y.space.obj ≃ₜ X.obj) := by
  let κ := #(X.obj : Type u)
  have hX' : κ < α.card := hα ▸ hX
  have h : κ.ord < α := (ord_lt_ord.mpr hX').trans_le (Cardinal.ord_card_le α)
  have hz : κ.ord.toZFSet ∈ ZFSet.vonNeumann α := by
    rw [ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet]
    exact h
  obtain ⟨Y, _, he⟩ := rankSpaceOn_set X _ hz (by rw [Ordinal.card_toZFSet, card_ord])
  exact ⟨Y, he⟩

private theorem strongLimit_power {κ : Cardinal.{u}} (h : κ.IsStrongLimit)
    (hω : ℵ₀ ≤ κ) {a b : Cardinal.{u}} (ha : a < κ) (hb : b < κ) : a ^ b < κ := by
  calc
    a ^ b ≤ (2 ^ a) ^ b := power_le_power_right (cantor a).le
    _ = 2 ^ (a * b) := (power_mul ..).symm
    _ < κ := h.isStrongPrelimit (mul_lt_of_lt hω ha hb)

private theorem rankSpace_bound_lt {κ τ : Cardinal.{u}} (h : κ.IsStrongLimit)
    (hω : ℵ₀ < κ) (ht : τ < κ) : smallSpaceBound τ < κ :=
  max_lt (strongLimit_power h hω.le ht hω)
    (max_lt (h.isStrongPrelimit (h.isStrongPrelimit ht)) (strongLimit_power h hω.le ht ht))

private theorem exists_rank_stage (β : Ordinal.{u}) {ν : Cardinal.{u}} (hν : ℵ₀ ≤ ν) :
    ∃ α : Ordinal.{u}, β ≤ α ∧ IsSuccLimit α ∧
      preBeth α = α.card ∧ ν < α.cof := by
  let f : Ordinal.{u} → Ordinal.{u} := fun o => (preBeth o).ord
  have hf : Order.IsNormal f := isNormal_ord.comp isNormal_preBeth
  let δ := (Order.succ ν).ord
  have hd : IsSuccLimit δ := Cardinal.isSuccLimit_ord (hν.trans (Order.le_succ ν))
  let b := β + δ
  have hb : IsSuccLimit b := Ordinal.isSuccLimit_add β hd
  let α := Ordinal.deriv f b
  have hc : α.cof = Order.succ ν := by
    rw [Ordinal.cof_map_of_isNormal (Ordinal.isNormal_deriv f) hb,
      Ordinal.cof_add β hd.ne_zero, (isRegular_succ hν).cof_ord]
  have he : f α = α := Ordinal.deriv_fp hf b
  have hα : IsSuccLimit α := Ordinal.one_lt_cof_iff.mp (by
    rw [hc]
    exact (Cardinal.one_lt_aleph0.trans_le hν).trans (Order.lt_succ ν))
  refine ⟨α, (le_self_add).trans ((Ordinal.isNormal_deriv f).strictMono.le_apply (x := b)),
    hα, ?_, ?_⟩
  · exact (card_ord (preBeth α)).symm.trans (congrArg Ordinal.card he)
  · rw [hc]
    exact Order.lt_succ ν

private theorem cgwhLimit_card {J : Type u} [SmallCategory J] (P : J ⥤ CGWH.{u}) :
    #((cgwhLimit P).cone.pt.obj : Type u) ≤ #(∀ j, ((P.obj j).obj : Type u)) :=
  mk_le_of_injective (f := fun x j => ((cgwhLimit P).cone.π.app j).hom x)
    (fun x y h => topologicalLimit_jointly_injective
      ((P ⋙ cgwhForget) ⋙ CompactlyGenerated.compactlyGeneratedToTop) x y (congrFun h))

private theorem cgwhColimit_card {J : Type u} [SmallCategory J] (P : J ⥤ CGWH.{u}) :
    #((cgwhColimit P).cocone.pt.obj : Type u) ≤ #(Σ j, ((P.obj j).obj : Type u)) := by
  let Q := (P ⋙ cgwhForget) ⋙ CompactlyGenerated.compactlyGeneratedToTop
  let X := (kelleyColimit (P ⋙ cgwhForget)).cocone.pt
  let q := weakHausdorffAdjunction.unit.app X
  have hq := (weakHausdorffUnit_isQuotientMap X).surjective
  let f : (Σ j, ((P.obj j).obj : Type u)) → ((colimit Q : TopCat.{u}) : Type u) :=
    fun x => colimit.ι Q x.1 x.2
  have hf : Surjective f := by
    intro x
    obtain ⟨j, y, h⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget TopCat.{u}) (colimit.isColimit Q)) x
    exact ⟨⟨j, y⟩, h⟩
  exact mk_le_of_surjective (hq.comp hf)

theorem rank_cardinal_properties {α : Ordinal.{u}} {ν : Cardinal.{u}}
    (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof) :
    (preBeth α).IsStrongLimit ∧ ℵ₀ < preBeth α ∧ (preBeth α).ord = α := by
  have hsl := isStrongLimit_preBeth.mpr hα
  have hω : ℵ₀ < preBeth α := hcard.symm ▸ ((hν.trans_lt hc).trans_le (Ordinal.cof_le_card α))
  have he : (preBeth α).ord = α := by
    apply le_antisymm
    · rw [hcard]
      exact Cardinal.ord_card_le α
    · exact (Cardinal.ord_strictMono.comp preBeth_strictMono).le_apply
  exact ⟨hsl, hω, he⟩

private theorem rank_diagram_size {α : Ordinal.{u}} {ν : Cardinal.{u}}
    (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof)
    {J : Type u} [SmallCategory J] (hJ : #J ≤ ν) (P : J ⥤ RankSpace α) :
    #((cgwhLimit (P ⋙ rankSpaceInclusion α)).cone.pt.obj : Type u) < preBeth α ∧
      #((cgwhColimit (P ⋙ rankSpaceInclusion α)).cocone.pt.obj : Type u) < preBeth α := by
  obtain ⟨hsl, hω, he⟩ := rank_cardinal_properties hα hcard hν hc
  let a (j : J) := #((P.obj j).space.obj : Type u)
  let b := ⨆ j, a j
  have hj : #J < (preBeth α).ord.cof := by rw [he]; exact hJ.trans_lt hc
  have hb : b < preBeth α :=
    Cardinal.iSup_lt_of_lt_cof_ord hj (fun j => (P.obj j).carrier_lt)
  have hle (j : J) : a j ≤ b := le_ciSup
    ⟨preBeth α, forall_mem_range.mpr fun j => (P.obj j).carrier_lt.le⟩ j
  have hJ' : #J < preBeth α := hj.trans_le (by simpa using Ordinal.cof_le_card (preBeth α).ord)
  constructor
  · apply (cgwhLimit_card _).trans_lt
    rw [Cardinal.mk_pi]
    refine (Cardinal.prod_le_prod a (fun _ => b) hle).trans_lt ?_
    rw [prod_const']
    exact strongLimit_power hsl hω.le hb hJ'
  · apply (cgwhColimit_card _).trans_lt
    rw [Cardinal.mk_sigma]
    exact (sum_le_mk_mul_iSup a).trans_lt (mul_lt_of_lt hω.le hJ' hb)

def cgwhIsoOfHomeo {X Y : CGWH.{u}} (e : X.obj ≃ₜ Y.obj) : X ≅ Y where
  hom := CGWH.map ⟨e, e.continuous⟩
  inv := CGWH.map ⟨e.symm, e.symm.continuous⟩
  hom_inv_id := cgwhForget.map_injective (ConcreteCategory.hom_ext _ _ e.symm_apply_apply)
  inv_hom_id := cgwhForget.map_injective (ConcreteCategory.hom_ext _ _ e.apply_symm_apply)

private theorem rank_limit_colimit {α : Ordinal.{u}} {ν : Cardinal.{u}}
    (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof)
    {J : Type u} [SmallCategory J] (hJ : #J ≤ ν) (P : J ⥤ RankSpace α) :
    HasLimit P ∧ HasColimit P ∧
      PreservesLimit P (rankSpaceInclusion α) ∧ PreservesColimit P (rankSpaceInclusion α) := by
  let L := cgwhLimit (P ⋙ rankSpaceInclusion α)
  let R := cgwhColimit (P ⋙ rankSpaceInclusion α)
  obtain ⟨hl, hr⟩ := rank_diagram_size hα hcard hν hc hJ P
  obtain ⟨l, ⟨el⟩⟩ := rankSpace_representative hcard L.cone.pt hl
  obtain ⟨r, ⟨er⟩⟩ := rankSpace_representative hcard R.cocone.pt hr
  letI : HasLimit (P ⋙ rankSpaceInclusion α) := ⟨⟨L⟩⟩
  letI : HasColimit (P ⋙ rankSpaceInclusion α) := ⟨⟨R⟩⟩
  letI : CreatesLimit P (rankSpaceInclusion α) :=
    createsLimitOfFullyFaithfulOfIso' L.isLimit l (cgwhIsoOfHomeo el)
  letI : CreatesColimit P (rankSpaceInclusion α) :=
    createsColimitOfFullyFaithfulOfIso' R.isColimit r (cgwhIsoOfHomeo er)
  letI := hasLimit_of_created P (rankSpaceInclusion α)
  letI := hasColimit_of_created P (rankSpaceInclusion α)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

private theorem rank_topological_size {α : Ordinal.{u}} {ν : Cardinal.{u}}
    (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof)
    (X : RankSpace α) : topologicalSize X.space.obj < preBeth α := by
  obtain ⟨hsl, hω, _⟩ := rank_cardinal_properties hα hcard hν hc
  let a := max ℵ₀ #(X.space.obj : Type u)
  have ha : a < preBeth α := max_lt hω X.carrier_lt
  exact (topologicalSize_le_two_power_of_carrier (κ := a) (le_max_left _ _) (le_max_right _ _)).trans_lt
    (hsl.isStrongPrelimit ha)

/-- Lemma E.3.2.3. The closed stage contains the prescribed carriers and admits
representatives up to the stated size bound. Its inclusion preserves all
limits and colimits with at most ν objects in their indexing category. -/
theorem exists_rank_bounded_spaces {I : Type u} (X : I → CGWH.{u}) (s : I → ZFSet.{u})
    (hs : ∀ i, ZFSet.card (s i) = #((X i).obj : Type u)) {ν : Cardinal.{u}} (hν : ℵ₀ ≤ ν) :
    ∃ α : Ordinal.{u}, IsSuccLimit α ∧ preBeth α = α.card ∧ ν < α.cof ∧
      (∀ i, ∃ Y : RankSpace α, rankCarrierCode Y.code = s i ∧ Nonempty (Y.space.obj ≃ₜ (X i).obj)) ∧
      (∀ (A : RankSpace α) (B : CGWH.{u}),
        topologicalSize B.obj ≤ smallSpaceBound (topologicalSize A.space.obj) →
        ∃ B' : RankSpace α, Nonempty (B'.space.obj ≃ₜ B.obj)) ∧
      ∀ (J : Type u) [SmallCategory J], #J ≤ ν → ∀ P : J ⥤ RankSpace α,
        HasLimit P ∧ HasColimit P ∧
        PreservesLimit P (rankSpaceInclusion α) ∧ PreservesColimit P (rankSpaceInclusion α) := by
  let β := ⨆ i, Order.succ (ZFSet.rank (s i))
  obtain ⟨α, hβα, hα, hcard, hc⟩ := exists_rank_stage β hν
  obtain ⟨hsl, hω, _⟩ := rank_cardinal_properties hα hcard hν hc
  refine ⟨α, hα, hcard, hc, ?_, ?_, fun J _ hJ P => rank_limit_colimit hα hcard hν hc hJ P⟩
  · intro i
    apply rankSpaceOn_set (X i) (s i) _ (hs i)
    apply ZFSet.mem_vonNeumann.mpr
    exact (Order.lt_succ _).trans_le ((le_ciSup (Ordinal.bddAbove_of_small) i).trans hβα)
  · intro A B hB
    apply rankSpace_representative hcard B
    apply ((carrier_card_le_size _).trans hB).trans_lt
    exact rankSpace_bound_lt hsl hω (rank_topological_size hα hcard hν hc A)


/-- The limit and colimit closure for a bounded shape, including preservation. -/
theorem rankSpace_diagram_closure {α : Ordinal.{u}} {ν : Cardinal.{u}}
    (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof)
    (J : Type u) [SmallCategory J] (hJ : #J ≤ ν) :
    HasLimitsOfShape J (RankSpace α) ∧ HasColimitsOfShape J (RankSpace α) ∧
      PreservesLimitsOfShape J (rankSpaceInclusion α) ∧ PreservesColimitsOfShape J (rankSpaceInclusion α) :=
  ⟨⟨fun P => (rank_limit_colimit hα hcard hν hc hJ P).1⟩,
    ⟨fun P => (rank_limit_colimit hα hcard hν hc hJ P).2.1⟩,
    ⟨fun {P} => (rank_limit_colimit hα hcard hν hc hJ P).2.2.1⟩,
    ⟨fun {P} => (rank_limit_colimit hα hcard hν hc hJ P).2.2.2⟩⟩

theorem rankSpace_countable_shape_closure {α : Ordinal.{u}} {ν : Cardinal.{u}}
    (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof)
    (J : Type) [SmallCategory J] [Countable J] :
    HasLimitsOfShape J (RankSpace α) ∧ HasColimitsOfShape J (RankSpace α) ∧
      PreservesLimitsOfShape J (rankSpaceInclusion α) ∧ PreservesColimitsOfShape J (rankSpaceInclusion α) := by
  let J' := ULiftHom.{u} (ULift.{u} J)
  let e : J ≌ J' := ULiftHomULiftCategory.equiv J
  letI : Countable J' := inferInstanceAs (Countable (ULift.{u} J))
  have hJ' : #J' ≤ ν := mk_le_aleph0.trans hν
  obtain ⟨lim, colim, presLim, presColim⟩ := rankSpace_diagram_closure hα hcard hν hc J' hJ'
  letI := lim
  letI := colim
  letI := presLim
  letI := presColim
  exact ⟨hasLimitsOfShape_of_equivalence e.symm, hasColimitsOfShape_of_equivalence e.symm,
    preservesLimitsOfShape_of_equiv e.symm _, preservesColimitsOfShape_of_equiv e.symm _⟩

/-- Proposition E.3.4.1(2). Pullbacks exist and are preserved by the inclusion. -/
theorem rankSpace_pullbacks {α : Ordinal.{u}} {ν : Cardinal.{u}}
    (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof) :
    HasPullbacks (RankSpace α) ∧ PreservesLimitsOfShape WalkingCospan (rankSpaceInclusion α) := by
  let f : WalkingCospan → Fin 3 :=
    fun x => match x with | .left => 0 | .right => 1 | .one => 2
  have hf : Injective f := by
    rintro (_ | (_ | _)) (_ | (_ | _)) h <;> simp_all [f]
  letI : Countable WalkingCospan := hf.countable
  obtain ⟨l, _, p, _⟩ := rankSpace_countable_shape_closure hα hcard hν hc WalkingCospan
  exact ⟨l, p⟩

/-- Proposition E.3.4.1(3). Countable coproducts and their preservation. -/
theorem rankSpace_countable_coproducts {α : Ordinal.{u}} {ν : Cardinal.{u}}
    (hα : IsSuccLimit α) (hcard : preBeth α = α.card) (hν : ℵ₀ ≤ ν) (hc : ν < α.cof)
    (I : Type) [Countable I] :
    HasColimitsOfShape (Discrete I) (RankSpace α) ∧
      PreservesColimitsOfShape (Discrete I) (rankSpaceInclusion α) := by
  have h : Injective (Discrete.as : Discrete I → I) := by
    rintro ⟨x⟩ ⟨y⟩ h
    exact congrArg Discrete.mk h
  letI : Countable (Discrete I) := h.countable
  obtain ⟨_, c, _, p⟩ := rankSpace_countable_shape_closure hα hcard hν hc (Discrete I)
  exact ⟨c, p⟩

/-- Proposition E.3.4.1(4). A CGWH space embedded in a bounded space
has a homeomorphic representative of bounded rank. -/
theorem rankSpace_embedding_representative {α : Ordinal.{u}} (hcard : preBeth α = α.card)
    (X : RankSpace α) (Z : CGWH.{u}) {f : Z.obj → X.space.obj} (hf : IsEmbedding f) :
    ∃ Y : RankSpace α, Nonempty (Y.space.obj ≃ₜ Z.obj) :=
  rankSpace_representative hcard Z ((mk_le_of_injective hf.injective).trans_lt X.carrier_lt)

/-- Proposition E.3.4.1(5). Locally closed subspaces, including open and
closed subspaces, have bounded rank representatives. -/
theorem rankSpace_locallyClosed_representative {α : Ordinal.{u}} (hcard : preBeth α = α.card)
    (X : RankSpace α) (Z : Set X.space.obj) (hZ : IsLocallyClosed Z) :
    ∃ Y : RankSpace α, Nonempty (Y.space.obj ≃ₜ Z) := by
  letI : CompactlyGeneratedSpace Z := locallyClosed_compactlyGenerated hZ
  let A := CGWH.of (weaklyHausdorff_subspace X.space.property Z)
  exact rankSpace_embedding_representative hcard X A IsEmbedding.subtypeVal

end Masullo
