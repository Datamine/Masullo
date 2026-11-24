/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import CompactCharacterCompleteness
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Baire.LocallyCompactRegular

open Filter Function MeasureTheory Set Topology
open scoped ComplexConjugate Pointwise

namespace Masullo

noncomputable section

/-- A character of a compact subgroup of a compact Hausdorff abelian group extends to the
whole group. The subgroup is presented by an injective continuous homomorphism.
Stone–Weierstrass gives density of the span of the restricted characters. Orthogonality
on the subgroup then gives the desired restriction. -/
theorem exists_pontryaginDual_extension_of_compact {H K : Type*}
    [CommGroup H] [TopologicalSpace H] [CompactSpace H]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (i : H →ₜ* K) (hi : Function.Injective i) (χ : PontryaginDual H) :
    ∃ ψ : PontryaginDual K, ∀ x, ψ (i x) = χ x := by
  classical
  have he := i.continuous.isClosedEmbedding hi
  let : T2Space H := he.isEmbedding.t2Space
  let : IsTopologicalGroup H := he.isEmbedding.isInducing.topologicalGroup i
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haar
  let r : PontryaginDual K →* C(H, ℂ) :=
    { toFun ψ := ⟨fun x ↦ (ψ (i x) : ℂ), continuous_subtype_val.comp (ψ.continuous.comp i.continuous)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let c : C(H, ℂ) := ⟨fun x ↦ (χ x : ℂ), continuous_subtype_val.comp χ.continuous⟩
  -- The Fourier coefficient at χ is a continuous linear functional on continuous functions.
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let L := (innerSL ℂ (T c)).comp T
  by_contra! hnone
  have horth : Submodule.span ℂ (range r) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨ψ, rfl⟩
    obtain ⟨g, hg⟩ := hnone ψ
    let δ : PontryaginDual H := PontryaginDual.map i ψ * χ⁻¹
    have hδ : (δ g : ℂ) ≠ 1 := by
      change ((ψ (i g) * (χ g)⁻¹ : Circle) : ℂ) ≠ 1
      rw [← div_eq_mul_inv]
      exact fun h ↦ hg (div_eq_one.mp (Circle.ext h))
    change inner ℂ (T c) (T (r ψ)) = 0
    rw [ContinuousMap.inner_toLp]
    change (∫ x, (ψ (i x) : ℂ) * conj (χ x : ℂ) ∂μ) = 0
    simp_rw [← Circle.coe_inv_eq_conj]
    change (∫ x, (δ x : ℂ) ∂μ) = 0
    -- Translation by g fixes the integral but multiplies it by the nontrivial value δ(g).
    have ht := integral_mul_left_eq_self (μ := μ) (fun x ↦ (δ x : ℂ)) g
    simp_rw [map_mul, Circle.coe_mul, integral_const_mul] at ht
    by_contra hn
    exact hδ ((mul_eq_right₀ hn).mp ht)
  have htop := (Submodule.span ℂ (range r)).topologicalClosure_minimal horth L.isClosed_ker
  rw [dense_span_restrictedCharacters i hi r (fun _ _ ↦ rfl)] at htop
  have hc : inner ℂ (T c) (T c) = 0 := htop (Submodule.mem_top (x := c))
  have hc0 := (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ)
    ((inner_self_eq_zero.mp hc).trans (map_zero T).symm)
  have : (1 : ℂ) = 0 := by simpa [c] using congrArg (fun f : C(H, ℂ) ↦ f 1) hc0
  exact one_ne_zero this

section Restriction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- A character of a compact group embedded in an LCA group extends to the whole group.
Evaluation embeds the compact group into the compact closure of the ambient evaluation image. -/
private theorem exists_extension_of_compact_source {K : Type*} [CommGroup K]
    [TopologicalSpace K] [CompactSpace K] (i : K →ₜ* G) (hi : Function.Injective i)
    (χ : PontryaginDual K) : ∃ ψ : PontryaginDual G, ∀ x, ψ (i x) = χ x := by
  let ev : G →* (PontryaginDual G → Circle) :=
    { toFun x ψ := ψ x
      map_one' := funext fun ψ ↦ map_one ψ
      map_mul' x y := funext fun ψ ↦ map_mul ψ x y }
  have hev : Continuous ev := continuous_pi fun ψ ↦ ψ.continuous
  have hinj : Function.Injective ev := by
    intro x y h
    by_contra hxy
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr hxy)
    exact hψ (by rw [map_div, show ψ x = ψ y from congrFun h ψ, div_self'])
  let L := ev.range.topologicalClosure
  let : CompactSpace L := isCompact_iff_compactSpace.mp ev.range.isClosed_topologicalClosure.isCompact
  let j : G →ₜ* L :=
    ⟨ev.codRestrict L (fun x ↦ ev.range.le_topologicalClosure ⟨x, rfl⟩), hev.subtype_mk _⟩
  have hj : Function.Injective j := fun _ _ h ↦ hinj (congrArg Subtype.val h)
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_extension_of_compact (j.comp i) (hj.comp hi) χ
  exact ⟨ψ.comp j, hψ⟩

omit [T2Space G] in
/-- A character of a closed subgroup which is trivial on its intersection with a compact
subgroup extends to a character trivial on the whole compact subgroup. In the quotient of
`G × Circle` by the graph and the compact subgroup, the circle factor still embeds. -/
theorem exists_pontryaginDual_extension_trivial_on_compact (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hK : IsCompact (K : Set G))
    (χ : PontryaginDual H) (hχ : ∀ x : H, (x : G) ∈ K → χ x = 1) :
    ∃ ψ : PontryaginDual G, (∀ x : H, ψ x = χ x) ∧ ∀ x : K, ψ x = 1 := by
  -- Quotient by the graph of χ and by the compact subgroup where the extension must vanish.
  let graph := (H.subtype.prod χ.toMonoidHom).range
  let K₀ := K.prod (⊥ : Subgroup Circle)
  let D := graph ⊔ K₀
  have hGraph : IsClosed (graph : Set (G × Circle)) := by
    rw [MonoidHom.coe_range]
    let f : H × Circle → G × Circle := Prod.map Subtype.val id
    have hf : IsClosedEmbedding f := hH.isClosedEmbedding_subtypeVal.prodMap IsClosedEmbedding.id
    have hc : IsClosed {p : H × Circle | χ p.1 = p.2} :=
      isClosed_eq (χ.continuous.comp continuous_fst) continuous_snd
    convert hf.isClosedMap _ hc using 1
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x, χ x), rfl, rfl⟩
    · rintro ⟨⟨x, z⟩, hz, rfl⟩
      exact ⟨x, Prod.ext rfl hz⟩
  have hK₀ : IsCompact (K₀ : Set (G × Circle)) := by
    simpa [K₀, Subgroup.coe_prod] using hK.prod (isCompact_singleton (x := (1 : Circle)))
  let : IsClosed (D : Set (G × Circle)) := by
    rw [Subgroup.mul_normal]
    exact hGraph.mul_right_of_isCompact hK₀
  let q : G × Circle →ₜ* (G × Circle) ⧸ D :=
    ⟨QuotientGroup.mk' D, QuotientGroup.continuous_mk⟩
  let i : Circle →ₜ* (G × Circle) ⧸ D :=
    q.comp ⟨MonoidHom.inr G Circle, continuous_const.prodMk continuous_id⟩
  have hInj : Function.Injective i := by
    apply (injective_iff_map_eq_one i.toMonoidHom).mpr
    intro z hz
    obtain ⟨_, ⟨x, rfl⟩, ⟨k, w⟩, ⟨hk, hw⟩, he⟩ :=
      Subgroup.mem_sup.mp ((QuotientGroup.eq_one_iff (1, z)).mp hz)
    have hx : (x : G) * k = 1 := congrArg Prod.fst he
    have hw' : w = 1 := Subgroup.mem_bot.mp hw
    have hxK : (x : G) ∈ K :=
      (eq_inv_of_mul_eq_one_left hx).symm ▸ K.inv_mem hk
    have hz' : χ x * w = z := congrArg Prod.snd he
    simpa [hχ x hxK, hw'] using hz'.symm
  let idχ : PontryaginDual Circle := ContinuousMonoidHom.id Circle
  obtain ⟨ψ, hψ⟩ := exists_extension_of_compact_source i hInj idχ
  let Ψ := ψ.comp q
  let ψG : PontryaginDual G :=
    (Ψ.comp ⟨MonoidHom.inl G Circle, continuous_id.prodMk continuous_const⟩)⁻¹
  have hTrivial (p : G × Circle) (hp : p ∈ D) : Ψ p = 1 := by
    change ψ (q p) = 1
    rw [show q p = 1 from (QuotientGroup.eq_one_iff p).mpr hp, map_one]
  refine ⟨ψG, fun x ↦ ?_, fun x ↦ ?_⟩
  · have hGraphMem : (↑x, χ x) ∈ graph := ⟨x, rfl⟩
    have h := hTrivial (x, χ x) ((show graph ≤ D from le_sup_left) hGraphMem)
    rw [show ((x : G), χ x) = ((x : G), 1) * (1, χ x) by simp, map_mul] at h
    change (Ψ (x, 1))⁻¹ = χ x
    exact (eq_inv_of_mul_eq_one_right (show Ψ (x, 1) * χ x = 1 from
      (hψ (χ x)) ▸ h)).symm
  · have hCompactMem : (↑x, 1) ∈ K₀ := ⟨x.property, Subgroup.one_mem _⟩
    have h := hTrivial (x, 1) ((show K₀ ≤ D from le_sup_right) hCompactMem)
    change (Ψ (x, 1))⁻¹ = 1
    simp [h]

end Restriction


/-- There is a radius such that characters mapping any fixed identity neighborhood into
the closed circle ball of that radius form a compact set in the compact-open topology.
Powers give equicontinuity at the identity, and Arzelà–Ascoli gives compactness. -/
theorem exists_isCompact_pontryaginDual_polar {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ r : ℝ, 0 < r ∧ ∀ U ∈ 𝓝 (1 : G),
      IsCompact {χ : PontryaginDual G | MapsTo χ U (Metric.closedBall 1 r)} := by
  classical
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  obtain ⟨r, hr, hBall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hArc
  refine ⟨r, hr, fun U hU ↦ ?_⟩
  let W := Metric.closedBall (1 : Circle) r
  let S := {f : G →* Circle | MapsTo f U W}
  have hEqui : Equicontinuous (fun f : S ↦ (f.1 : G → Circle)) := by
    refine equicontinuous_of_equicontinuousAt_one Subtype.val ?_
    apply (Metric.equicontinuousAt_iff_right (α := Circle)).mpr
    intro ε hε
    let T (n : ℕ) := (fun z : Circle ↦ z ^ n) ⁻¹' W
    have hDisj : Disjoint (Metric.ball (1 : Circle) ε)ᶜ (⋂ n, T n) := by
      refine Set.disjoint_left.mpr fun z hz hzT ↦ ?_
      have hz1 := Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two (z := z)
        (fun n _ ↦ hBall (mem_iInter.mp hzT n))
      exact hz (hz1.symm ▸ Metric.mem_ball_self hε)
    obtain ⟨N, hN⟩ := (isClosed_compl_iff.mpr Metric.isOpen_ball).isCompact
      |>.elim_finite_subfamily_closed T
        (fun n ↦ Metric.isClosed_closedBall.preimage (continuous_pow n)) hDisj.inter_eq
    have hNear : ∀ᶠ x : G in 𝓝 1, ∀ n ∈ N, x ^ n ∈ U :=
      (eventually_all_finset N).2 fun n _ ↦
        (continuous_pow n).tendsto' 1 1 (one_pow n) hU
    filter_upwards [hNear] with x hx f
    have hPow : f.1 x ∈ ⋂ n ∈ N, T n := by
      simp only [mem_iInter, T, mem_preimage, ← map_pow]
      exact fun n hn ↦ f.2 (hx n hn)
    have hMem : f.1 x ∈ Metric.ball (1 : Circle) ε := by
      by_contra hz
      exact (Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hN)) hz hPow
    simpa [Function.comp_def, map_one, Metric.mem_ball, dist_comm] using hMem
  let A := {f : ContinuousMonoidHom G Circle | MapsTo f U W}
  let C := ContinuousMonoidHom.toContinuousMap '' A
  have hPointwise : ContinuousMap.toFun '' C =
      Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
    ext f
    constructor
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      exact ⟨hψ, ψ.toMonoidHom, rfl⟩
    · rintro ⟨hf, ψ, rfl⟩
      let ψc : ContinuousMonoidHom G Circle :=
        { toMonoidHom := ψ, continuous_toFun := hEqui.continuous ⟨ψ, hf⟩ }
      exact ⟨ψc.toContinuousMap, ⟨ψc, hf, rfl⟩, rfl⟩
  have hC : IsCompact C := by
    apply ArzelaAscoli.isCompact_of_equicontinuous
    · rw [hPointwise]
      exact ((isClosed_set_pi fun _ _ ↦ Metric.isClosed_closedBall).inter
        (MonoidHom.isClosed_range_coe G Circle)).isCompact
    · refine (equicontinuous_iff_range (F := fun f : C ↦ f.1.toFun)).mpr ?_
      rw [← Set.image_eq_range ContinuousMap.toFun C, hPointwise]
      have hRange : range (fun f : S ↦ (f.1 : G → Circle)) =
          Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
        ext f
        constructor
        · rintro ⟨ψ, rfl⟩
          exact ⟨ψ.2, ψ.1, rfl⟩
        · rintro ⟨hf, ψ, rfl⟩
          exact ⟨⟨ψ, hf⟩, rfl⟩
      rw [← hRange]
      exact equicontinuous_iff_range.mp hEqui
  exact (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).isCompact_iff.mpr hC


section Annihilators

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The compact-open neighborhoods of the trivial character test values on compact sets. -/
theorem pontryaginDual_nhds_one_hasBasis :
    (𝓝 (1 : PontryaginDual G)).HasBasis
      (fun p : Set G × Set Circle ↦ IsCompact p.1 ∧ p.2 ∈ 𝓝 (1 : Circle))
      (fun p ↦ {χ | MapsTo χ p.1 p.2}) := by
  let f : PontryaginDual G → C(G, Circle) := ContinuousMonoidHom.toContinuousMap
  have hf : IsInducing f := ContinuousMonoidHom.isInducing_toContinuousMap G Circle
  rw [hf.nhds_eq_comap]
  exact ((𝓝 (1 : Circle)).basis_sets.nhds_continuousMapConst (X := G)).comap f

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator consists of characters
whose restriction to the subgroup is trivial. -/
def lcaAnnihilator (H : Subgroup G) : Subgroup (PontryaginDual G) :=
  (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)).toMonoidHom.ker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator in the original group is
the intersection of the kernels of the characters in the given subgroup. -/
def lcaDualAnnihilator (J : Subgroup (PontryaginDual G)) : Subgroup G :=
  ⨅ χ : J, (show G →ₜ* Circle from χ.val).toMonoidHom.ker

/-- Paper: Definition D.1.4.5, p. 758. A character is in the annihilator exactly
when its value on every element of the subgroup is one. -/
theorem mem_lcaAnnihilator_iff (H : Subgroup G) (χ : PontryaginDual G) :
    χ ∈ lcaAnnihilator H ↔ ∀ x : H, χ x.val = 1 := by
  rw [lcaAnnihilator, MonoidHom.mem_ker]
  constructor
  · intro h x
    exact congrArg (fun ψ : PontryaginDual H ↦ ψ x) h
  · exact fun h ↦ PontryaginDual.ext h

/-- Paper: Definition D.1.4.5, p. 758. A group element is in the dual annihilator
exactly when every character of the subgroup takes value one there. -/
theorem mem_lcaDualAnnihilator_iff (J : Subgroup (PontryaginDual G)) (x : G) :
    x ∈ lcaDualAnnihilator J ↔ ∀ χ : J, χ.val x = 1 :=
  Subgroup.mem_iInf

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.1.4.6(1), p. 758. Taking the annihilator twice recovers a
closed subgroup under the evaluation pairing. -/
theorem lcaDualAnnihilator_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    lcaDualAnnihilator (lcaAnnihilator H) = H := by
  ext x
  rw [mem_lcaDualAnnihilator_iff]
  constructor
  · intro hx
    let : T1Space (G ⧸ H) := QuotientGroup.t1Space_iff.mpr hH
    let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
    apply (QuotientGroup.eq_one_iff x).mp
    by_contra hne
    obtain ⟨ψ, hψne⟩ := exists_pontryaginDual_apply_ne_one hne
    apply hψne
    have hψ : PontryaginDual.map q ψ ∈ lcaAnnihilator H := by
      apply (mem_lcaAnnihilator_iff H _).mpr
      intro y
      have hy : q y.val = 1 := (QuotientGroup.eq_one_iff y.val).mpr y.property
      rw [PontryaginDual.map_apply, hy, map_one]
    exact hx ⟨PontryaginDual.map q ψ, hψ⟩
  · intro hx χ
    exact (mem_lcaAnnihilator_iff H χ.val).mp χ.property ⟨x, hx⟩

omit [T2Space G] in
/-- A compact subset of a quotient of a locally compact group lies in the image of a compact set. -/
private theorem exists_isCompact_quotient_preimage (H : Subgroup G) {K : Set (G ⧸ H)}
    (hK : IsCompact K) : ∃ C : Set G, IsCompact C ∧ K ⊆ QuotientGroup.mk '' C := by
  obtain ⟨L, hLcomp, hL⟩ := exists_compact_mem_nhds (1 : G)
  have hU : QuotientGroup.mk '' L ∈ 𝓝 (1 : G ⧸ H) :=
    (QuotientGroup.isOpenMap_coe (N := H)).image_mem_nhds hL
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK
    ⟨(1 : G ⧸ H), mem_interior_iff_mem_nhds.mpr hU⟩
  refine ⟨⋃ g ∈ t, Homeomorph.mulLeft (g.out)⁻¹ '' L,
    t.isCompact_biUnion fun g _ =>
      hLcomp.image (Homeomorph.mulLeft (g.out)⁻¹).continuous, ?_⟩
  intro k hk
  obtain ⟨g, hg, hkU⟩ := mem_iUnion₂.mp (ht hk)
  rw [mem_preimage, mem_image] at hkU
  obtain ⟨y, hy, hgy⟩ := hkU
  refine ⟨(g.out)⁻¹ * y, mem_iUnion₂.mpr ⟨g, hg, mem_image_of_mem _ hy⟩, ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', hgy,
    inv_mul_cancel_left]

/-- Paper: Lemma D.1.4.6(2), p. 758. Pullback by the quotient map identifies
the dual of a quotient with the annihilator. -/
theorem lcaQuotientDual_equiv_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H,
      ∀ (χ : PontryaginDual (G ⧸ H)) x, (e χ).val x = χ (QuotientGroup.mk x) := by
  -- Closedness of `H` makes the quotient Hausdorff.
  have hpre : QuotientGroup.mk ⁻¹' ({1} : Set (G ⧸ H)) = (H : Set G) := by
    simpa [QuotientGroup.mk_one] using QuotientGroup.preimage_mk_one H
  have : T2Space (G ⧸ H) := IsTopologicalGroup.t2Space_iff_one_closed.mpr <| by
    rw [← (QuotientGroup.isQuotientMap_mk H).isCoinducing.isClosed_preimage, hpre]
    exact hH
  let q : G →ₜ* G ⧸ H :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := QuotientGroup.continuous_mk }
  have hq (x : G) : q x = QuotientGroup.mk x := by
    change QuotientGroup.mk' H x = QuotientGroup.mk x
    exact QuotientGroup.mk'_apply H x
  have hker (ψ : lcaAnnihilator H) : H ≤ ψ.val.toMonoidHom.ker := by
    intro x hx
    exact (mem_lcaAnnihilator_iff H ψ.val).1 ψ.property ⟨x, hx⟩
  let toAnn : PontryaginDual (G ⧸ H) →* lcaAnnihilator H :=
    { toFun := fun χ => ⟨PontryaginDual.map q χ, by
        rw [mem_lcaAnnihilator_iff]
        intro x
        rw [PontryaginDual.map_apply]
        have : q x.val = 1 := by
          change QuotientGroup.mk x.val = 1
          exact (QuotientGroup.eq_one_iff _).2 x.property
        rw [this, map_one]⟩
      map_one' := Subtype.ext (map_one (PontryaginDual.map q))
      map_mul' := fun χ φ => Subtype.ext (map_mul (PontryaginDual.map q) χ φ) }
  let fromAnnFun (ψ : lcaAnnihilator H) : PontryaginDual (G ⧸ H) :=
    { toMonoidHom := QuotientGroup.lift H ψ.val.toMonoidHom (hker ψ)
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 ψ.val.continuous_toFun }
  have happly (ψ : lcaAnnihilator H) (x : G) :
      fromAnnFun ψ (QuotientGroup.mk x) = ψ.val x := by
    dsimp [fromAnnFun]
    exact QuotientGroup.lift_mk' H (hker ψ) x
  let fromAnn : lcaAnnihilator H →* PontryaginDual (G ⧸ H) :=
    { toFun := fromAnnFun
      map_one' := by
        apply PontryaginDual.ext
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        rw [happly 1 x]
        rfl
      map_mul' := fun ψ φ => by
        apply PontryaginDual.ext
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        rw [happly (ψ * φ) x]
        have hr :
            (fromAnnFun ψ * fromAnnFun φ) (QuotientGroup.mk x) =
              fromAnnFun ψ (QuotientGroup.mk x) * fromAnnFun φ (QuotientGroup.mk x) :=
          ContinuousMonoidHom.mul_apply _ _ _
        rw [hr, happly ψ x, happly φ x, Subgroup.coe_mul]
        rfl }
  have hinv_left (χ : PontryaginDual (G ⧸ H)) : fromAnn (toAnn χ) = χ := by
    apply PontryaginDual.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    dsimp [fromAnn]
    rw [happly (toAnn χ) x]
    dsimp [toAnn]
    rw [hq]
  have hinv_right (ψ : lcaAnnihilator H) : toAnn (fromAnn ψ) = ψ := by
    apply Subtype.ext
    apply PontryaginDual.ext
    intro x
    dsimp [toAnn, fromAnn]
    rw [hq, happly ψ x]
  have hbij : Function.Bijective toAnn :=
    ⟨fun χ φ h => (hinv_left χ).symm.trans ((congrArg fromAnn h).trans (hinv_left φ)),
      fun ψ => ⟨fromAnn ψ, hinv_right ψ⟩⟩
  have hto_cont : Continuous toAnn := by
    rw [IsInducing.subtypeVal.continuous_iff (f := toAnn)]
    exact (PontryaginDual.map q).continuous
  have hfrom_cont : Continuous fromAnn := by
    refine continuous_of_continuousAt_one fromAnn ?_
    rw [ContinuousAt, map_one fromAnn]
    refine (pontryaginDual_nhds_one_hasBasis (G := G ⧸ H)).tendsto_right_iff.mpr ?_
    rintro ⟨K, V⟩ ⟨hK, hV⟩
    obtain ⟨C, hC, hKC⟩ := exists_isCompact_quotient_preimage H hK
    rw [IsInducing.subtypeVal.nhds_eq_comap (1 : lcaAnnihilator H)]
    refine mem_comap.mpr ⟨{ψ : PontryaginDual G | MapsTo ψ C V},
      pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (C, V)) ⟨hC, hV⟩, ?_⟩
    intro ψ hψ
    replace hψ : MapsTo (ψ.val : G → Circle) C V := by
      simpa [Set.mem_ofPred] using hψ
    show MapsTo (fromAnn ψ) K V
    intro k hk
    obtain ⟨x, hxC, rfl⟩ := hKC hk
    dsimp [fromAnn]
    rw [happly ψ x]
    exact hψ hxC
  let e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H :=
    { toFun := toAnn
      invFun := fromAnn
      left_inv := hinv_left
      right_inv := hinv_right
      map_mul' := toAnn.map_mul
      continuous_toFun := hto_cont
      continuous_invFun := hfrom_cont }
  refine ⟨e, fun χ x => ?_⟩
  dsimp [e, toAnn]
  rw [hq]

open scoped Pointwise in
/-- Some compact subgroup has a σ-compact annihilator. The subgroup is the
intersection of a decreasing sequence of compact identity neighborhoods. -/
private theorem exists_compact_subgroup_sigmaCompact_annihilator :
    ∃ K : Subgroup G, IsCompact (K : Set G) ∧ SigmaCompactSpace (lcaAnnihilator K) := by
  let N := {U : Set G // U ∈ 𝓝 (1 : G) ∧ IsCompact U}
  have hNext (U : N) : ∃ V : N, (V : Set G)⁻¹ = V.val ∧ V.val * V.val ⊆ U.val := by
    obtain ⟨V, hV, hVc, hVi, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset U.property.1
    have hVU : V ⊆ U.val := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds hV))
    exact ⟨⟨V, hV, U.property.2.of_isClosed_subset hVc hVU⟩, hVi, hVV⟩
  choose next hInv hMul using hNext
  obtain ⟨U₀, hU₀, hU₀nhds⟩ := exists_compact_mem_nhds (1 : G)
  let seq : ℕ → N := Nat.rec ⟨U₀, hU₀nhds, hU₀⟩ fun _ U ↦ next U
  let U (n : ℕ) : Set G := (seq n).val
  have hOne (n : ℕ) : (1 : G) ∈ U n := mem_of_mem_nhds (seq n).property.1
  have hMulU (n : ℕ) : U (n + 1) * U (n + 1) ⊆ U n := hMul (seq n)
  have hAnti : Antitone U := antitone_nat_of_succ_le fun n x hx ↦
    hMulU n (mul_one x ▸ Set.mul_mem_mul hx (hOne (n + 1)))
  let K : Subgroup G :=
    { carrier := ⋂ n, U n
      one_mem' := mem_iInter.mpr hOne
      mul_mem' := fun hx hy ↦ mem_iInter.mpr fun n ↦ hMulU n
        (Set.mul_mem_mul (mem_iInter.mp hx (n + 1)) (mem_iInter.mp hy (n + 1)))
      inv_mem' := fun hx ↦ mem_iInter.mpr fun n ↦ hAnti (Nat.le_succ n) (by
          change _ ∈ (next (seq n)).val
          rw [← hInv (seq n)]
          simpa only [Set.mem_inv, inv_inv] using mem_iInter.mp hx (n + 1)) }
  have hUc (n) : IsCompact (U n) := (seq n).property.2
  have hUK : IsClosed (K : Set G) := isClosed_iInter fun n ↦ (hUc n).isClosed
  have hK : IsCompact (K : Set G) := (hUc 0).of_isClosed_subset hUK (iInter_subset U 0)
  refine ⟨K, hK, ?_⟩
  obtain ⟨r, hr, hPolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  let A := lcaAnnihilator K
  have hA : IsClosed (A : Set (PontryaginDual G)) :=
    isClosed_singleton.preimage
      (PontryaginDual.map (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* G)).continuous
  let P (n : ℕ) : Set A := Subtype.val ⁻¹' {χ | MapsTo χ (U n) (Metric.closedBall 1 r)}
  refine ⟨⟨P, fun n ↦ (?_ : IsCompact (P n)), eq_univ_of_forall fun χ ↦ ?_⟩⟩
  · exact hA.isClosedEmbedding_subtypeVal.isCompact_preimage (hPolar _ (seq n).property.1)
  · let W := (χ.val : PontryaginDual G) ⁻¹' Metric.ball 1 r
    have hW : IsOpen W := Metric.isOpen_ball.preimage χ.val.continuous
    have hKW : (K : Set G) ⊆ W := fun x hx ↦
      show χ.val x ∈ Metric.ball 1 r by
        rw [(mem_lcaAnnihilator_iff K χ.val).mp χ.property ⟨x, hx⟩]
        exact Metric.mem_ball_self hr
    have hDisj : Disjoint (U 0 \ W) (⋂ n, U n) :=
      Set.disjoint_left.mpr fun x hx hxn ↦ hx.2 (hKW hxn)
    obtain ⟨n, hn⟩ := ((hUc 0).diff hW).elim_directed_family_closed U
      (fun n ↦ (hUc n).isClosed) hDisj.inter_eq hAnti.directed_ge
    refine mem_iUnion.mpr ⟨n, fun x hx ↦ Metric.ball_subset_closedBall ?_⟩
    by_contra hxW
    exact Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hn)
      ⟨hAnti (Nat.zero_le n) hx, hxW⟩ hx

/-- Restriction to a closed subgroup is an open map on the dual groups. -/
private theorem isOpenMap_restrict_dual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsOpenMap (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)) := by
  let f := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  obtain ⟨K, hK, hSigma⟩ := exists_compact_subgroup_sigmaCompact_annihilator (G := G)
  -- The restriction between the two open annihilators is surjective.
  let L := K.comap H.subtype
  have hL : IsCompact (L : Set H) := hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let A := lcaAnnihilator K
  let B := lcaAnnihilator L
  let : SigmaCompactSpace A := hSigma
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hB : IsOpen (B : Set (PontryaginDual H)) :=
    (isOpen_discrete ({1} : Set (PontryaginDual L))).preimage
      (PontryaginDual.map (⟨L.subtype, continuous_subtype_val⟩ : L →ₜ* H)).continuous
  let : LocallyCompactSpace B := hB.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let g : A →* B := (f.toMonoidHom.comp A.subtype).codRestrict B fun χ ↦
    (mem_lcaAnnihilator_iff L _).mpr fun x ↦
      (mem_lcaAnnihilator_iff K χ.val).mp χ.property ⟨(x.val : G), x.property⟩
  have hg : Continuous g := (f.continuous.comp continuous_subtype_val).subtype_mk _
  have hgSurj : Function.Surjective g := by
    intro χ
    obtain ⟨ψ, hψ, hψK⟩ := exists_pontryaginDual_extension_trivial_on_compact H K hH hK χ.val
      (fun x hx ↦ (mem_lcaAnnihilator_iff L χ.val).mp χ.property ⟨x, hx⟩)
    exact ⟨⟨ψ, (mem_lcaAnnihilator_iff K ψ).mpr hψK⟩, Subtype.ext (PontryaginDual.ext hψ)⟩
  have hOpen := g.isOpenMap_of_sigmaCompact hgSurj hg
  have hImg (U : Set (PontryaginDual G)) (hU : U ∈ 𝓝 1) : f '' U ∈ 𝓝 1 := by
    have hU' : (Subtype.val : A → PontryaginDual G) ⁻¹' U ∈ 𝓝 (1 : A) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hU
    have hV := hOpen.image_mem_nhds hU'
    rw [map_one g] at hV
    apply mem_of_superset (hB.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hV)
    rintro _ ⟨_, ⟨χ, hχ, rfl⟩, rfl⟩
    exact ⟨χ.val, hχ, rfl⟩
  exact IsTopologicalGroup.isOpenMap_iff_nhds_one.mpr fun U hU ↦
    mem_of_superset (hImg (f ⁻¹' U) hU) (image_preimage_subset f U)

/-- Paper: Lemma D.1.4.6(2), p. 758. Restriction of characters identifies the
dual modulo the annihilator with the dual of the subgroup. -/
theorem lcaDualQuotient_equiv_subgroupDual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : (PontryaginDual G ⧸ lcaAnnihilator H) ≃ₜ* PontryaginDual H,
      ∀ (χ : PontryaginDual G) (x : H), e (QuotientGroup.mk χ) x = χ x.val := by
  let f := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  have hSurj : Function.Surjective f := by
    intro χ
    obtain ⟨ψ, hψ, _⟩ := exists_pontryaginDual_extension_trivial_on_compact H ⊥ hH
      (by simp) χ (fun x hx ↦ by
        have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
        rw [hx1, map_one])
    exact ⟨ψ, PontryaginDual.ext hψ⟩
  have hOpen := isOpenMap_restrict_dual H hH
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hSurj
  have hq := QuotientGroup.isQuotientMap_mk (lcaAnnihilator H)
  have hf := hOpen.isQuotientMap f.continuous hSurj
  refine ⟨e.toContinuousMulEquiv fun _ ↦ ?_, fun _ _ ↦ rfl⟩
  exact (hq.isCoinducing.isOpen_preimage.symm.trans hf.isCoinducing.isOpen_preimage)

-- Retain the LCA assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.1.4.6(3), p. 758. The annihilator of a compact subgroup is open. -/
theorem isOpen_lcaAnnihilator (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    IsOpen (lcaAnnihilator H : Set (PontryaginDual G)) := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  let restrict := PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)
  change IsOpen (restrict ⁻¹' ({1} : Set (PontryaginDual H)))
  exact (isOpen_discrete _).preimage restrict.continuous

/-- Paper: Lemma D.1.4.6(4), p. 758. The annihilator of an open subgroup is compact. -/
theorem isCompact_lcaAnnihilator (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (lcaAnnihilator H : Set (PontryaginDual G)) := by
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator H (H.isClosed_of_isOpen hH)
  exact isCompact_iff_compactSpace.mpr e.toHomeomorph.compactSpace

end Annihilators

end
end Masullo
