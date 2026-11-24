/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import CompactCharacterCompleteness
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Pontryagin evaluation and the duality of one-parameter subgroups
-/

open Filter Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- Evaluation at a point defines a continuous character of the dual. -/
def pontryaginBidualEval : G →ₜ* PontryaginDual (PontryaginDual G) := by
  have hEval : Continuous (fun p : PontryaginDual G × G ↦ p.1 p.2) :=
    (continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_fst).prodMk continuous_snd)
  let atPoint (x : G) : PontryaginDual (PontryaginDual G) :=
    { toFun := fun χ ↦ χ x
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := hEval.comp (continuous_id.prodMk continuous_const) }
  refine
    { toFun := atPoint
      map_one' := PontryaginDual.ext fun χ ↦ map_one χ
      map_mul' := fun x y ↦ PontryaginDual.ext fun χ ↦ map_mul χ x y
      continuous_toFun := ?_ }
  exact ContinuousMonoidHom.continuous_of_continuous_uncurry atPoint
    (hEval.comp (continuous_snd.prodMk continuous_fst))

omit [IsTopologicalGroup G] in
@[simp] theorem pontryaginBidualEval_apply (x : G) (χ : PontryaginDual G) :
    pontryaginBidualEval x χ = χ x := rfl

/-- D.1.1.1(2). Compact sets of characters recover the topology and local
compactness makes the evaluation image closed. -/
theorem pontryaginBidualEval_isClosedEmbedding [T2Space G] :
    IsClosedEmbedding (pontryaginBidualEval (G := G)) := by
  let e := pontryaginBidualEval (G := G)
  have hInducing : IsInducing e := by
    rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto e (𝓝 (1 : G)) (𝓝 (e 1)) := e.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      obtain ⟨K, hK, hTest⟩ := exists_compact_pontryaginDual_test hU
      let V : Set (PontryaginDual (PontryaginDual G)) :=
        {ψ | MapsTo ψ K (Metric.ball 1 (1 / 4))}
      have hV : IsOpen V :=
        (ContinuousMap.isOpen_setOfPred_mapsTo hK Metric.isOpen_ball).preimage
          (ContinuousMonoidHom.isInducing_toContinuousMap (PontryaginDual G) Circle).continuous
      refine Filter.mem_comap.mpr ⟨V, hV.mem_nhds ?_, fun x hx ↦ hTest x (fun χ hχ ↦ hx hχ)⟩
      intro χ _
      simp [Metric.mem_ball]
  have hInjective : Function.Injective e := by
    intro x y h
    by_contra hxy
    obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr hxy)
    have heq : χ x = χ y := DFunLike.congr_fun h χ
    exact hχ (by rw [map_div, heq, div_self'])
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : UniformSpace (PontryaginDual (PontryaginDual G)) := IsTopologicalGroup.rightUniformSpace _
  let : IsUniformGroup G := isUniformGroup_of_commGroup
  let : IsUniformGroup (PontryaginDual (PontryaginDual G)) := isUniformGroup_of_commGroup
  let : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace
  exact (MonoidHom.isUniformEmbedding_of_isEmbedding (f := e)
    ⟨hInducing, hInjective⟩).isClosedEmbedding

/-- D.1.1.1(3). The compact-discrete duality follows already from the closed
embedding. -/
theorem compactSpace_iff_discretePontryaginDual [T2Space G] :
    CompactSpace G ↔ DiscreteTopology (PontryaginDual G) := by
  constructor
  · intro h
    infer_instance
  · intro h
    exact (pontryaginBidualEval_isClosedEmbedding (G := G)).compactSpace

/-- Evaluation is onto for a discrete group. Its evaluations separate points
of the compact dual, so their span is dense by Stone–Weierstrass.
Any additional character would be orthogonal to this span. -/
theorem pontryaginBidualEval_surjective_of_discrete [DiscreteTopology G] :
    Surjective (pontryaginBidualEval (G := G)) := by
  classical
  let K := PontryaginDual G
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haar
  let e : G →ₜ* PontryaginDual K := pontryaginBidualEval
  let r : G →* C(K, ℂ) :=
    { toFun x := ⟨fun χ ↦ (e x χ : ℂ), continuous_subtype_val.comp (e x).continuous⟩
      map_one' := ContinuousMap.ext fun χ ↦ by simp [e]
      map_mul' x y := ContinuousMap.ext fun χ ↦ by
        change ((e (x * y)) χ : ℂ) = (e x χ : ℂ) * (e y χ : ℂ)
        rw [map_mul]
        exact Circle.coe_mul _ _ }
  let S := MonoidHom.mrange r
  let A := StarAlgebra.adjoin ℂ (S : Set C(K, ℂ))
  have hstar : star (S : Set C(K, ℂ)) ⊆ S := by
    rw [Set.star_subset]
    rintro _ ⟨x, rfl⟩
    refine ⟨x⁻¹, ContinuousMap.ext fun χ ↦ ?_⟩
    change ((e x⁻¹ χ) : ℂ) = star (e x χ : ℂ)
    rw [map_inv]
    exact Circle.coe_inv_eq_conj _
  have hsep : A.SeparatesPoints := by
    intro χ ψ hne
    obtain ⟨x, hx⟩ : ∃ x, χ x ≠ ψ x := by
      by_contra! h
      exact hne (PontryaginDual.ext h)
    refine ⟨_, ⟨r x, StarAlgebra.subset_adjoin ℂ (S : Set C(K, ℂ)) ⟨x, rfl⟩, rfl⟩, ?_⟩
    exact fun h ↦ hx (Circle.coe_inj.mp h)
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span ℂ (range r) := by
    rw [StarAlgebra.adjoin_eq_span, Set.union_eq_left.mpr hstar, S.closure_eq]
    rfl
  have hdense : (Submodule.span ℂ (range r)).topologicalClosure = ⊤ := by
    rw [← hspan]
    exact congrArg (fun B : StarSubalgebra ℂ C(K, ℂ) ↦ B.toSubalgebra.toSubmodule)
      (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep)
  intro η
  by_contra hη
  let c : C(K, ℂ) := ⟨fun χ ↦ (η χ : ℂ), continuous_subtype_val.comp η.continuous⟩
  let T := ContinuousMap.toLp (E := ℂ) 2 μ ℂ
  let L := (innerSL ℂ (T c)).comp T
  have horth : Submodule.span ℂ (range r) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change inner ℂ (T c) (T (r x)) = 0
    rw [ContinuousMap.inner_toLp]
    have hne : η ≠ e x := fun h ↦ hη ⟨x, h.symm⟩
    simpa [c, r, hne, mul_comm] using integral_character_pair μ η (e x)
  have htop := (Submodule.span ℂ (range r)).topologicalClosure_minimal horth L.isClosed_ker
  rw [hdense] at htop
  have hc : inner ℂ (T c) (T c) = 0 := htop (Submodule.mem_top (x := c))
  have hc0 := (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ)
    ((inner_self_eq_zero.mp hc).trans (map_zero T).symm)
  have : (1 : ℂ) = 0 := by simpa [c] using congrArg (fun f : C(K, ℂ) ↦ f 1) hc0
  exact one_ne_zero this

/-- Evaluation is onto for a compact Hausdorff group. A nontrivial character
on the quotient by the evaluation image would, by the discrete case, be
evaluation at a character of the original group. That character must be trivial. -/
theorem pontryaginBidualEval_surjective_of_compact [T2Space G] [CompactSpace G] :
    Surjective (pontryaginBidualEval (G := G)) := by
  let e := pontryaginBidualEval (G := G)
  let J := e.toMonoidHom.range
  let : IsClosed (J : Set (PontryaginDual (PontryaginDual G))) :=
    (pontryaginBidualEval_isClosedEmbedding (G := G)).isClosed_range
  let q : PontryaginDual (PontryaginDual G) →ₜ* (PontryaginDual (PontryaginDual G) ⧸ J) :=
    ⟨QuotientGroup.mk' J, QuotientGroup.continuous_mk⟩
  intro η
  by_contra hη
  have hne : q η ≠ 1 := fun h ↦ hη ((QuotientGroup.eq_one_iff η).mp h)
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one hne
  obtain ⟨χ, hχ⟩ := pontryaginBidualEval_surjective_of_discrete (G := PontryaginDual G)
    (PontryaginDual.map q ψ)
  have htriv : χ = 1 := by
    apply PontryaginDual.ext
    intro x
    have hx : q (e x) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨x, rfl⟩
    have hh := DFunLike.congr_fun hχ (e x)
    exact hh.trans (by simp [PontryaginDual.map_apply, hx])
  exact hψ (by simpa [htriv, PontryaginDual.map_apply] using (DFunLike.congr_fun hχ η).symm)

/-- The space of continuous one-parameter subgroups with the compact-open topology. -/
abbrev OneParameterSubgroups (G : Type*) [Group G] [TopologicalSpace G] :=
  Multiplicative ℝ →ₜ* G

/-- D.1.6.4. When evaluation is a bidual isomorphism, transposing the character
pairing identifies one-parameter subgroups with continuous homomorphisms on
the dual. The proof checks continuity in both compact-open topologies. -/
theorem oneParameterSubgroups_dual_of_bidual
    (eG : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (heG : ∀ x χ, eG x χ = χ x) :
    ∃ e : OneParameterSubgroups G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  let evalReal := pontryaginBidualEval (G := Multiplicative ℝ)
  let eGinv : PontryaginDual (PontryaginDual G) →ₜ* G := eG.symm
  let dual := PontryaginDual.mapHom (Multiplicative ℝ) G
  let inverse (b : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)) :
      OneParameterSubgroups G :=
    eGinv.comp ((PontryaginDual.map b).comp evalReal)
  have hEval (b : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ))
      (t : Multiplicative ℝ) (χ : PontryaginDual G) : χ (inverse b t) = b χ t := by
    calc
      χ (inverse b t) = eG (inverse b t) χ := (heG _ _).symm
      _ = evalReal t (b χ) := by
        change eG (eG.symm (PontryaginDual.map b (evalReal t))) χ = _
        rw [eG.apply_symm_apply, PontryaginDual.map_apply]
      _ = b χ t := rfl
  have hLeft : Function.LeftInverse inverse dual := by
    intro a
    apply ContinuousMonoidHom.ext
    intro t
    apply eG.injective
    apply PontryaginDual.ext
    intro χ
    rw [heG, heG, hEval (dual a)]
    rfl
  have hRight : Function.RightInverse inverse dual :=
    fun b ↦ ContinuousMonoidHom.ext fun χ ↦ PontryaginDual.ext fun t ↦ hEval b t χ
  have hCont : Continuous inverse :=
    eGinv.continuous_comp_right.comp
      (evalReal.continuous_comp_left.comp
        (PontryaginDual.mapHom (PontryaginDual G) (PontryaginDual (Multiplicative ℝ))).continuous)
  exact ⟨{ toFun := dual
           invFun := inverse
           left_inv := hLeft
           right_inv := hRight
           map_mul' := map_mul dual
           continuous_toFun := dual.continuous
           continuous_invFun := hCont }, fun _ ↦ rfl⟩

/-- D.1.6.4 for a compact Hausdorff group, with the compact-open topology
on both homomorphism spaces. -/
theorem oneParameterSubgroups_dual_of_compact [T2Space G] [CompactSpace G] :
    ∃ e : OneParameterSubgroups G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  let e := pontryaginBidualEval (G := G)
  have hEmb := pontryaginBidualEval_isClosedEmbedding (G := G)
  have hSurj := pontryaginBidualEval_surjective_of_compact (G := G)
  let equiv := MulEquiv.ofBijective e.toMonoidHom ⟨hEmb.injective, hSurj⟩
  have hOpen := hEmb.isInducing.isOpenMap (by rw [hSurj.range_eq]; exact isOpen_univ)
  let eG := equiv.toContinuousMulEquiv (fun _ ↦
    (hOpen.isQuotientMap e.continuous hSurj).isCoinducing.isOpen_preimage)
  exact oneParameterSubgroups_dual_of_bidual eG (fun _ _ ↦ rfl)

end
end Masullo
