import BruhatSchwartzStages
import PontryaginDuality
import ElementarySchwartzTranslationContinuity
import CompactGroupAveraging

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- The Schwartz space in the coordinates of the given elementary presentation. -/
abbrev ElementaryLCAPresentation.Schwartz (e : ElementaryLCAPresentation G) :=
  ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor

/-- Compact quotients of elementary locally compact abelian groups are elementary. -/
theorem elementaryLCAPresentation_compactQuotient (e : ElementaryLCAPresentation G)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    Nonempty (ElementaryLCAPresentation (G ⧸ K)) := by
  obtain ⟨hGen, d, ⟨hchart⟩⟩ := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin d)) G := hchart
  obtain ⟨ev, _⟩ := pontryaginDual_bidual (G := G)
  have hDual : IsCompactlyGeneratedGroup (PontryaginDual G) :=
    isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mpr
      ⟨d, ⟨ev.toHomeomorph.chartedSpace⟩⟩
  have hOpen := isOpen_lcaAnnihilator K hK
  let t₀ : (⊤ : Subgroup G) ≃ₜ* G :=
    ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  let J : OpenCompactlyGeneratedSubgroups G :=
    ⟨⊤, by simp, compactGeneration_transport t₀.symm hGen⟩
  let P : LCAStructuralPair G :=
    ⟨J, K, hK.isClosed, hOpen, isCompactlyGeneratedGroup_closedSubgroup hDual _
      ((lcaAnnihilator K).isClosed_of_isOpen hOpen), le_top⟩
  obtain ⟨q⟩ := P.quotient_elementary
  let t : J.val ≃ₜ* G := t₀
  have ht : Subgroup.map t.toMonoidHom (K.comap J.val.subtype) = K := by
    exact Subgroup.map_comap_eq_self_of_surjective t.surjective K
  let m := QuotientGroup.congr (K.comap J.val.subtype) K t.toMulEquiv ht
  let u := m.toContinuousMulEquiv (fun U ↦ by
    rw [← (QuotientGroup.isQuotientMap_mk K).isCoinducing.isOpen_preimage,
      ← (QuotientGroup.isQuotientMap_mk (K.comap J.val.subtype)).isCoinducing.isOpen_preimage]
    change IsOpen (t ⁻¹' (QuotientGroup.mk ⁻¹' U)) ↔ IsOpen (QuotientGroup.mk ⁻¹' U)
    exact t.toHomeomorph.isOpen_preimage)
  exact ⟨{ q with equiv := u.symm.trans q.equiv }⟩

/-- Evaluation on the elementary Schwartz space, as a continuous linear form. -/
private def elementarySchwartzEvaluation (e : ElementaryLCAPresentation G) (x : G) :
    e.Schwartz →L[ℂ] ℂ := by
  let z := (e.equiv x).toAdd
  let ev : e.Schwartz →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ f z
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine ⟨ev, (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp ev fun _ ↦ ?_⟩
  refine Seminorm.continuous_of_le
    (elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)) fun f ↦ ?_
  change ‖f z‖ ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f
  have hb : (‖f z‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) := by
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun w ↦ (‖f w‖₊ : ENNReal)) z
  exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb

/-- Lemma D.1.6.18. Normalized Haar averaging from an elementary group to its
compact quotient is a continuous linear surjection of Schwartz spaces. -/
theorem elementarySchwartz_average_compactQuotient (e : ElementaryLCAPresentation G)
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] :
    ∃ (eQ : ElementaryLCAPresentation (G ⧸ K)) (P : e.Schwartz →L[ℂ] eQ.Schwartz),
      Surjective P ∧ ∀ (f : e.Schwartz) (x : G),
        Integrable (fun k : K ↦ f (e.equiv (x * k.val)).toAdd) μ ∧
        P f (eQ.equiv (QuotientGroup.mk x : G ⧸ K)).toAdd =
          ∫ k : K, f (e.equiv (x * k.val)).toAdd ∂μ := by
  classical
  obtain ⟨eQ⟩ := elementaryLCAPresentation_compactQuotient e K hK
  let q : G →ₜ* G ⧸ K := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have hqK : q.toMonoidHom.ker = K := QuotientGroup.ker_mk' K
  have hqProper : IsProperMap q :=
    LCAStructuralPair.proper_of_open_surjective_compact_kernel q hq.surjective
      hq.isOpenMap (hqK.symm ▸ hK)
  let d₀ : _ →ₜ* _ := ⟨eQ.equiv.toMonoidHom, eQ.equiv.continuous⟩
  let d₁ : _ →ₜ* _ := ⟨e.equiv.symm.toMonoidHom, e.equiv.symm.continuous⟩
  let d := d₀.comp (q.comp d₁)
  let φ := d.toMonoidHom.toAdditive
  have hφ (x : G) : φ (e.equiv x).toAdd = (eQ.equiv (q x)).toAdd := by
    change (eQ.equiv (q (e.equiv.symm (e.equiv x)))).toAdd = _
    rw [e.equiv.symm_apply_apply]
  have hproper : IsProperMap φ := eQ.equiv.toHomeomorph.isProperMap.comp
    (hqProper.comp e.equiv.symm.toHomeomorph.isProperMap)
  have hopen : IsOpenMap φ := eQ.equiv.toHomeomorph.isOpenMap.comp
    (hq.isOpenMap.comp e.equiv.symm.toHomeomorph.isOpenMap)
  have hsurj : Surjective φ :=
    eQ.equiv.surjective.comp (hq.surjective.comp e.equiv.symm.surjective)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : T2Space e.Schwartz := elementarySchwartz_t2
  letI : CompleteSpace e.Schwartz := completeSpace_elementarySchwartz
  letI : ContinuousSMul ℂ e.Schwartz :=
    (PolynormableSpace.withSeminorms ℂ e.Schwartz).continuousSMul
  letI : LocallyConvexSpace ℝ e.Schwartz :=
    (PolynormableSpace.withSeminorms ℂ e.Schwartz).toLocallyConvexSpace
  let ρ (k : K) : e.Schwartz →L[ℂ] e.Schwartz :=
    elementarySchwartz_translate (e.equiv k.val).toAdd
  have hcoord : Continuous (fun k : K ↦ (e.equiv k.val).toAdd) :=
    continuous_toAdd.comp (e.equiv.continuous.comp continuous_subtype_val)
  have hρ : Continuous (fun w : K × e.Schwartz ↦ ρ w.1 w.2) :=
    continuous_elementarySchwartz_translate.comp ((hcoord.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨L, hL⟩ := compactPettis_clm_exists μ ρ hρ
  have hFormula (f : e.Schwartz) (x : G) :
      Integrable (fun k : K ↦ f (e.equiv (x * k.val)).toAdd) μ ∧
      L f (e.equiv x).toAdd = ∫ k : K, f (e.equiv (x * k.val)).toAdd ∂μ := by
    have h := hL f (elementarySchwartzEvaluation e x)
    change Integrable (fun k : K ↦ f ((e.equiv x).toAdd + (e.equiv k.val).toAdd)) μ ∧
      L f (e.equiv x).toAdd = ∫ k : K, f ((e.equiv x).toAdd + (e.equiv k.val).toAdd) ∂μ at h
    simpa only [map_mul, toAdd_mul] using h
  have hInv (f : e.Schwartz) (x : G) (k : K) :
      L f (e.equiv (x * k.val)).toAdd = L f (e.equiv x).toAdd := by
    rw [(hFormula f _).2, (hFormula f x).2]
    simpa only [mul_assoc, Subgroup.coe_mul] using
      (integral_mul_left_eq_self (μ := μ) (fun t : K ↦ f (e.equiv (x * t.val)).toAdd) k)
  let T := elementarySchwartz_properPullback φ hproper
  have hEmb : IsClosedEmbedding T :=
    elementarySchwartz_properPullback_isClosedEmbedding φ hproper hopen hsurj
  obtain ⟨lift, hlift⟩ := hsurj.hasRightInverse
  have hRange (f : e.Schwartz) : L f ∈ T.toLinearMap.range := by
    let g := (L f).val ∘ lift
    have heq : g ∘ φ = (L f).val := by
      funext u
      let x := e.equiv.symm (Multiplicative.ofAdd u)
      let y := e.equiv.symm (Multiplicative.ofAdd (lift (φ u)))
      have hxy : QuotientGroup.mk y = (QuotientGroup.mk x : G ⧸ K) := by
        apply eQ.equiv.injective
        exact congrArg Multiplicative.ofAdd (hlift (φ u))
      have hmem : y / x ∈ K := QuotientGroup.eq_iff_div_mem.mp hxy
      have hmul : x * (y / x) = y := by rw [mul_comm, div_mul_cancel]
      have h := hInv f x (⟨y/x, hmem⟩ : K)
      have hu : (e.equiv x).toAdd = u := congrArg Multiplicative.toAdd (e.equiv.apply_symm_apply _)
      have hv : (e.equiv y).toAdd = lift (φ u) :=
        congrArg Multiplicative.toAdd (e.equiv.apply_symm_apply _)
      change L f (lift (φ u)) = L f u
      simpa only [hmul, hu, hv] using h
    have hg := elementarySchwartz_mem_of_openPullback φ hproper.continuous hopen hsurj (L f) g heq
    exact ⟨⟨g, hg⟩, Subtype.ext heq⟩
  let inv := LinearEquiv.ofInjective T.toLinearMap hEmb.injective
  have hBack : Continuous inv.symm := by
    apply hEmb.isEmbedding.isInducing.continuous_iff.mpr
    exact continuous_subtype_val.congr
      (fun u ↦ congrArg Subtype.val (inv.apply_symm_apply u).symm)
  let P : e.Schwartz →L[ℂ] eQ.Schwartz :=
    (⟨inv.symm.toLinearMap, hBack⟩ : T.toLinearMap.range →L[ℂ] eQ.Schwartz).comp
      (L.codRestrict _ hRange)
  have hP (f : e.Schwartz) : T (P f) = L f :=
    congrArg Subtype.val (inv.apply_symm_apply (⟨L f, hRange f⟩ : T.toLinearMap.range))
  have hEval (f : e.Schwartz) (x : G) :
      P f (eQ.equiv (QuotientGroup.mk x : G ⧸ K)).toAdd =
        ∫ k : K, f (e.equiv (x * k.val)).toAdd ∂μ := by
    rw [← (hFormula f x).2]
    have he : P f (φ (e.equiv x).toAdd) = L f (e.equiv x).toAdd :=
      congrArg (fun u : e.Schwartz ↦ u (e.equiv x).toAdd) (hP f)
    rwa [hφ] at he
  refine ⟨eQ, P, ?_, fun f x ↦ ⟨(hFormula f x).1, hEval f x⟩⟩
  intro g
  refine ⟨T g, Subtype.ext (funext fun v ↦ ?_)⟩
  obtain ⟨u, rfl⟩ := hsurj v
  let x := e.equiv.symm (Multiplicative.ofAdd u)
  change P (T g) (eQ.equiv (QuotientGroup.mk x : G ⧸ K)).toAdd = g (φ u)
  rw [hEval]
  have hconst (k : K) : T g (e.equiv (x * k.val)).toAdd = g (φ u) := by
    change g (φ (e.equiv (x * k.val)).toAdd) = g (φ u)
    rw [hφ]
    change _ = g (eQ.equiv (q x)).toAdd
    have hk : q k.val = 1 := (QuotientGroup.eq_one_iff k.val).mpr k.property
    rw [map_mul, hk, mul_one]
  simp_rw [hconst]
  simp

end

end Masullo
