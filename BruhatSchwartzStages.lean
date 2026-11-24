import BruhatDirectionalDerivatives
import ElementarySchwartzRefinement

open Function Set Topology
open scoped Classical Pointwise

namespace Masullo.LCAStructuralPair

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Every structural quotient map induced by refinement is open. -/
theorem stageMap_isOpenMap (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : Q.kernel ≤ P.kernel) :
    IsOpenMap (Q.stageMap P hu hk) := by
  let j : Q.upper.val → P.upper.val := Subgroup.inclusion hu
  have hj : IsOpenMap j :=
    (IsOpenEmbedding.inclusion (s := (Q.upper.val : Set G)) (t := (P.upper.val : Set G))
      hu (Q.upper.property.1.preimage continuous_subtype_val)).isOpenMap
  let e : P.upper.val → P.StageQuotient := QuotientGroup.mk
  let d : Q.upper.val → Q.StageQuotient := QuotientGroup.mk
  have he : IsOpenMap e := QuotientGroup.isOpenMap_coe
  have hd : Continuous d := QuotientGroup.continuous_mk
  have hc : Q.stageMap P hu hk ∘ d = e ∘ j := funext (Q.stageMap_mk P hu hk)
  intro U hU
  have h := (he.comp hj) (d ⁻¹' U) (hd.isOpen_preimage _ hU)
  rw [← hc, image_comp, image_preimage_eq _ QuotientGroup.mk_surjective] at h
  exact h

/-- When the upper subgroup is fixed, the stage map is surjective. -/
theorem stageMap_surjective_of_upper_eq (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : Q.kernel ≤ P.kernel)
    (he : Q.upper.val = P.upper.val) :
    Surjective (Q.stageMap P hu hk) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  let z : Q.upper.val := ⟨y.val, he.symm ▸ y.property⟩
  exact ⟨QuotientGroup.mk z, Q.stageMap_mk P hu hk z⟩

/-- With the kernel fixed, enlarging the upper subgroup embeds its quotient
as an open subgroup of the larger quotient. -/
theorem stageMap_openEmbedding_of_kernel_eq (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : Q.kernel ≤ P.kernel)
    (he : Q.kernel = P.kernel) :
    IsOpenEmbedding (Q.stageMap P hu hk) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap (Q.stageMap P hu hk).continuous
      _ (Q.stageMap_isOpenMap P hu hk)
  intro x y hxy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  change Q.stageMap P hu hk (QuotientGroup.mk x) =
    Q.stageMap P hu hk (QuotientGroup.mk y) at hxy
  rw [stageMap_mk, stageMap_mk, QuotientGroup.eq_iff_div_mem] at hxy
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (x.val / y.val) ∈ Q.kernel
  rw [he]
  exact hxy

/-- An open continuous surjection of abelian groups with compact kernel is proper. -/
theorem proper_of_open_surjective_compact_kernel
    {A B : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CommGroup B] [TopologicalSpace B] (f : A →ₜ* B)
    (hsurj : Surjective f) (hopen : IsOpenMap f)
    (hk : IsCompact (f.toMonoidHom.ker : Set A)) : IsProperMap f := by
  let K := f.toMonoidHom.ker
  have hSat (S : Set A) : f ⁻¹' (f '' S) = S * (K : Set A) := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      have hyx : x / y ∈ K := by
        change f (x / y) = 1
        rw [map_div, he, div_self']
      exact ⟨y, hy, x / y, hyx, by
        change y * (x / y) = x
        rw [mul_comm y, div_mul_cancel]⟩
    · rintro ⟨y, hy, k, hk', rfl⟩
      change f (y * k) ∈ f '' S
      refine ⟨y, hy, ?_⟩
      have he : f k = 1 := hk'
      rw [map_mul, he, mul_one]
  have hQuot := hopen.isQuotientMap f.continuous hsurj
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨f.continuous, ?_, ?_⟩
  · intro S hS
    apply hQuot.isClosed_preimage.mp
    rw [hSat]
    exact hS.mul_right_of_isCompact hk
  · intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have he := hSat ({x} : Set A)
    rw [Set.image_singleton] at he
    rw [he]
    exact isCompact_singleton.mul hk

/-- For a fixed upper subgroup, shrinking the compact kernel yields the
proper surjection of structural quotients used in D.1.5.4. -/
theorem stageMap_proper_of_upper_eq (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : Q.kernel ≤ P.kernel)
    (he : Q.upper.val = P.upper.val) :
    IsProperMap (Q.stageMap P hu hk) := by
  apply proper_of_open_surjective_compact_kernel _ (Q.stageMap_surjective_of_upper_eq P hu hk he)
    (Q.stageMap_isOpenMap P hu hk)
  have hc : IsCompact (P.kernel : Set G) := by
    rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  let K : Set Q.upper.val := Subtype.val ⁻¹' (P.kernel : Set G)
  have hK : IsCompact K :=
    (Q.upper.val.isClosed_of_isOpen Q.upper.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage hc
  have hh : ((Q.stageMap P hu hk).toMonoidHom.ker : Set Q.StageQuotient) =
      QuotientGroup.mk '' K := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · intro hy
      refine ⟨y, ?_, rfl⟩
      change Q.stageMap P hu hk (QuotientGroup.mk y) = 1 at hy
      rw [stageMap_mk, QuotientGroup.eq_one_iff] at hy
      exact hy
    · rintro ⟨z, hz, hez⟩
      change Q.stageMap P hu hk (QuotientGroup.mk y) = 1
      rw [← hez, stageMap_mk, QuotientGroup.eq_one_iff]
      exact hz
  rw [hh]
  exact hK.image QuotientGroup.continuous_mk

/-- The intermediate stage for a refinement uses the smaller upper
subgroup and the smaller kernel. -/
def refinementMiddle (Q P : LCAStructuralPair G) (hk : P.kernel ≤ Q.kernel) : LCAStructuralPair G :=
  ⟨Q.upper, P.kernel, P.kernel_closed, P.annihilator_open, P.annihilator_compactlyGenerated,
    hk.trans Q.kernel_le⟩

/-- The intermediate quotient is elementary, maps properly onto the first
quotient, and embeds as an open subgroup of the second quotient. -/
theorem refinementMiddle_geometry (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : P.kernel ≤ Q.kernel) :
    let R := Q.refinementMiddle P hk
    Nonempty (ElementaryLCAPresentation R.StageQuotient) ∧
      IsProperMap (R.stageMap Q le_rfl hk) ∧ Surjective (R.stageMap Q le_rfl hk) ∧
      IsOpenEmbedding (R.stageMap P hu le_rfl) := by
  let R := Q.refinementMiddle P hk
  exact ⟨R.quotient_elementary, R.stageMap_proper_of_upper_eq Q le_rfl hk rfl,
    R.stageMap_surjective_of_upper_eq Q le_rfl hk rfl,
    R.stageMap_openEmbedding_of_kernel_eq P hu le_rfl rfl⟩

/-- Realize a stage function on the ambient group by quotient pullback and
extension by zero outside the open upper subgroup. -/
def realizeSchwartz (P : LCAStructuralPair G) (p : ElementaryLCAPresentation P.StageQuotient) :
    ElementarySchwartz p.realDim p.torusDim p.latticeRank p.finiteFactor →ₗ[ℂ] (G → ℂ) where
  toFun f x := if hx : x ∈ P.upper.val then f (P.stageCoordinates p ⟨x, hx⟩).toAdd else 0
  map_add' f h := by
    funext x
    by_cases hx : x ∈ P.upper.val
    · simp only [Pi.add_apply, Pi.smul_apply, RingHom.id_apply, dite_eq_left hx]
      rfl
    · simp [hx]
  map_smul' b f := by
    funext x
    by_cases hx : x ∈ P.upper.val
    · simp only [Pi.add_apply, Pi.smul_apply, RingHom.id_apply, dite_eq_left hx]
      rfl
    · simp [hx]

@[simp] theorem realizeSchwartz_apply_of_not_mem (P : LCAStructuralPair G)
    (p : ElementaryLCAPresentation P.StageQuotient)
    (f : ElementarySchwartz p.realDim p.torusDim p.latticeRank p.finiteFactor)
    (x : G) (hx : x ∉ P.upper.val) :
    P.realizeSchwartz p f x = 0 := by
  simp [realizeSchwartz, hx]

@[simp] theorem realizeSchwartz_apply_of_mem (P : LCAStructuralPair G)
    (p : ElementaryLCAPresentation P.StageQuotient)
    (f : ElementarySchwartz p.realDim p.torusDim p.latticeRank p.finiteFactor)
    (x : P.upper.val) :
    P.realizeSchwartz p f x.val = f (P.stageCoordinates p x).toAdd := by
  simp [realizeSchwartz, x.property]

theorem realizeSchwartz_injective (P : LCAStructuralPair G)
    (p : ElementaryLCAPresentation P.StageQuotient) : Injective (P.realizeSchwartz p) := by
  intro f h he
  apply Subtype.ext
  funext x
  have hsurj : Surjective (P.stageCoordinates p) :=
    p.equiv.surjective.comp QuotientGroup.mk_surjective
  obtain ⟨y, hy⟩ := hsurj (Multiplicative.ofAdd x)
  have hx := congrFun he y.val
  rw [P.realizeSchwartz_apply_of_mem, P.realizeSchwartz_apply_of_mem, hy] at hx
  exact hx

/-- Differentiation of a realized Schwartz test is realized by the
continuous linear derivative on the same elementary stage. -/
theorem bruhatOrbitDeriv_realizeSchwartz (P : LCAStructuralPair G)
    (p : ElementaryLCAPresentation P.StageQuotient)
    (c : Multiplicative ℝ →ₜ* G)
    (f : ElementarySchwartz p.realDim p.torusDim p.latticeRank p.finiteFactor) :
    bruhatOrbitDeriv c (P.realizeSchwartz p f) =
      P.realizeSchwartz p (elementarySchwartz_derivative
        ((P.stageCoordinates p).comp (P.restrictOneParameter c)) f) := by
  funext x
  by_cases hx : x ∈ P.upper.val
  · let y : P.upper.val := ⟨x, hx⟩
    rw [show x = y.val from rfl, P.realizeSchwartz_apply_of_mem,
      elementarySchwartz_derivative_apply]
    exact bruhatOrbitDeriv_stage c (P.realizeSchwartz p f) P p f
      (fun z ↦ (P.realizeSchwartz_apply_of_mem p f z).symm) y
  · have hs : support (P.realizeSchwartz p f) ⊆ P.upper.val := by
      intro y hy
      by_contra hn
      exact (show P.realizeSchwartz p f y ≠ 0 from hy)
        (P.realizeSchwartz_apply_of_not_mem p f y hn)
    rw [P.realizeSchwartz_apply_of_not_mem p _ x hx]
    by_contra hh
    exact hx (bruhatOrbitDeriv_support_subset P c _ hs (show x ∈ support _ from hh))

/-- Lemma D.1.5.4. The refinement transition is pullback by the proper
surjection followed by extension by zero along the open subgroup embedding.
It is a closed topological embedding and preserves the realized function. -/
theorem schwartz_refinement_closedEmbedding (Q P : LCAStructuralPair G)
    (hu : Q.upper.val ≤ P.upper.val) (hk : P.kernel ≤ Q.kernel)
    (p : ElementaryLCAPresentation Q.StageQuotient)
    (q : ElementaryLCAPresentation P.StageQuotient) :
    ∃ T : ElementarySchwartz p.realDim p.torusDim p.latticeRank p.finiteFactor →L[ℂ]
        ElementarySchwartz q.realDim q.torusDim q.latticeRank q.finiteFactor,
      IsClosedEmbedding T ∧ ∀ f, P.realizeSchwartz q (T f) = Q.realizeSchwartz p f := by
  let R := Q.refinementMiddle P hk
  obtain ⟨⟨r⟩, hProper, hSurj, hEmb⟩ := Q.refinementMiddle_geometry P hu hk
  let a := R.stageCoordinateMap Q le_rfl hk r p
  let b := R.stageCoordinateMap P hu le_rfl r q
  have ha : IsProperMap a :=
    p.equiv.toHomeomorph.isProperMap.comp (hProper.comp r.equiv.symm.toHomeomorph.isProperMap)
  have hoa : IsOpenMap a := p.equiv.toHomeomorph.isOpenMap.comp
    ((R.stageMap_isOpenMap Q le_rfl hk).comp r.equiv.symm.toHomeomorph.isOpenMap)
  have hsa : Surjective a := p.equiv.surjective.comp (hSurj.comp r.equiv.symm.surjective)
  have hob : IsOpenMap b := q.equiv.toHomeomorph.isOpenMap.comp
    (hEmb.isOpenMap.comp r.equiv.symm.toHomeomorph.isOpenMap)
  have hib : Injective b := q.equiv.injective.comp (hEmb.injective.comp r.equiv.symm.injective)
  let aa := a.toMonoidHom.toAdditive
  let bb := b.toMonoidHom.toAdditive
  let pull := elementarySchwartz_properPullback aa ha
  let extZero := elementarySchwartz_extendOpen bb b.continuous hob hib
  refine ⟨extZero.comp pull,
    (elementarySchwartz_extendOpen_isClosedEmbedding bb b.continuous hob hib).comp
      (elementarySchwartz_properPullback_isClosedEmbedding aa ha hoa hsa), ?_⟩
  intro f
  funext x
  by_cases hx : x ∈ Q.upper.val
  · let y : R.upper.val := ⟨x, hx⟩
    let z : P.upper.val := Subgroup.inclusion hu y
    calc
      _ = extZero (pull f) (P.stageCoordinates q z).toAdd :=
        P.realizeSchwartz_apply_of_mem q (extZero (pull f)) z
      _ = f (Q.stageCoordinates p y).toAdd := by
        have hb : b (R.stageCoordinates r y) = P.stageCoordinates q z :=
          R.stageCoordinateMap_stageCoordinates P hu le_rfl r q y
        have ha₀ : a (R.stageCoordinates r y) = Q.stageCoordinates p y :=
          R.stageCoordinateMap_stageCoordinates Q le_rfl hk r p y
        have he := congrFun (elementarySchwartz_extendOpen_comp bb b.continuous hob hib (pull f))
          ((R.stageCoordinates r y).toAdd)
        change extZero (pull f) (b (R.stageCoordinates r y)).toAdd =
          f (a (R.stageCoordinates r y)).toAdd at he
        rw [hb, ha₀] at he
        exact he
      _ = _ := (Q.realizeSchwartz_apply_of_mem p f y).symm
  · rw [Q.realizeSchwartz_apply_of_not_mem p f x hx]
    by_cases hy : x ∈ P.upper.val
    · let z : P.upper.val := ⟨x, hy⟩
      rw [show x = z.val from rfl, P.realizeSchwartz_apply_of_mem]
      apply elementarySchwartz_extendOpen_off_range bb b.continuous hob hib
      rintro ⟨w, hw⟩
      have hr : Surjective (R.stageCoordinates r) :=
        r.equiv.surjective.comp QuotientGroup.mk_surjective
      obtain ⟨y, hey⟩ := hr (Multiplicative.ofAdd w)
      have hxy : P.stageCoordinates q z = P.stageCoordinates q (Subgroup.inclusion hu y) := by
        calc
          _ = b (Multiplicative.ofAdd w) := Multiplicative.toAdd.injective hw.symm
          _ = b (R.stageCoordinates r y) := congrArg b hey.symm
          _ = _ := R.stageCoordinateMap_stageCoordinates P hu le_rfl r q y
      have heq : (QuotientGroup.mk z : P.StageQuotient) =
          QuotientGroup.mk (Subgroup.inclusion hu y) := q.equiv.injective hxy
      have hh := (QuotientGroup.eq_iff_div_mem.mp heq)
      change x / y.val ∈ P.kernel at hh
      apply hx
      have hx' := Q.upper.val.mul_mem (Q.kernel_le (hk hh)) y.property
      rwa [div_mul_cancel] at hx'
    · exact P.realizeSchwartz_apply_of_not_mem q _ x hy


end

end Masullo.LCAStructuralPair
