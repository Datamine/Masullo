import ManuscriptHeckeArchimedeanSlopes
import CompactElementaryDual
import CompactBruhatFourierStages

open Bornology Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev K := normOneIdeleClass F
private abbrev Arch := mixedEmbedding.mixedSpace F
private abbrev RealPlace := {v : InfinitePlace F // v.IsReal}
private abbrev ComplexPlace := {v : InfinitePlace F // v.IsComplex}

private def archFrequencyWeight (v : Arch F) : ℝ :=
  (∑ j : RealPlace F, |v.1 j|) +
    ∑ j : ComplexPlace F, (2 * |(v.2 j).re| + |(v.2 j).im|)

private theorem archFrequencyWeight_nonneg (v : Arch F) : 0 ≤ archFrequencyWeight F v := by
  unfold archFrequencyWeight
  positivity

variable (χ : PontryaginDual (IdeleClass F))
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hs : Surjective (sIdeleClassInclusion F S))
variable (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
  (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))

private abbrev boxPhase :=
  sLocalNormOneCharacterOfGlobal F (heckeNormOneRestriction F χ) S hs hu

/-- Bounds on the shifted radial parameters and the integral angular parameters
of an actual Hecke character at a given height. -/
def manuscriptHeckeArchParametersInBox (t T : ℝ) : Prop :=
  (∀ j : RealPlace F, ‖-(t : ℂ) * Complex.I +
    (sLocalRealArchParameters F S (boxPhase F χ S hs hu) j).1‖ ≤ T) ∧
  (∀ j : ComplexPlace F, ‖-(t : ℂ) * Complex.I +
    (sLocalComplexArchParameters F S (boxPhase F χ S hs hu) j).1‖ ≤ T) ∧
  (∀ j : ComplexPlace F, |((sLocalComplexArchParameters F S (boxPhase F χ S hs hu) j).2 : ℝ)| ≤ T)

/-- A box in the absolute archimedean parameters bounds the derivative along
any fixed archimedean velocity. The coefficient depends only on the velocity. -/
private theorem norm_manuscriptArchExponent_le (t : ℝ) (v : Arch F) (T : ℝ)
    (hbox : manuscriptHeckeArchParametersInBox F χ S hs hu t T) :
    ‖manuscriptArchExponent F χ S hs hu t 0 v‖ ≤ T * archFrequencyWeight F v := by
  obtain ⟨hr, hc, ha⟩ := hbox
  unfold manuscriptArchExponent archFrequencyWeight
  simp only [zero_sub]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  apply (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← neg_mul]
    exact mul_le_mul_of_nonneg_right (hr j) (abs_nonneg _)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    refine (norm_add_le _ _).trans ?_
    rw [mul_add]
    apply add_le_add
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← neg_mul]
      exact mul_le_mul_of_nonneg_right (hc j) (by positivity)
    · rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast,
        Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (ha j) (abs_nonneg _)

variable {n : ℕ} {D : Type*} [AddCommGroup D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
private abbrev BoxModel := Multiplicative (ElementaryLCAModel 0 n 0 D)

omit [Finite D] in
/-- A fixed compact elementary quotient of norm-one classes admits fixed
archimedean lifts of the unit torus velocities. -/
theorem exists_idelicTorusVelocity_lift
    (q : K F →ₜ* BoxModel (n := n) (D := D)) (hq : Surjective q) :
    ∃ u : Fin n → (Multiplicative ℝ →ₜ* K F), ∃ v : Fin n → Arch F,
      ∀ (i : Fin n) (x : Multiplicative ℝ),
        q (u i x) = elementaryOneParameter (r := 0) (F := D) (elementaryTorusVelocity i) x ∧
        (u i x).val = manuscriptArchFlow F (v i) x := by
  letI : CompactSpace (K F) := normOneIdeleClass_compact F
  letI : T2Space (IdeleClass F) := ideleClasses_hausdorff
  letI : T2Space (BoxModel (n := n) (D := D)) :=
    T2Space.of_injective_continuous Multiplicative.toAdd.injective continuous_toAdd
  let ι : K F →ₜ* IdeleClass F :=
    ⟨(normOneIdeleClass F).subtype, continuous_subtype_val⟩
  choose u hu using fun i : Fin n ↦ exists_oneParameter_lift_proper
    (G := K F) (H := BoxModel (n := n) (D := D)) q q.continuous.isProperMap hq (elementaryOneParameter (r := 0) (F := D) (elementaryTorusVelocity i))
  choose v hv using fun i : Fin n ↦ exists_manuscriptArchFlow_eq F (ι.comp (u i))
  exact ⟨u, v, fun i x ↦ ⟨DFunLike.congr_fun (hu i) x, DFunLike.congr_fun (hv i) x⟩⟩

/-- Every integer torus frequency of a descended character is bounded by a
quotient-dependent constant times the radius of the Hecke parameter box. -/
theorem exists_idelicTorusFrequency_bound
    (q : K F →ₜ* BoxModel (n := n) (D := D)) (hq : Surjective q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (χ : PontryaginDual (IdeleClass F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
        (hs : Surjective (sIdeleClassInclusion F S))
        (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
          (sUnramified F S : Set (QuasiCharacter (IdeleClass F))))
        (θ : PontryaginDual (BoxModel (n := n) (D := D))),
        (∀ x : K F, θ (q x) = χ x.val) →
        ∀ (t : ℝ), HasHeckeHeight F χ t → ∀ (T : ℝ), 0 ≤ T →
        manuscriptHeckeArchParametersInBox F χ S hs hu t T →
        ∀ i, |(compactElementaryCharacter_frequency θ i : ℝ)| ≤ C * T := by
  obtain ⟨u, v, huv⟩ := exists_idelicTorusVelocity_lift F q hq
  let B : ℝ := 1 + ∑ i : Fin n, archFrequencyWeight F (v i)
  have hB : 0 < B := by
    dsimp [B]
    linarith [Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) ↦
      archFrequencyWeight_nonneg F (v i))]
  refine ⟨B / (2 * Real.pi), div_pos hB (by positivity), ?_⟩
  intro χ S hs hu θ hθ t ht T hT hbox i
  let k : ℝ := compactElementaryCharacter_frequency θ i
  have hOrbit (x : ℝ) :
      (χ (manuscriptArchFlow F (v i) (Multiplicative.ofAdd x)) : ℂ) *
          Complex.exp ((0 : ℂ) *
            (modulatedLog (mellinClassModulus F)
              (manuscriptArchFlow F (v i) (Multiplicative.ofAdd x)) : ℂ)) =
        Complex.exp (((2 * Real.pi * k : ℝ) : ℂ) * Complex.I * (x : ℂ)) := by
    have he := huv i (Multiplicative.ofAdd x)
    simp only [zero_mul, Complex.exp_zero, mul_one]
    rw [← he.2, ← hθ, he.1]
    change (θ (Multiplicative.ofAdd (elementaryCoverHom (x • elementaryTorusVelocity i))) : ℂ) = _
    rw [compactElementaryCharacterPhase_spec, Circle.coe_exp, map_smul, smul_eq_mul,
      compactElementaryCharacter_frequency_spec, Complex.ofReal_mul]
    change Complex.exp ((x : ℂ) * ((2 * Real.pi * k : ℝ) : ℂ) * Complex.I) = _
    apply congrArg Complex.exp
    ring
  have hId := (mellinOrbitSlope_eq_of_orbit_exp (G := IdeleClass F) (mellinClassModulus F)
    0 χ (manuscriptArchFlow F (v i)) _ hOrbit).symm.trans
      (manuscriptHecke_archSlope F χ S hs hu t ht 0 (v i))
  simp only [Complex.ofReal_zero] at hId
  have hCount := norm_manuscriptArchExponent_le F χ S hs hu t (v i) T hbox
  rw [← hId, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (show 0 < 2 * Real.pi by positivity)] at hCount
  have hB' : archFrequencyWeight F (v i) ≤ B := by
    have hle := Finset.single_le_sum (f := fun j : Fin n ↦ archFrequencyWeight F (v j))
      (fun j _ ↦ archFrequencyWeight_nonneg F (v j)) (Finset.mem_univ i)
    dsimp [B]
    linarith
  change |k| ≤ B / (2 * Real.pi) * T
  rw [div_mul_eq_mul_div, le_div_iff₀ (show 0 < 2 * Real.pi by positivity)]
  calc
    |k| * (2 * Real.pi) = (2 * Real.pi) * |k| := mul_comm _ _
    _ ≤ T * archFrequencyWeight F (v i) := hCount
    _ ≤ B * T := by rw [mul_comm B T]; exact mul_le_mul_of_nonneg_left hB' hT

/-- The descended characters that occur inside a Hecke parameter box. A
descended character represents just its norm-one restriction. -/
def idelicHeckeCharactersInBox
    (q : K F →ₜ* BoxModel (n := n) (D := D)) (T : ℝ) :
    Set (PontryaginDual (BoxModel (n := n) (D := D))) :=
  {θ | ∃ (χ : PontryaginDual (IdeleClass F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
      (hs : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) (t : ℝ),
      (∀ x : K F, θ (q x) = χ x.val) ∧ HasHeckeHeight F χ t ∧
        manuscriptHeckeArchParametersInBox F χ S hs hu t T}

/-- In a fixed quotient the number of contributing norm-one components is
bounded by a box of integer torus frequencies times the finite dual. -/
theorem exists_idelicHeckeCharacters_card_box
    (q : K F →ₜ* BoxModel (n := n) (D := D)) (hq : Surjective q) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
      (idelicHeckeCharactersInBox F q T).Finite ∧
      Nat.card (idelicHeckeCharactersInBox F q T) ≤
        (2 * ⌈C * T⌉₊ + 1) ^ n * Nat.card (PontryaginDual (Multiplicative D)) := by
  obtain ⟨C, hC, hb⟩ := exists_idelicTorusFrequency_bound F q hq
  refine ⟨C, hC, fun T hT ↦ ?_⟩
  let N := ⌈C * T⌉₊
  let B := {θ : PontryaginDual (BoxModel (n := n) (D := D)) |
    ∀ i, |compactElementaryCharacter_frequency θ i| ≤ (N : ℤ)}
  have hsub : idelicHeckeCharactersInBox F q T ⊆ B := by
    rintro θ ⟨χ, S, hs, hu, t, hθ, ht, hbox⟩ i
    have h := (hb χ S hs hu θ hθ t ht T hT hbox i).trans (Nat.le_ceil (C * T))
    exact_mod_cast h
  letI : Finite (PontryaginDual (Multiplicative D)) := inferInstance
  letI : Finite B := Finite.of_equiv _ (compactElementaryCharacter_boxEquiv (F := D) (n := n) N).symm
  have hB := Set.toFinite B
  exact ⟨hB.subset hsub, (Nat.card_mono hB hsub).trans_eq
    (compactElementaryCharacter_card_box (F := D) (n := n) N)⟩

set_option maxHeartbeats 900000 in
/-- Removing the two zero-dimensional factors of a compact stage keeps the
same quotient map kernel. -/
theorem exists_wholeBruhatStage_boxCoordinates
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (P : WholeBruhatStage G)
    (h : P.val.2.realDim = 0 ∧ P.val.2.latticeRank = 0) :
    ∃ q : G →ₜ* BoxModel (n := P.val.2.torusDim) (D := P.val.2.finiteFactor),
      Surjective q ∧ q.toMonoidHom.ker = P.val.1.kernel := by
  let A := WholeBruhatStage.coordinateModel P
  let B := ElementaryLCAModel 0 P.val.2.torusDim 0 P.val.2.finiteFactor
  let p : Multiplicative A →ₜ* Multiplicative B :=
    { toFun := fun x ↦ Multiplicative.ofAdd (0, x.toAdd.2.1, 0, x.toAdd.2.2.2)
      map_one' := rfl
      map_mul' := fun x y ↦ by
        change Multiplicative.ofAdd (0, x.toAdd.2.1 + y.toAdd.2.1, 0,
          x.toAdd.2.2.2 + y.toAdd.2.2.2) =
          Multiplicative.ofAdd ((0, x.toAdd.2.1, 0, x.toAdd.2.2.2) +
            (0, y.toAdd.2.1, 0, y.toAdd.2.2.2) : B)
        apply Multiplicative.toAdd.injective
        exact Prod.ext (Subsingleton.elim _ _)
          (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) rfl))
      continuous_toFun := continuous_ofAdd.comp (continuous_const.prodMk
        ((continuous_fst.comp (continuous_snd.comp continuous_toAdd)).prodMk
          (continuous_const.prodMk
            (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd)))))) }
  have hR : Subsingleton (EuclideanSpace ℝ (Fin P.val.2.realDim)) := by
    rw [h.1]
    infer_instance
  have hZ : Subsingleton (Fin P.val.2.latticeRank → ℤ) := by
    rw [h.2]
    infer_instance
  have hp : Injective p := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    refine Prod.ext (hR.elim _ _) (Prod.ext ?_ (Prod.ext (hZ.elim _ _) ?_))
    · exact congrArg (fun z : Multiplicative B ↦ z.toAdd.2.1) hxy
    · exact congrArg (fun z : Multiplicative B ↦ z.toAdd.2.2.2) hxy
  have hs : Surjective p := by
    intro y
    refine ⟨Multiplicative.ofAdd (0, y.toAdd.2.1, 0, y.toAdd.2.2.2), ?_⟩
    apply Multiplicative.toAdd.injective
    exact Prod.ext (Subsingleton.elim _ _)
      (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _) rfl))
  let Q : G →ₜ* Multiplicative A := P.coordinates
  have hQ : Q.toMonoidHom.ker = P.val.1.kernel := P.coordinates_ker
  have hker : (p.comp Q).toMonoidHom.ker = Q.toMonoidHom.ker := by
    apply SetLike.ext
    intro x
    change p (Q x) = 1 ↔ Q x = 1
    exact (congrArg (p (Q x) = ·) (map_one p)).symm.to_iff.trans hp.eq_iff
  exact ⟨p.comp Q, hs.comp P.coordinates_surjective, hker.trans hQ⟩

section CompactStage

local instance : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact

local instance : CompactSpace (K F) := normOneIdeleClass_compact F
local instance : T2Space (IdeleClass F) := ideleClasses_hausdorff

private theorem normOneRestriction_extension (ω : PontryaginDual (K F)) (x : K F) :
    normOneEulerCharacter F ω x.val = ω x := by
  change ω (ideleClassNormOnePart F x.val) = ω x
  congr 1
  apply Subtype.ext
  change x.val / ideleClassExpSection F (ideleClassLogNorm F x.val) = x.val
  have hx : ideleClassLogNorm F x.val = 1 := by
    change Multiplicative.ofAdd (Real.log (ideleClassNorm F x.val)) = _
    rw [x.property, Real.log_one]
    rfl
  rw [hx, map_one, div_one]

set_option maxHeartbeats 1200000 in
private theorem normOneAnnihilator_compactlyGenerated (H : Subgroup (K F))
    (hgen : IsCompactlyGeneratedGroup
      (lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype))) :
    IsCompactlyGeneratedGroup (lcaAnnihilator (G := K F) H) := by
  let J := lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype)
  let L := lcaAnnihilator (G := K F) H
  let ι : K F →ₜ* IdeleClass F := ⟨(normOneIdeleClass F).subtype, continuous_subtype_val⟩
  let r := PontryaginDual.map ι
  have hRmem (χ : J) : r χ.val ∈ L := by
    apply (mem_lcaAnnihilator_iff (G := K F) H _).mpr
    intro x
    change χ.val x.val.val = 1
    have hx : x.val.val ∈ H.map (normOneIdeleClass F).subtype :=
      ⟨x.val, x.property, rfl⟩
    exact (mem_lcaAnnihilator_iff (G := IdeleClass F) _ χ.val).mp χ.property ⟨_, hx⟩
  let R : J →* L := (r.toMonoidHom.comp J.subtype).codRestrict L hRmem
  have hR : Continuous R := (r.continuous.comp continuous_subtype_val).subtype_mk _
  have hs : Surjective R := by
    intro ω
    have hm : normOneEulerCharacter F ω.val ∈ J := by
      apply (mem_lcaAnnihilator_iff _ _).mpr
      rintro ⟨x, hx⟩
      obtain ⟨y, hy, rfl⟩ := hx
      change normOneEulerCharacter F ω.val y.val = 1
      exact (normOneRestriction_extension F ω.val y).trans
        ((mem_lcaAnnihilator_iff (G := K F) H _).mp ω.property ⟨y, hy⟩)
    refine ⟨⟨_, hm⟩, Subtype.ext (PontryaginDual.ext fun x ↦ ?_)⟩
    exact normOneRestriction_extension F ω.val x
  obtain ⟨A, hA, hAc, hAg⟩ := hgen
  letI : DiscreteTopology (PontryaginDual (K F)) :=
    (compactSpace_iff_discretePontryaginDual (G := K F)).mp inferInstance
  refine ⟨R '' A, (isOpen_discrete _).mem_nhds ⟨1, mem_of_mem_nhds hA, map_one R⟩,
    hAc.image hR, ?_⟩
  rw [← MonoidHom.map_closure, hAg, Subgroup.map_top_of_surjective R hs]

set_option maxHeartbeats 900000 in
/-- A compact norm-one subgroup whose ambient annihilator is compactly
generated is an elementary structural kernel on the norm-one classes. -/
theorem exists_normOneWholeBruhatStage (H : Subgroup (K F)) (hH : IsCompact (H : Set (K F)))
    (hgen : IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F)
      (H.map (normOneIdeleClass F).subtype))) :
    ∃ P : WholeBruhatStage (K F), P.val.1.kernel = H := by
  letI : DiscreteTopology (PontryaginDual (K F)) :=
    (compactSpace_iff_discretePontryaginDual (G := K F)).mp inferInstance
  let eTop : (⊤ : Subgroup (K F)) ≃ₜ* K F :=
    ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  have hcg : IsCompactlyGeneratedGroup (K F) :=
    ⟨univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩
  let J : OpenCompactlyGeneratedSubgroups (K F) :=
    ⟨⊤, isOpen_univ, compactGeneration_transport (A := K F) (B := ↥(⊤ : Subgroup (K F))) eTop.symm hcg⟩
  let B : LCAStructuralPair (K F) :=
    ⟨J, H, hH.isClosed, isOpen_discrete _, normOneAnnihilator_compactlyGenerated F H hgen, le_top⟩
  obtain ⟨e⟩ := B.quotient_elementary
  let P : WholeBruhatStage (K F) := ⟨⟨B, e⟩, rfl⟩
  exact ⟨P, rfl⟩

set_option maxHeartbeats 900000 in
/-- The compact norm-one invariance of a bounded family of Bruhat tests can be taken to
be the kernel of a whole compact elementary stage. It retains the same global
annihilator, so the uniform finite conductor bounds apply to its survivors. -/
theorem ideleClassMellin_exists_normOneStage_of_bounded
    (B : Set (BruhatCompactTest (IdeleClass F))) (hB : IsVonNBounded ℂ B) :
    ∃ P : WholeBruhatStage (K F),
      (P.val.2.realDim = 0 ∧ P.val.2.latticeRank = 0) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F)
        (P.val.1.kernel.map (normOneIdeleClass F).subtype)) ∧
      ∀ f ∈ B, ∀ k : P.val.1.kernel, ∀ x, f.val.val (k.val.val * x) = f.val.val x := by
  obtain ⟨H, hH, _, hgen, hInv⟩ := ideleClassMellin_exists_bounded_invariance F B hB
  obtain ⟨P, hP⟩ := exists_normOneWholeBruhatStage F H hH hgen
  refine ⟨P, wholeBruhatStage_compact_dimensions P, ?_, ?_⟩
  · rw [hP]
    exact hgen
  · intro f hf k x
    have hk : k.val ∈ H := hP ▸ k.property
    exact hInv f hf ⟨k.val, hk⟩ x

set_option maxHeartbeats 900000 in
/-- The compact norm-one invariance of an actual Bruhat test can be taken to
be the kernel of a whole compact elementary stage. It retains the same global
annihilator, so the uniform finite conductor bounds apply to its survivors. -/
theorem ideleClassMellin_exists_normOneStage (f : BruhatCompactTest (IdeleClass F)) :
    ∃ P : WholeBruhatStage (K F),
      (P.val.2.realDim = 0 ∧ P.val.2.latticeRank = 0) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F)
        (P.val.1.kernel.map (normOneIdeleClass F).subtype)) ∧
      ∀ k : P.val.1.kernel, ∀ x, f.val.val (k.val.val * x) = f.val.val x := by
  obtain ⟨P, hP, hg, hi⟩ :=
    ideleClassMellin_exists_normOneStage_of_bounded F {f} (isVonNBounded_singleton f)
  exact ⟨P, hP, hg, hi f (mem_singleton f)⟩

omit [Finite D] in
/-- A survivor of the compact invariance kernel determines a unique
character of the quotient, independently of its real norm twist. -/
theorem existsUnique_normOneHeckeCharacter_descends
    (q : K F →ₜ* BoxModel (n := n) (D := D)) (hq : Surjective q)
    (χ : PontryaginDual (IdeleClass F))
    (hχ : q.toMonoidHom.ker ≤ (heckeNormOneRestriction F χ).toMonoidHom.ker) :
    ∃! θ : PontryaginDual (BoxModel (n := n) (D := D)), ∀ x : K F, θ (q x) = χ x.val := by
  letI : T2Space (BoxModel (n := n) (D := D)) :=
    T2Space.of_injective_continuous Multiplicative.toAdd.injective continuous_toAdd
  let E := QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hq
  let ω := heckeNormOneRestriction F χ
  let d := (QuotientGroup.lift q.toMonoidHom.ker ω.toMonoidHom hχ).comp E.symm.toMonoidHom
  have hd (x : K F) : d (q x) = ω x := by
    change QuotientGroup.lift q.toMonoidHom.ker ω.toMonoidHom hχ
      (E.symm (E (QuotientGroup.mk x))) = ω x
    rw [E.symm_apply_apply]
    rfl
  have hdCont : Continuous d :=
    (q.continuous.isProperMap.isClosedMap.isQuotientMap q.continuous hq).continuous_iff.mpr
      (ω.continuous.congr fun x ↦ (hd x).symm)
  let θ : PontryaginDual (BoxModel (n := n) (D := D)) := ⟨d, hdCont⟩
  exact ⟨θ, hd, fun ψ hψ ↦ PontryaginDual.ext fun z ↦ by
    obtain ⟨x, rfl⟩ := hq z
    exact (hψ x).trans (hd x).symm⟩


/-- The distinct norm-one restrictions of the surviving Hecke characters in
an archimedean parameter box. -/
def normOneHeckeCharactersInBox (H : Subgroup (K F)) (T : ℝ) :
    Set (PontryaginDual (K F)) :=
  {ω | ω ∈ lcaAnnihilator (G := K F) H ∧
    ∃ (χ : PontryaginDual (IdeleClass F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
      (hs : Surjective (sIdeleClassInclusion F S))
      (hu : globalNormOneCharacter F (heckeNormOneRestriction F χ) ∈
        (sUnramified F S : Set (QuasiCharacter (IdeleClass F)))) (t : ℝ),
      heckeNormOneRestriction F χ = ω ∧ HasHeckeHeight F χ t ∧
        manuscriptHeckeArchParametersInBox F χ S hs hu t T}

set_option maxHeartbeats 900000 in
private def heckeFrequencyBoxEquiv (H : Subgroup (K F))
    (q : K F →ₜ* BoxModel (n := n) (D := D)) (hq : Surjective q)
    (hH : q.toMonoidHom.ker = H) (T : ℝ) :
    idelicHeckeCharactersInBox F q T ≃ normOneHeckeCharactersInBox F H T := by
  let pull (θ : idelicHeckeCharactersInBox F q T) : normOneHeckeCharactersInBox F H T := by
    refine ⟨PontryaginDual.map q θ.val, ?_⟩
    obtain ⟨χ, S, hs, hu, t, hθ, ht, hb⟩ := θ.property
    refine ⟨?_, χ, S, hs, hu, t, PontryaginDual.ext fun x ↦ (hθ x).symm, ht, hb⟩
    apply (mem_lcaAnnihilator_iff (G := K F) H _).mpr
    intro x
    have hx : q x.val = 1 := by
      change x.val ∈ q.toMonoidHom.ker
      rw [hH]
      exact x.property
    change θ.val (q x.val) = 1
    rw [hx, map_one]
  apply Equiv.ofBijective pull
  constructor
  · intro a b hab
    apply Subtype.ext
    apply PontryaginDual.ext
    intro y
    obtain ⟨x, rfl⟩ := hq y
    exact congrArg (fun ω : normOneHeckeCharactersInBox F H T ↦ ω.val x) hab
  · intro ω
    obtain ⟨hω, χ, S, hs, hu, t, hχ, ht, hb⟩ := ω.property
    have hker : q.toMonoidHom.ker ≤ (heckeNormOneRestriction F χ).toMonoidHom.ker := by
      rw [hH, hχ]
      intro x hx
      exact (mem_lcaAnnihilator_iff (G := K F) H ω.val).mp hω ⟨x, hx⟩
    obtain ⟨θ, hθ, _⟩ := existsUnique_normOneHeckeCharacter_descends F q hq χ hker
    refine ⟨⟨θ, χ, S, hs, hu, t, hθ, ht, hb⟩, Subtype.ext (PontryaginDual.ext fun x ↦ ?_)⟩
    exact (hθ x).trans (congrArg (fun ψ : PontryaginDual (K F) ↦ ψ x) hχ)

private theorem normOneHeckeCharacters_card_box_of_coordinates (H : Subgroup (K F))
    (q : K F →ₜ* BoxModel (n := n) (D := D)) (hq : Surjective q)
    (hker : q.toMonoidHom.ker = H) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T →
      (normOneHeckeCharactersInBox F H T).Finite ∧
      Nat.card (normOneHeckeCharactersInBox F H T) ≤
        (2 * ⌈C * T⌉₊ + 1) ^ n * Nat.card (PontryaginDual (Multiplicative D)) := by
  obtain ⟨C, hC, hbox⟩ := exists_idelicHeckeCharacters_card_box F q hq
  refine ⟨C, hC, fun T hT ↦ ?_⟩
  obtain ⟨hfin, hcard⟩ := hbox T hT
  let e := heckeFrequencyBoxEquiv F H q hq hker T
  letI := hfin.to_subtype
  letI : Finite (normOneHeckeCharactersInBox F H T) := Finite.of_equiv _ e
  exact ⟨Set.toFinite _, (Nat.card_congr e).symm.trans_le hcard⟩

set_option maxHeartbeats 1100000 in
/-- For a bounded family of compact Bruhat tests, one invariance kernel works for
both the global annihilator and the polynomial count of distinct norm-one
components in any archimedean parameter box. -/
theorem ideleClassMellin_normOneCharacters_card_box_of_bounded
    (B : Set (BruhatCompactTest (IdeleClass F))) (hB : IsVonNBounded ℂ B) :
    ∃ (H : Subgroup (K F)) (C : ℝ) (n M : ℕ), 0 < C ∧
      IsCompact (H : Set (K F)) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F)
        (H.map (normOneIdeleClass F).subtype)) ∧
      (∀ f ∈ B, ∀ k : H, ∀ x, f.val.val (k.val.val * x) = f.val.val x) ∧
      ∀ T : ℝ, 0 ≤ T → (normOneHeckeCharactersInBox F H T).Finite ∧
        Nat.card (normOneHeckeCharactersInBox F H T) ≤ (2 * ⌈C * T⌉₊ + 1) ^ n * M := by
  obtain ⟨P, hP, hgen, hInv⟩ := ideleClassMellin_exists_normOneStage_of_bounded F B hB
  obtain ⟨q, hq, hker⟩ := exists_wholeBruhatStage_boxCoordinates (G := K F) P hP
  obtain ⟨C, hC, hbox⟩ := normOneHeckeCharacters_card_box_of_coordinates F
    (n := P.val.2.torusDim) (D := P.val.2.finiteFactor) P.val.1.kernel q hq hker
  exact ⟨P.val.1.kernel, C, P.val.2.torusDim,
      Nat.card (PontryaginDual (Multiplicative P.val.2.finiteFactor)), hC,
      P.val.1.kernel_closed.isCompact, hgen, hInv, hbox⟩


set_option maxHeartbeats 1100000 in
/-- For every actual compact Bruhat test, one invariance kernel works for
both the global annihilator and the polynomial count of distinct norm-one
components in any archimedean parameter box. -/
theorem ideleClassMellin_normOneCharacters_card_box (f : BruhatCompactTest (IdeleClass F)) :
    ∃ (H : Subgroup (K F)) (C : ℝ) (n M : ℕ), 0 < C ∧
      IsCompact (H : Set (K F)) ∧
      IsCompactlyGeneratedGroup (lcaAnnihilator (G := IdeleClass F)
        (H.map (normOneIdeleClass F).subtype)) ∧
      (∀ k : H, ∀ x, f.val.val (k.val.val * x) = f.val.val x) ∧
      ∀ T : ℝ, 0 ≤ T → (normOneHeckeCharactersInBox F H T).Finite ∧
        Nat.card (normOneHeckeCharactersInBox F H T) ≤ (2 * ⌈C * T⌉₊ + 1) ^ n * M := by
  obtain ⟨H, C, n, M, hC, hc, hg, hi, hbox⟩ :=
    ideleClassMellin_normOneCharacters_card_box_of_bounded F {f} (isVonNBounded_singleton f)
  exact ⟨H, C, n, M, hC, hc, hg, hi f (mem_singleton f), hbox⟩

end CompactStage

end
end Masullo
