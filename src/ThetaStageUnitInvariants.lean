import AdelicPolarDistributions
import GlobalThetaStageRetraction
import PointwiseLinearSeries
import SLocalThetaStrictFrechet
import SLocalUnramifiedThetaRange

open Bornology Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E (S : Finset (Place F)) := SLocalThetaQuotient F S

private def blockProjection (S : Finset (Place F)) : Idele F →* (SAdeles F S)ˣ :=
  Units.map (sAdelesProjection F S).toMonoidHom

/-- The global integral units with trivial archimedean and selected coordinates. -/
def thetaIntegralTailUnits (S : Finset (Place F)) : Subgroup (Idele F) :=
  sIdeleBlock F S ⊓ (blockProjection F S).ker

/-- The same group restricted to the additional coordinates of a finite stage. -/
def thetaRelativeIntegralUnits (S T : Finset (Place F)) : Subgroup (SAdeles F T)ˣ :=
  (thetaIntegralTailUnits F S).comap ((sIdeleBlock F T).subtype.comp (sLocalEmbed F T))

theorem mem_thetaIntegralTailUnits_iff (S : Finset (Place F)) (g : Idele F) :
    g ∈ thetaIntegralTailUnits F S ↔
      g.val.1 = 1 ∧ (∀ w : S, g.val.2 w.val = 1) ∧
        ∀ w ∉ S, g.val.2 w ∈ w.adicCompletionIntegers F ∧
          g.inv.2 w ∈ w.adicCompletionIntegers F := by
  change (_ ∧ blockProjection F S g = 1) ↔ _
  have hunit : blockProjection F S g = 1 ↔
      g.val.1 = 1 ∧ ∀ w : S, g.val.2 w.val = 1 := by
    constructor
    · intro h
      have hv := congrArg Units.val h
      exact ⟨congrArg Prod.fst hv, fun w ↦ congrFun (congrArg Prod.snd hv) w⟩
    · rintro ⟨ha,hf⟩
      exact Units.ext (Prod.ext ha (funext hf))
  rw [hunit]
  change ((_ ∧ _) ∧ _) ↔ _
  constructor
  · rintro ⟨⟨hv,hi⟩,ha,hf⟩
    exact ⟨ha,hf,fun w hw ↦ ⟨hv w hw, hi w hw⟩⟩
  · rintro ⟨ha,hf,hv⟩
    exact ⟨⟨fun w hw ↦ (hv w hw).1, fun w hw ↦ (hv w hw).2⟩,ha,hf⟩

/-- The relative unit subgroup has trivial coordinates on the smaller
block and arbitrary integral-unit coordinates at the new places. -/
theorem mem_thetaRelativeIntegralUnits_iff {S T : Finset (Place F)} (hST : S ⊆ T)
    (a : (SAdeles F T)ˣ) :
    a ∈ thetaRelativeIntegralUnits F S T ↔
      a.val.1 = 1 ∧ (∀ w : S, a.val.2 ⟨w.val,hST w.property⟩ = 1) ∧
        ∀ w : T, w.val ∉ S → a.val.2 w ∈ w.val.adicCompletionIntegers F ∧
          a.inv.2 w ∈ w.val.adicCompletionIntegers F := by
  let g := (sLocalEmbed F T a).val
  change g ∈ thetaIntegralTailUnits F S ↔ _
  have hi (w : T) : g.inv.2 w.val = a.inv.2 w := by
    have h := sLocalEmbed_finite F T a⁻¹ w
    rw [map_inv] at h
    exact h
  rw [mem_thetaIntegralTailUnits_iff, sLocalEmbed_arch]
  have hf (w : S) : g.val.2 w.val = a.val.2 ⟨w.val,hST w.property⟩ :=
    sLocalEmbed_finite F T a ⟨w.val,hST w.property⟩
  simp only [hf]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨?_,?_⟩
  · intro h w hw
    rw [← sLocalEmbed_finite F T a w, ← hi w]
    exact h w.val hw
  · intro h w hw
    by_cases hT : w ∈ T
    · let v : T := ⟨w,hT⟩
      rw [show g.val.2 w = a.val.2 v from sLocalEmbed_finite F T a v,
        show g.inv.2 w = a.inv.2 v from hi v]
      exact h v hw
    · exact ⟨(sLocalEmbed F T a).property.1 w hT, (sLocalEmbed F T a).property.2 w hT⟩

private theorem singleUnit_mem_tail (S : Finset (Place F)) {v : Place F} (hv : v ∉ S)
    (u : (v.adicCompletion F)ˣ) (hu : u ∈ finitePlaceIntegralUnits F v) :
    singleFiniteIdele F v u ∈ thetaIntegralTailUnits F S := by
  have hu' := (Submonoid.mem_units_iff (v.adicCompletionIntegers F).toSubmonoid u).mp hu
  have hvalue (a : (v.adicCompletion F)ˣ) :
      (singleFiniteIdele F v a).val.2 v = a.val := by
    change Function.update (fun w : Place F ↦ (1 : w.adicCompletion F)) v a.val v = a.val
    exact Function.update_self _ _ _
  have hother (a : (v.adicCompletion F)ˣ) (w : Place F) (hw : w ≠ v) :
      (singleFiniteIdele F v a).val.2 w = 1 := by
    change Function.update (fun j : Place F ↦ (1 : j.adicCompletion F)) v a.val w = 1
    exact Function.update_of_ne hw _ _
  have hinv : (singleFiniteIdele F v u).inv = (singleFiniteIdele F v u⁻¹).val := rfl
  have hmem (a : (v.adicCompletion F)ˣ) (ha : a.val ∈ v.adicCompletionIntegers F) (w : Place F) :
      (singleFiniteIdele F v a).val.2 w ∈ w.adicCompletionIntegers F := by
    by_cases h : w = v
    · subst w
      rwa [hvalue]
    · rw [hother a w h]
      exact one_mem _
  refine ⟨⟨fun w _ ↦ hmem u hu'.1 w, fun w _ ↦ by
    change (singleFiniteIdele F v u).inv.2 w ∈ w.adicCompletionIntegers F
    rw [hinv]
    exact hmem u⁻¹ hu'.2 w⟩, ?_⟩
  change blockProjection F S (singleFiniteIdele F v u) = 1
  apply Units.ext
  change sAdelesProjection F S (singleFiniteIdele F v u).val = (1 : SAdeles F S)
  refine Prod.ext rfl ?_
  funext w
  exact hother u w.val fun h ↦ hv (h ▸ w.property)

private theorem thetaToGlobal_fixed_tail (S : Finset (Place F))
    (q : E F S) (a : thetaIntegralTailUnits F S) :
    globalThetaTranslate F (ideleClassMap F a.val) (sLocalThetaToGlobal F S q) =
      sLocalThetaToGlobal F S q := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let b : sIdeleBlock F S := ⟨a.val,a.property.1⟩
  have hproj : (sBlockUnitProduct F S b).1 = 1 := a.property.2
  rw [sLocalThetaToGlobal_mk, globalThetaTranslate_class, globalThetaTranslateIdeles_mk]
  change (Submodule.Quotient.mk (GlobalBruhat.leftTranslate F b.val f.val) : GlobalThetaQuotient F) =
    Submodule.Quotient.mk f.val
  rw [bruhatTranslate_block_eq F S b f, hproj, map_one]
  change (Submodule.Quotient.mk (GlobalBruhat.leftTranslate F 1 f.val) : GlobalThetaQuotient F) =
    Submodule.Quotient.mk f.val
  rw [← globalThetaTranslateIdeles_mk, ← globalThetaTranslate_class, map_one,
    globalThetaTranslate_one]
  rfl

private theorem exists_thetaStageRepresentative_onePlace (S : Finset (Place F)) (v : Place F) (hv : v ∉ S)
    (hS : Surjective (sIdeleClassInclusion F S)) (q : E F (insert v S))
    (hq : ∀ u : (v.adicCompletion F)ˣ, u ∈ finitePlaceIntegralUnits F v →
      globalThetaTranslate F (ideleClassMap F (singleFiniteIdele F v u))
        (sLocalThetaToGlobal F (insert v S) q) = sLocalThetaToGlobal F (insert v S) q) :
    ∃ p : E F S, sLocalThetaToGlobal F S p = sLocalThetaToGlobal F (insert v S) q := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let L := (globalThetaOperator F).ker.mkQ
  have hfixed (u : (v.adicCompletion F)ˣ) (hu : u ∈ finitePlaceIntegralUnits F v) :
      L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v u) f.val) = L f.val := by
    have h := hq u hu
    rwa [sLocalThetaToGlobal_mk, globalThetaTranslate_class, globalThetaTranslateIdeles_mk] at h
  have hshift (n : ℤ) (g : sLocalBruhatImage F S) :
      ∃ b : sLocalBruhatImage F S,
        L (GlobalBruhat.leftTranslate F (singleFiniteIdele F v (chosenFiniteUniformizer F v ^ n)) g.val) =
          L b.val := by
    let d := singleFiniteIdele F v (chosenFiniteUniformizer F v ^ n)
    obtain ⟨c,hc⟩ := hS (ideleClassMap F d)
    let p := sLocalThetaTranslate F S (sIdeleClassToLocal F S c) (Submodule.Quotient.mk g)
    obtain ⟨b,hb⟩ := Submodule.Quotient.mk_surjective _ p
    refine ⟨b, ?_⟩
    have he := sLocalThetaToGlobal_translate_blockClass F S c (Submodule.Quotient.mk g)
    change sLocalThetaToGlobal F S p = _ at he
    rw [← hb, hc, sLocalThetaToGlobal_mk, sLocalThetaToGlobal_mk,
      globalThetaTranslate_class, globalThetaTranslateIdeles_mk] at he
    exact he.symm
  obtain ⟨p,hp⟩ := exists_sLocalBaseRepresentative_onePlace_of_fixed F S v hv L f hfixed hshift
  exact ⟨Submodule.Quotient.mk p, hp.symm⟩

private theorem thetaStageRepresentative_union (S : Finset (Place F))
    (hS : Surjective (sIdeleClassInclusion F S)) (q : GlobalThetaQuotient F)
    (B : Finset (Place F)) (hB : Disjoint B S)
    (hq : ∀ v ∈ B, ∀ u : (v.adicCompletion F)ˣ, u ∈ finitePlaceIntegralUnits F v →
      globalThetaTranslate F (ideleClassMap F (singleFiniteIdele F v u)) q = q)
    (hx : q ∈ range (sLocalThetaToGlobal F (B ∪ S))) :
    q ∈ range (sLocalThetaToGlobal F S) := by
  induction B using Finset.induction_on with
  | empty =>
    rwa [Finset.empty_union] at hx
  | insert v B hv ih =>
    obtain ⟨hvS,hBS⟩ := Finset.disjoint_insert_left.mp hB
    have hvA : v ∉ B ∪ S := by simp [hv,hvS]
    rw [Finset.insert_union] at hx
    obtain ⟨x,hx⟩ := hx
    obtain ⟨p,hp⟩ := exists_thetaStageRepresentative_onePlace F (B ∪ S) v hvA
      (sIdeleClassInclusion_surjective_mono F Finset.subset_union_right hS)
      x (by
        intro u hu
        rw [hx]
        exact hq v (Finset.mem_insert_self _ _) u hu)
    exact ih hBS (fun w hw ↦ hq w (Finset.mem_insert_of_mem hw)) ⟨p,hp.trans hx⟩

/-- The image in the actual global theta quotient is the fixed subspace
for the omitted integral units whenever the S-block meets all idele classes. -/
theorem sLocalThetaToGlobal_range_eq_unitFixed (S : Finset (Place F))
    (hS : Surjective (sIdeleClassInclusion F S)) :
    range (sLocalThetaToGlobal F S) =
      {q | ∀ a : thetaIntegralTailUnits F S, globalThetaTranslate F (ideleClassMap F a.val) q = q} := by
  ext q
  constructor
  · rintro ⟨x,rfl⟩ a
    exact thetaToGlobal_fixed_tail F S x a
  · intro hq
    obtain ⟨T,hST,_,x,hx⟩ := globalThetaQuotient_exhausted_by_different_stages F S q
    apply thetaStageRepresentative_union F S hS q (T \ S) Finset.sdiff_disjoint
    · intro v hv u hu
      exact hq ⟨_, singleUnit_mem_tail F S (Finset.mem_sdiff.mp hv).2 u hu⟩
    · rw [Finset.sdiff_union_of_subset hST]
      exact ⟨x,hx⟩

/-- The image in a larger finite theta stage is precisely the fixed subspace
for the integral units in its additional coordinates. -/
theorem sLocalThetaTransition_range_eq_unitFixed {S T : Finset (Place F)} (hST : S ⊆ T)
    (hS : Surjective (sIdeleClassInclusion F S)) :
    range (sLocalThetaTransition F hST) =
      {q | ∀ a : thetaRelativeIntegralUnits F S T, sLocalThetaTranslate F T (QuotientGroup.mk a.val) q = q} := by
  ext q
  constructor
  · rintro ⟨x,rfl⟩ a
    apply sLocalThetaToGlobal_injective F T
    rw [sLocalThetaToGlobal_translate_class, sLocalThetaToGlobal_transition]
    exact thetaToGlobal_fixed_tail F S x ⟨_,a.property⟩
  · intro hq
    let y := sLocalThetaToGlobal F T q
    have hr : ∃ x : E F S, sLocalThetaToGlobal F S x = y := by
      have hfixed (v : Place F) (hv : v ∈ T \ S) (u : (v.adicCompletion F)ˣ)
          (hu : u ∈ finitePlaceIntegralUnits F v) :
          globalThetaTranslate F (ideleClassMap F (singleFiniteIdele F v u)) y = y := by
        let a := Units.map (sAdelesProjection F T).toMonoidHom (singleFiniteIdele F v u)
        have ha := singleFiniteIdele_embedded_of_mem F v (Finset.mem_sdiff.mp hv).1 u
        have ha' : a ∈ thetaRelativeIntegralUnits F S T := by
          change (sLocalEmbed F T a).val ∈ thetaIntegralTailUnits F S
          rw [ha]
          exact singleUnit_mem_tail F S (Finset.mem_sdiff.mp hv).2 u hu
        have h := congrArg (sLocalThetaToGlobal F T) (hq ⟨a,ha'⟩)
        rw [sLocalThetaToGlobal_translate_class,ha] at h
        exact h
      apply thetaStageRepresentative_union F S hS y (T \ S) Finset.sdiff_disjoint hfixed
      rw [Finset.sdiff_union_of_subset hST]
      exact ⟨q,rfl⟩
    obtain ⟨x,hx⟩ := hr
    refine ⟨x,sLocalThetaToGlobal_injective F T ?_⟩
    rwa [sLocalThetaToGlobal_transition]

/-- Theorem 6.1.2.1 on the ordinary theta quotients, with the exact relative
and global integral-unit groups. Both fixed subspaces are closed and carry
the topology of the inserted stage. -/
theorem thetaStage_closedUnitFixed_of_trivialPicard {S T : Finset (Place F)}
    (hST : S ⊆ T) [Subsingleton (SPicardGroup F S)] :
    IsClosedEmbedding (sLocalThetaTransition F hST) ∧
      range (sLocalThetaTransition F hST) =
        {q | ∀ a : thetaRelativeIntegralUnits F S T,
          sLocalThetaTranslate F T (QuotientGroup.mk a.val) q = q} ∧
      IsClosedEmbedding (sLocalThetaToGlobal F S) ∧
      range (sLocalThetaToGlobal F S) =
        {q | ∀ a : thetaIntegralTailUnits F S,
          globalThetaTranslate F (ideleClassMap F a.val) q = q} :=
  ⟨sLocalThetaTransition_isClosedEmbedding F hST,
    sLocalThetaTransition_range_eq_unitFixed F hST (sIdeleClassInclusion_surjective_of_subsingleton_sPicard F S),
    sLocalThetaToGlobal_isClosedEmbedding F S,
    sLocalThetaToGlobal_range_eq_unitFixed F S (sIdeleClassInclusion_surjective_of_subsingleton_sPicard F S)⟩

/-- A padded principal coset contributes one continuous evaluation on the
smaller theta quotient, subject to the outside-place integrality test. -/
def thetaPaddingCosetEval (S : Finset (Place F)) (g : Idele F) (t : Fˣ) : E F S →L[ℂ] ℂ :=
  let y := principalIdele F t * g
  let p := Units.map (sAdelesProjection F S).toMonoidHom y
  if y.val ∈ globalIntegralSubring F S then sLocalThetaQuotientEval F S p else 0

theorem thetaPaddingCosetEval_mk (S : Finset (Place F)) (g : Idele F) (t : Fˣ)
    (f : sLocalBruhatImage F S) :
    thetaPaddingCosetEval F S g t (Submodule.Quotient.mk f) = globalThetaPaddingCosetTerm F S f g t := by
  dsimp only [thetaPaddingCosetEval, globalThetaPaddingCosetTerm]
  split_ifs <;> rfl

private theorem hasSumUniformlyOn_thetaPadding {ι : Type*} (S : Finset (Place F))
    (L : ι → E F S →L[ℂ] ℂ) (G : E F S → ℂ)
    (h : ∀ x, HasSum (fun i ↦ L i x) (G x))
    {B : Set (E F S)} (hB : IsVonNBounded ℂ B) :
    HasSumUniformlyOn (fun i x ↦ L i x) G B := by
  letI : UniformSpace (E F S) := IsTopologicalAddGroup.rightUniformSpace _
  letI : IsUniformAddGroup (E F S) := isUniformAddGroup_of_addCommGroup
  letI : BarrelledSpace ℂ (E F S) := sLocalThetaQuotient_barrelled F S
  letI : ContinuousSMul ℂ (E F S) :=
    (sLocalThetaQuotient_nuclear F S).2.1.withSeminorms.continuousSMul
  obtain ⟨R,hR⟩ := exists_continuousLinearMap_hasSum_pointwise L (fun x ↦ (h x).summable)
  have he : (fun x ↦ R x) = G := funext fun x ↦ (hR x).unique (h x)
  rw [← he]
  exact hasSumUniformlyOn_of_linear_pointwise L R hR
    (nuclearLocallyConvex_totallyBounded (sLocalThetaQuotient_nuclear F S) hB)

/-- The adelic theta values descend to the ordinary global quotient. -/
def globalThetaOnQuotient : GlobalThetaQuotient F →ₗ[ℂ] (IdeleClass F → ℂ) :=
  (globalThetaOperator F).ker.liftQ (globalThetaOperator F) le_rfl

/-- The global orbit sum for padding converges uniformly on bounded
source classes at every fixed evaluation idele. -/
theorem hasSumUniformlyOn_globalThetaPaddingCosets (S : Finset (Place F)) (g : Idele F)
    (r : (Fˣ ⧸ (sUnitToField F S).range) → Fˣ) (hr : ∀ q, QuotientGroup.mk (r q) = q)
    {B : Set (E F S)} (hB : IsVonNBounded ℂ B) :
    HasSumUniformlyOn (fun i q ↦ thetaPaddingCosetEval F S g (r i) q)
      (fun q ↦ globalThetaOnQuotient F (sLocalThetaToGlobal F S q) (ideleClassMap F g)) B := by
  apply hasSumUniformlyOn_thetaPadding F S (fun i ↦ thetaPaddingCosetEval F S g (r i)) _ _ hB
  intro q
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [thetaPaddingCosetEval_mk]
  exact hasSum_globalThetaPaddingCosets F S f g r hr

/-- The finite enlargement has the same bounded-uniform summation
statement, using cosets of the two S-unit groups. -/
theorem hasSumUniformlyOn_sLocalThetaPaddingCosets {S T : Finset (Place F)} (hST : S ⊆ T)
    (g : (SAdeles F T)ˣ)
    (r : ((sIntegerRing F T)ˣ ⧸ (sUnitInclusion F hST).range) → (sIntegerRing F T)ˣ)
    (hr : ∀ q, QuotientGroup.mk (r q) = q)
    {B : Set (E F S)} (hB : IsVonNBounded ℂ B) :
    HasSumUniformlyOn
      (fun i q ↦ thetaPaddingCosetEval F S (sLocalEmbed F T g).val (sUnitToField F T (r i)) q)
      (fun q ↦ sLocalThetaQuotientEval F T g (sLocalThetaTransition F hST q)) B := by
  apply hasSumUniformlyOn_thetaPadding F S
    (fun i ↦ thetaPaddingCosetEval F S (sLocalEmbed F T g).val (sUnitToField F T (r i))) _ _ hB
  intro q
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [thetaPaddingCosetEval_mk]
  exact hasSum_sLocalThetaPaddingCosets F hST f g r hr

/-- The printed global operator inverse cannot exist. The ordinary
theta quotient is nonzero, as detected by the polar evaluations. -/
theorem globalTheta_principalDifference_no_leftInverse (t : Fˣ) :
    ¬ ∃ L : GlobalThetaQuotient F → GlobalThetaQuotient F,
      LeftInverse L ((ContinuousLinearMap.id ℂ (GlobalThetaQuotient F) -
        globalThetaTranslate F (ideleClassMap F (principalIdele F t)) :
        GlobalThetaQuotient F →L[ℂ] GlobalThetaQuotient F) :
        GlobalThetaQuotient F → GlobalThetaQuotient F) := by
  rw [globalTheta_principalDifference_zero]
  obtain ⟨q,hq⟩ := globalThetaPolarEvaluation_surjective F (1, 0)
  rintro ⟨L,hL⟩
  have h : q = 0 := (hL q).symm.trans (hL 0)
  rw [h,map_zero] at hq
  exact one_ne_zero (congrArg Prod.fst hq).symm

end
end Masullo
