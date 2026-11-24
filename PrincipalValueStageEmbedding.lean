import GlobalThetaStageRetraction
import PrincipalValueEquivariance
import GlobalWeilUnitAverage
import SLocalThetaStrictFrechet

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev E (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev Q (S : Finset (Place F)) := SLocalThetaQuotient F S
private abbrev G := GlobalThetaQuotient F

/-- The canonical principal-value product on a finite ordinary theta quotient. -/
def sLocalThetaPrincipalValues (S : Finset (Place F)) (W : Finset S) :
    Q F S →L[ℂ] Q F S :=
  (existsUnique_sLocalWeilPrincipalValuesQuotient F S W).exists.choose

theorem sLocalThetaPrincipalValues_injective (S : Finset (Place F)) (W : Finset S) :
    Injective (sLocalThetaPrincipalValues F S W) :=
  (existsUnique_sLocalWeilPrincipalValuesQuotient F S W).exists.choose_spec.1

@[simp] theorem sLocalThetaPrincipalValues_mk (S : Finset (Place F)) (W : Finset S)
    (f : E F S) :
    sLocalThetaPrincipalValues F S W (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sLocalWeilPrincipalValues F S W f) :=
  (existsUnique_sLocalWeilPrincipalValuesQuotient F S W).exists.choose_spec.2 f

private abbrev project (S : Finset (Place F)) : Idele F →* (SAdeles F S)ˣ :=
  Units.map (sAdelesProjection F S).toMonoidHom

private abbrev U (w : Place F) := ↥(principalIntegralUnits F w)

private def principalTranslateArgument (w : Place F) (u : U F w) : Idele F :=
  singleFiniteIdele F w (chosenFiniteUniformizer F w * u.val)

private theorem principalTranslateArgument_mul (w : Place F) (u : U F w) :
    principalTranslateArgument F w u = singleFiniteIdele F w (chosenFiniteUniformizer F w) *
      singleFiniteIdele F w u.val :=
  singleFiniteIdele_mul F w _ _

private theorem globalTranslate_into_stage (S : Finset (Place F)) (w : S)
    (u : (w.val.adicCompletion F)ˣ) (q : Q F S) :
    globalThetaTranslateIdeles F (singleFiniteIdele F w.val u) (sLocalThetaToGlobal F S q) =
      sLocalThetaToGlobal F S
        (sLocalThetaTranslateIdeles F S (project F S (singleFiniteIdele F w.val u)) q) := by
  rw [sLocalThetaToGlobal_translate, singleFiniteIdele_embedded_of_mem F w.val w.property u]

/-- Scalar pairing with the one-place quotient operator is identity minus
Haar averaging of the uniformizer-shifted unit orbit. -/
theorem sLocalThetaPrincipalValue_pairing (S : Finset (Place F)) (w : S)
    (q : Q F S) (ℓ : Q F S →ₗ[ℂ] ℂ) :
    ℓ (sLocalThetaPrincipalValues F S {w} q) =
      ℓ q - ∫ u : U F w.val, ℓ (sLocalThetaTranslateIdeles F S
        (project F S (principalTranslateArgument F w.val u)) q) ∂principalUnitHaar F w.val := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨R,hR⟩ := sLocalThetaToGlobal_exists_retraction F S
  let N := (globalThetaOperator F).ker
  let B := ℓ.comp (R.toLinearMap.comp N.mkQ)
  have hB (x : E F S) : B x.val = ℓ (Submodule.Quotient.mk x) :=
    congrArg ℓ (hR (Submodule.Quotient.mk x))
  rw [sLocalThetaPrincipalValues_mk]
  have hs : sLocalWeilPrincipalValues F S ({w} : Finset S) = sLocalWeilPrincipalValue F S w :=
    Finset.noncommProd_singleton _ _
  rw [hs, ← hB, ← globalWeilPrincipalValue_stage F S w,
    globalWeilPrincipalValue_eq_unitAverage, map_sub, hB]
  let D := GlobalBruhat.leftTranslate F (singleFiniteIdele F w.val (chosenFiniteUniformizer F w.val))
  have hI := (globalFiniteUnitAverage_pairing F w.val f.val (B.comp D.toLinearMap)).2
  change ℓ (Submodule.Quotient.mk f) -
    (B.comp D.toLinearMap) (globalFiniteUnitAverage F w.val f.val) = _
  rw [hI]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  change B (D (GlobalBruhat.leftTranslate F (singleFiniteIdele F w.val u.val) f.val)) = _
  rw [show D (GlobalBruhat.leftTranslate F (singleFiniteIdele F w.val u.val) f.val) =
    GlobalBruhat.leftTranslate F (principalTranslateArgument F w.val u) f.val by
      dsimp only [D]
      rw [globalBruhatLeftTranslate_mul, principalTranslateArgument_mul]]
  change ℓ (R (Submodule.Quotient.mk
    (GlobalBruhat.leftTranslate F (principalTranslateArgument F w.val u) f.val))) = _
  rw [← globalThetaTranslateIdeles_mk]
  change ℓ (R (globalThetaTranslateIdeles F (principalTranslateArgument F w.val u)
      (sLocalThetaToGlobal F S (Submodule.Quotient.mk f)))) = _
  unfold principalTranslateArgument
  rw [globalTranslate_into_stage F S w, hR]

private def insertIndex (S : Finset (Place F)) (v : Place F) : S ↪ ↥(insert v S) :=
  ⟨fun w ↦ ⟨w.val, Finset.mem_insert_of_mem w.property⟩, fun _ _ h ↦
    Subtype.ext (congrArg (fun x : (insert v S : Finset (Place F)) ↦ x.val) h)⟩

private theorem sLocalThetaStageRetraction_principalValue (S : Finset (Place F))
    (v : Place F) (hv : v ∉ S) (w : S) (q : Q F (insert v S)) :
    let R := sLocalThetaStageRetraction F S v hv
    R (sLocalThetaPrincipalValues F (insert v S) {insertIndex F S v w} q) =
      sLocalThetaPrincipalValues F S {w} (R q) := by
  intro R
  by_contra hn
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hn)
  apply hℓ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hT := sLocalThetaPrincipalValue_pairing F (insert v S) (insertIndex F S v w) q
    (ℓ.comp R.toLinearMap)
  have hS := sLocalThetaPrincipalValue_pairing F S w (R q) ℓ
  change (ℓ.comp R.toLinearMap) (sLocalThetaPrincipalValues F (insert v S) {insertIndex F S v w} q) = _
  rw [hT, hS]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  let d := principalTranslateArgument F w.val u
  let a := project F S d
  have ha : (sLocalEmbed F S a).val = d :=
    singleFiniteIdele_embedded_of_mem F w.val w.property _
  change ℓ (R (sLocalThetaTranslateIdeles F (insert v S) (project F (insert v S) d) q)) =
    ℓ (sLocalThetaTranslateIdeles F S a (R q))
  have h := sLocalThetaStageRetraction_translate F S v hv a q
  change R (sLocalThetaTranslateIdeles F (insert v S)
      (project F (insert v S) (sLocalEmbed F S a).val) q) = _ at h
  rw [ha] at h
  exact congrArg ℓ h

private theorem sLocalThetaPrincipalValues_insert (S : Finset (Place F)) (w : S)
    (W : Finset S) (hw : w ∉ W) (q : Q F S) :
    sLocalThetaPrincipalValues F S (insert w W) q =
      sLocalThetaPrincipalValues F S {w} (sLocalThetaPrincipalValues F S W q) := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [sLocalThetaPrincipalValues_mk]
  congr 1
  have hx : sLocalWeilPrincipalValues F S (insert w W) =
      sLocalWeilPrincipalValue F S w * sLocalWeilPrincipalValues F S W :=
    Finset.noncommProd_insert_of_notMem W w _ _ hw
  have hs : sLocalWeilPrincipalValues F S ({w} : Finset S) = sLocalWeilPrincipalValue F S w :=
    Finset.noncommProd_singleton _ _
  rw [hx,hs]
  rfl

/-- The chosen continuous one-place left inverse of stage insertion
intertwines the full product at the previously selected places. -/
theorem sLocalThetaStageRetraction_principalValues (S : Finset (Place F))
    (v : Place F) (hv : v ∉ S) (W : Finset S) (q : Q F (insert v S)) :
    let R := sLocalThetaStageRetraction F S v hv
    R (sLocalThetaPrincipalValues F (insert v S) (W.map (insertIndex F S v)) q) =
      sLocalThetaPrincipalValues F S W (R q) := by
  intro R
  induction W using Finset.induction_on generalizing q with
  | empty =>
    have h (A : Finset (Place F)) (x : Q F A) : sLocalThetaPrincipalValues F A ∅ x = x := by
      obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [sLocalThetaPrincipalValues_mk]
      have he : sLocalWeilPrincipalValues F A ∅ = 1 := Finset.noncommProd_empty _ _
      rw [he]
      rfl
    rw [Finset.map_empty, h, h]
  | insert w W hw ih =>
    rw [Finset.map_insert, sLocalThetaPrincipalValues_insert _ _ _ _ (by simpa using hw),
      sLocalThetaPrincipalValues_insert _ _ _ _ hw]
    change sLocalThetaStageRetraction F S v hv _ = _
    rw [sLocalThetaStageRetraction_principalValue]
    exact congrArg (sLocalThetaPrincipalValues F S {w}) (ih q)

/-- The selected global places viewed as coordinates of a finite stage. -/
def thetaPrincipalValueSelection (S W : Finset (Place F)) : Finset S :=
  Finset.univ.filter fun w ↦ w.val ∈ W

omit [NumberField F] in
private theorem thetaPrincipalValueSelection_map (S W : Finset (Place F)) (hW : W ⊆ S) :
    (thetaPrincipalValueSelection F S W).map ⟨Subtype.val, Subtype.val_injective⟩ = W := by
  ext w
  constructor
  · intro hw
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hw
    exact (Finset.mem_filter.mp ha).2
  · intro hw
    exact Finset.mem_map.mpr ⟨⟨w,hW hw⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩

omit [NumberField F] in
private theorem thetaPrincipalValueSelection_insert (S W : Finset (Place F)) (hW : W ⊆ S)
    (v : Place F) :
    (thetaPrincipalValueSelection F S W).map (insertIndex F S v) =
      thetaPrincipalValueSelection F (insert v S) W := by
  ext w
  constructor
  · intro hw
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
  · intro hw
    have hw' := (Finset.mem_filter.mp hw).2
    exact Finset.mem_map.mpr ⟨⟨w.val,hW hw'⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw'⟩,Subtype.ext rfl⟩

theorem globalThetaPrincipalValues_stage (S W : Finset (Place F))
    (hW : W ⊆ S) (q : Q F S) :
    globalWeilPrincipalValuesQuotient F W (sLocalThetaToGlobal F S q) =
      sLocalThetaToGlobal F S (sLocalThetaPrincipalValues F S (thetaPrincipalValueSelection F S W) q) := by
  have h := DFunLike.congr_fun
    (globalWeilPrincipalValuesQuotient_stage F S (thetaPrincipalValueSelection F S W)
      _ (sLocalThetaPrincipalValues_mk F S (thetaPrincipalValueSelection F S W))) q
  simpa only [ContinuousLinearMap.comp_apply,thetaPrincipalValueSelection_map F S W hW] using h

private def hasPrincipalValueRetraction {S T : Finset (Place F)} (W : Finset (Place F))
    (hST : S ⊆ T) : Prop :=
  ∃ r : Q F T →L[ℂ] Q F S,
    LeftInverse r (sLocalThetaTransition F hST) ∧
    ∀ x, r (sLocalThetaPrincipalValues F T (thetaPrincipalValueSelection F T W) x) =
      sLocalThetaPrincipalValues F S (thetaPrincipalValueSelection F S W) (r x)

private theorem hasPrincipalValueRetraction_congr {S T A : Finset (Place F)} (W : Finset (Place F))
    (hST : S ⊆ T) (hSA : S ⊆ A) (he : T = A) :
    hasPrincipalValueRetraction F W hST → hasPrincipalValueRetraction F W hSA := by
  subst A
  exact id

private theorem sLocalThetaPrincipalValues_retract_union (S W : Finset (Place F))
    (hW : W ⊆ S) (B : Finset (Place F)) (hB : Disjoint B S) :
    hasPrincipalValueRetraction F W (show S ⊆ B ∪ S from Finset.subset_union_right) := by
  induction B using Finset.induction_on with
  | empty =>
    apply hasPrincipalValueRetraction_congr F W (show S ⊆ S from le_rfl) _
      (Finset.empty_union S).symm
    exact ⟨ContinuousLinearMap.id ℂ _, by rw [sLocalThetaTransition_refl]; exact fun _ ↦ rfl, fun _ ↦ rfl⟩
  | insert v B hv ih =>
    obtain ⟨hvS,hBS⟩ := Finset.disjoint_insert_left.mp hB
    have hvA : v ∉ B ∪ S := by simp [hv,hvS]
    obtain ⟨r,hr,hcomm⟩ := ih hBS
    let hA : S ⊆ B ∪ S := Finset.subset_union_right
    let hT : B ∪ S ⊆ insert v (B ∪ S) := Finset.subset_insert v _
    apply hasPrincipalValueRetraction_congr F W (hA.trans hT) _ (Finset.insert_union _ _ _).symm
    let u := sLocalThetaStageRetraction F (B ∪ S) v hvA
    refine ⟨r.comp u, ?_, fun x ↦ ?_⟩
    · rw [← sLocalThetaTransition_comp F hA hT]
      intro x
      change r (u (sLocalThetaTransition F hT (sLocalThetaTransition F hA x))) = x
      rw [sLocalThetaStageRetraction_leftInverse F (B ∪ S) v hvA, hr]
    · change r (u (sLocalThetaPrincipalValues F _ _ x)) = _
      rw [← thetaPrincipalValueSelection_insert F (B ∪ S) W
        (hW.trans Finset.subset_union_right) v, sLocalThetaStageRetraction_principalValues, hcomm]
      rfl

/-- For any finite enlargement, one can choose a continuous linear left
inverse of insertion that also intertwines the selected principal values. -/
theorem sLocalThetaPrincipalValues_exists_retraction {S T W : Finset (Place F)}
    (hST : S ⊆ T) (hW : W ⊆ S) :
    ∃ r : Q F T →L[ℂ] Q F S,
      LeftInverse r (sLocalThetaTransition F hST) ∧
      ∀ x, r (sLocalThetaPrincipalValues F T (thetaPrincipalValueSelection F T W) x) =
        sLocalThetaPrincipalValues F S (thetaPrincipalValueSelection F S W) (r x) := by
  exact hasPrincipalValueRetraction_congr F W Finset.subset_union_right hST
    (Finset.sdiff_union_of_subset hST)
    (sLocalThetaPrincipalValues_retract_union F S W hW (T \ S) Finset.sdiff_disjoint)

/-- The inverse image of the global principal-value range on every stage
containing the chosen places is exactly the range of the stage operator. -/
theorem globalThetaPrincipalValues_stage_mem_range {S W : Finset (Place F)}
    (hW : W ⊆ S) (x : Q F S) :
    sLocalThetaToGlobal F S x ∈ range (globalWeilPrincipalValuesQuotient F W) ↔
      x ∈ range (sLocalThetaPrincipalValues F S (thetaPrincipalValueSelection F S W)) := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨T,hST,_,y,hy⟩ := globalThetaQuotient_exhausted_by_different_stages F S q
    have hEq : sLocalThetaPrincipalValues F T (thetaPrincipalValueSelection F T W) y =
        sLocalThetaTransition F hST x := by
      apply sLocalThetaToGlobal_injective F T
      rw [← globalThetaPrincipalValues_stage F T W (hW.trans hST), hy, sLocalThetaToGlobal_transition]
      exact hq
    obtain ⟨r,hr,hcomm⟩ := sLocalThetaPrincipalValues_exists_retraction F hST hW
    refine ⟨r y, ?_⟩
    rw [← hcomm, hEq, hr]
  · rintro ⟨y,rfl⟩
    exact ⟨sLocalThetaToGlobal F S y, globalThetaPrincipalValues_stage F S W hW y⟩

/- The following three locally convex lemmas adapt the projection proof in
   mccorvie/riemann-masullo, Ch05 Sec3a, at 8ebf0e4d15ac7757fab6abfd9ef984adc80e9ddf
   (Apache-2.0). -/

/-- Through an inducing linear map into a polynormable space, every continuous seminorm of the
source is bounded by a continuous seminorm of the target. -/
private theorem seminorm_bound_of_inducing {X E : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    (f : X →ₗ[ℂ] E) (hf : IsInducing f) (s : Seminorm ℂ X) (hs : Continuous s) :
    ∃ t : Seminorm ℂ E, Continuous t ∧ ∀ z, s z ≤ t (f z) := by
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  obtain ⟨F, C, -, hle⟩ :=
    Seminorm.bound_of_continuous (hf.withSeminorms (PolynormableSpace.withSeminorms ℂ E)) s hs
  refine ⟨C • F.sup (fun p : {p : Seminorm ℂ E // Continuous p} ↦ p.1),
    (Seminorm.continuous_finsetSup fun t _ ↦ t.2).const_smul _, fun z ↦ (hle z).trans ?_⟩
  simp only [smul_apply, Seminorm.finset_sup_apply, SeminormFamily.comp_apply,
    Seminorm.comp_apply, le_refl]

/-- An endomorphism of a space exhausted by closed embedded stages is a closed embedding when it
restricts to a closed embedding on each stage and commutes with continuous projections onto the
stages that fix every earlier stage. -/
private theorem closedEmbedding_endomorphism_of_stageProjections {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [hE : PolynormableSpace ℂ E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    (ι : ∀ n, X n →L[ℂ] E) (hι : ∀ n, IsClosedEmbedding (ι n))
    (P : E →L[ℂ] E) (Pn : ∀ n, X n →L[ℂ] X n) (hPn : ∀ n, IsClosedEmbedding (Pn n))
    (hP : ∀ n z, P (ι n z) = ι n (Pn n z))
    (pr : ℕ → E →L[ℂ] E) (hmem : ∀ n x, pr n x ∈ range (ι n))
    (hfix : ∀ n m, n ≤ m → ∀ z, pr m (ι n z) = ι n z)
    (hprP : ∀ n x, pr n (P x) = P (pr n x))
    (hexh : ∀ x, ∃ n z, ι n z = x)
    (hfin : ∀ q : Seminorm ℂ E, (∀ n, Continuous (q ∘ ι n)) → Continuous q) :
    IsClosedEmbedding P := by
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  have hPι (n : ℕ) : IsClosedEmbedding (fun z ↦ P (ι n z)) := by
    have h : (fun z ↦ P (ι n z)) = ι n ∘ Pn n := funext (hP n)
    rw [h]
    exact (hι n).comp (hPn n)
  -- Injectivity is checked on a stage containing the vector.
  have hinj : Injective P := by
    refine (injective_iff_map_eq_zero P).mpr fun x hx ↦ ?_
    obtain ⟨n, z, rfl⟩ := hexh x
    have hz : z = 0 := (hPι n).injective (by simpa using hx)
    rw [hz, map_zero]
  -- A limit point of the range is fixed by the projection of its stage, which maps the
  -- range into the closed range of the stage.
  have hclosed : IsClosed (range P) := by
    refine isClosed_of_closure_subset fun y hy ↦ ?_
    obtain ⟨m, z, rfl⟩ := hexh y
    have hmaps : MapsTo (pr m) (range P) (range fun w ↦ P (ι m w)) := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := hmem m x
      exact ⟨w, by rw [hprP, ← hw]⟩
    have h := map_mem_closure (pr m).continuous hy hmaps
    rw [(hPι m).isClosed_range.closure_eq, hfix m m le_rfl] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨ι m w, hw⟩
  -- The successive differences of the projections split each vector into finitely many
  -- stage pieces, on each of which the stage estimate applies.
  let D : ℕ → E →L[ℂ] E := fun n ↦ Nat.casesOn n (pr 0) fun k ↦ pr (k + 1) - pr k
  have hDsum (m : ℕ) (x : E) : ∑ n ∈ Finset.range (m + 1), D n x = pr m x := by
    induction m with
    | zero => simp [D]
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      simp [D]
  have hDzero (m : ℕ) (z : X m) (n : ℕ) (hn : m < n) : D n (ι m z) = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [D, sub_apply]
    rw [hfix m (k + 1) (by omega), hfix m k (by omega), sub_self]
  have hDmem (n : ℕ) (x : E) : ∃ w, ι n w = D n x := by
    cases n with
    | zero => exact hmem 0 x
    | succ k =>
      obtain ⟨a, ha⟩ := hmem (k + 1) x
      obtain ⟨b, hb⟩ := hmem k x
      obtain ⟨c, hc⟩ := hmem (k + 1) (ι k b)
      rw [hfix k (k + 1) (Nat.le_succ k)] at hc
      exact ⟨a - c, by simp [D, ha, hb, hc]⟩
  have hDP (n : ℕ) (x : E) : D n (P x) = P (D n x) := by
    cases n with
    | zero => exact hprP 0 x
    | succ k => simp [D, hprP]
  have key (p : Seminorm ℂ E) (hp : Continuous p) :
      ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ x, p x ≤ q (P x) := by
    have hb (n : ℕ) : ∃ t : Seminorm ℂ E, Continuous t ∧ ∀ z, p (ι n z) ≤ t (P (ι n z)) := by
      obtain ⟨t, ht, hle⟩ := seminorm_bound_of_inducing
        ((P : E →ₗ[ℂ] E).comp (ι n : X n →ₗ[ℂ] E)) (hPι n).isInducing
        (p.comp (ι n : X n →ₗ[ℂ] E)) (hp.comp (ι n).continuous)
      exact ⟨t, ht, hle⟩
    choose t ht htle using hb
    have hsupp (x : E) : ∃ m, ∀ n, m < n → D n x = 0 := by
      obtain ⟨m, z, rfl⟩ := hexh x
      exact ⟨m, hDzero m z⟩
    have hsumm (x : E) : Summable fun n ↦ t n (D n x) := by
      obtain ⟨m, hm⟩ := hsupp x
      refine summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun n hn ↦ ?_
      rw [Finset.mem_range, not_lt] at hn
      rw [hm n (by omega), map_zero]
    let q : Seminorm ℂ E := Seminorm.of (fun x ↦ ∑' n, t n (D n x))
      (fun x y ↦ by
        have h := (hsumm x).add (hsumm y)
        calc ∑' n, t n (D n (x + y)) ≤ ∑' n, (t n (D n x) + t n (D n y)) :=
              (hsumm (x + y)).tsum_le_tsum (fun n ↦ by rw [map_add]; exact map_add_le_add _ _ _) h
          _ = _ := (hsumm x).tsum_add (hsumm y))
      (fun a x ↦ by
        simp only [map_smul, map_smul_eq_mul]
        exact tsum_mul_left)
    have hq : Continuous q := by
      refine hfin q fun k ↦ ?_
      have h : (fun z ↦ q (ι k z)) = fun z ↦ ∑ n ∈ Finset.range (k + 1), t n (D n (ι k z)) := by
        funext z
        refine tsum_eq_sum fun n hn ↦ ?_
        rw [Finset.mem_range, not_lt] at hn
        rw [hDzero k z n (by omega), map_zero]
      change Continuous (fun z ↦ q (ι k z))
      rw [h]
      exact continuous_finsetSum _ fun n _ ↦ (ht n).comp ((D n).continuous.comp (ι k).continuous)
    refine ⟨q, hq, fun x ↦ ?_⟩
    obtain ⟨m, z, rfl⟩ := hexh x
    calc p (ι m z) = p (∑ n ∈ Finset.range (m + 1), D n (ι m z)) := by
          rw [hDsum, hfix m m le_rfl]
      _ ≤ ∑ n ∈ Finset.range (m + 1), p (D n (ι m z)) :=
          Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ ≤ ∑ n ∈ Finset.range (m + 1), t n (D n (P (ι m z))) := by
          refine Finset.sum_le_sum fun n _ ↦ ?_
          obtain ⟨w, hw⟩ := hDmem n (ι m z)
          rw [hDP, ← hw]
          exact htle n w
      _ ≤ ∑' n, t n (D n (P (ι m z))) :=
          (hsumm _).sum_le_tsum _ fun n _ ↦ apply_nonneg _ _
  have hind : IsInducing P := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm ?_ (fun U hU ↦ ?_)
    · have h := P.continuous.tendsto 0
      rw [map_zero] at h
      exact h.le_comap
    · obtain ⟨⟨I, r⟩, hr, hpU⟩ :=
        (PolynormableSpace.withSeminorms ℂ E).hasBasis_zero_ball.mem_iff.mp hU
      let p := I.sup (fun s : {s : Seminorm ℂ E // Continuous s} ↦ s.val)
      have hp : Continuous p := Seminorm.continuous_finsetSup (fun s _ ↦ s.property)
      obtain ⟨q, hq, hpq⟩ := key p hp
      refine ⟨q.ball 0 r, Seminorm.ball_mem_nhds hq hr, fun x hx ↦ hpU ?_⟩
      rw [mem_preimage, Seminorm.mem_ball_zero] at hx
      exact (Seminorm.mem_ball_zero p).mpr ((hpq x).trans_lt hx)
  exact ⟨⟨hind, hinj⟩, hclosed⟩

/-- Continuous linear left inverses of the steps of a chain of stages, commuting with operators
compatible with the stage maps, assemble into continuous projections onto the stages that fix
the earlier stages and commute with the operator on the limit. -/
private theorem commutingProjections_of_stageRetractions {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    [hX : ∀ n, PolynormableSpace ℂ (X n)]
    (ι : ∀ n, X n →L[ℂ] E) (hι : ∀ n, Injective (ι n))
    (j : ∀ n, X n →L[ℂ] X (n + 1)) (hj : ∀ n z, ι (n + 1) (j n z) = ι n z)
    (r : ∀ n, X (n + 1) →L[ℂ] X n) (hr : ∀ n z, r n (j n z) = z)
    (P : E →L[ℂ] E) (Pn : ∀ n, X n →L[ℂ] X n) (hP : ∀ n z, P (ι n z) = ι n (Pn n z))
    (hrP : ∀ n z, r n (Pn (n + 1) z) = Pn n (r n z))
    (hexh : ∀ x, ∃ n z, ι n z = x)
    (hfin : ∀ (N : ℕ) (q : Seminorm ℂ E), (∀ d, Continuous (q ∘ ι (N + d))) → Continuous q) :
    ∃ pr : ℕ → E →L[ℂ] E, (∀ n x, pr n x ∈ range (ι n)) ∧
      (∀ n m, n ≤ m → ∀ z, pr m (ι n z) = ι n z) ∧ (∀ n x, pr n (P x) = P (pr n x)) := by
  have hnest (a b : ℕ) (hab : a ≤ b) (z : X a) : ∃ w : X b, ι b w = ι a z := by
    induction b, hab using Nat.le_induction with
    | base => exact ⟨z, rfl⟩
    | succ b _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨j b w, (hj b w).trans hw⟩
  -- The composite of the left inverses from stage `n + d` down to stage `n`.
  let R (n : ℕ) : ∀ d, X (n + d) →L[ℂ] X n := fun d ↦
    Nat.rec (motive := fun d ↦ X (n + d) →L[ℂ] X n) (ContinuousLinearMap.id ℂ (X n))
      (fun d R ↦ R.comp (r (n + d))) d
  have hRsucc (n d : ℕ) (z : X (n + (d + 1))) : R n (d + 1) z = R n d (r (n + d) z) := rfl
  have hRP (n d : ℕ) (z : X (n + d)) : R n d (Pn (n + d) z) = Pn n (R n d z) := by
    induction d with
    | zero => rfl
    | succ d ih =>
      have h := hrP (n + d) z
      exact (congrArg (R n d) h).trans (ih (r (n + d) z))
  -- The composite only depends on the vector of the limit that a stage vector represents.
  have hcons (n d : ℕ) (z : X (n + d)) (d' : ℕ) (hd : d ≤ d') :
      ∀ z' : X (n + d'), ι (n + d') z' = ι (n + d) z → R n d' z' = R n d z := by
    induction d', hd using Nat.le_induction with
    | base => exact fun z' h ↦ congrArg (R n d) (hι _ h)
    | succ d' hdd' ih =>
      intro z' h
      obtain ⟨w, hw⟩ := hnest (n + d) (n + d') (by omega) z
      have hz' : z' = j (n + d') w := hι (n + d' + 1) (h.trans (hw.symm.trans (hj _ w).symm))
      rw [hz']
      exact (congrArg (R n d') (hr (n + d') w)).trans (ih w hw)
  have hcons' (n d d' : ℕ) (z : X (n + d)) (z' : X (n + d'))
      (h : ι (n + d') z' = ι (n + d) z) : R n d' z' = R n d z := by
    rcases le_total d d' with hd | hd
    · exact hcons n d z d' hd z' h
    · exact (hcons n d' z' d hd z h.symm).symm
  have hrep (n : ℕ) (x : E) : ∃ d, ∃ z : X (n + d), ι (n + d) z = x := by
    obtain ⟨k, z, rfl⟩ := hexh x
    obtain ⟨w, hw⟩ := hnest k (n + k) (by omega) z
    exact ⟨k, w, hw⟩
  have hcommon (n : ℕ) (x y : E) :
      ∃ d, ∃ a b : X (n + d), ι (n + d) a = x ∧ ι (n + d) b = y := by
    obtain ⟨d₁, z₁, rfl⟩ := hrep n x
    obtain ⟨d₂, z₂, rfl⟩ := hrep n y
    obtain ⟨a, ha⟩ := hnest (n + d₁) (n + max d₁ d₂) (by omega) z₁
    obtain ⟨b, hb⟩ := hnest (n + d₂) (n + max d₁ d₂) (by omega) z₂
    exact ⟨max d₁ d₂, a, b, ha, hb⟩
  choose dx zx hzx using hrep
  have hQ (n d : ℕ) (z : X (n + d)) : R n (dx n (ι (n + d) z)) (zx n (ι (n + d) z)) = R n d z :=
    hcons' n d _ z _ (hzx n _)
  let Q (n : ℕ) : E →ₗ[ℂ] X n :=
    { toFun := fun x ↦ R n (dx n x) (zx n x)
      map_add' := fun x y ↦ by
        obtain ⟨d, a, b, rfl, rfl⟩ := hcommon n x y
        have h := hQ n d (a + b)
        rw [map_add] at h
        rw [h, hQ, hQ, map_add]
      map_smul' := fun c x ↦ by
        obtain ⟨d, z, rfl⟩ : ∃ d, ∃ z : X (n + d), ι (n + d) z = x := ⟨dx n x, zx n x, hzx n x⟩
        have h := hQ n d (c • z)
        rw [map_smul] at h
        rw [h, hQ, map_smul]
        rfl }
  have hQapp (n d : ℕ) (z : X (n + d)) : Q n (ι (n + d) z) = R n d z := hQ n d z
  have hQc (n : ℕ) : Continuous (Q n) := by
    refine (PolynormableSpace.withSeminorms ℂ (X n)).continuous_of_continuous_comp (Q n)
      fun s ↦ hfin n ((s.1).comp (Q n)) fun d ↦ ?_
    have h : ⇑((s.1).comp (Q n)) ∘ ι (n + d) = s.1 ∘ R n d :=
      funext fun z ↦ congrArg s.1 (hQapp n d z)
    rw [h]
    exact s.2.comp (R n d).continuous
  refine ⟨fun n ↦ (ι n).comp ⟨Q n, hQc n⟩, fun n x ↦ ⟨_, rfl⟩, fun n m hnm z ↦ ?_,
    fun n x ↦ ?_⟩
  · obtain ⟨w, hw⟩ := hnest n m hnm z
    change ι m (Q m (ι n z)) = ι n z
    rw [← hw]
    exact congrArg (ι m) (hQapp m 0 w)
  · obtain ⟨d, z, rfl⟩ : ∃ d, ∃ z : X (n + d), ι (n + d) z = x := ⟨dx n x, zx n x, hzx n x⟩
    change ι n (Q n (P (ι (n + d) z))) = P (ι n (Q n (ι (n + d) z)))
    rw [hP (n + d), hP n, hQapp, hQapp, hRP]


/-- The ordinary global principal-value map is a closed topological embedding
exactly when all stages containing the selected places have that property. -/
theorem globalThetaPrincipalValues_closedEmbedding_iff (W : Finset (Place F)) :
    IsClosedEmbedding (globalWeilPrincipalValuesQuotient F W) ↔
      ∀ S : Finset (Place F), W ⊆ S →
        IsClosedEmbedding (sLocalThetaPrincipalValues F S (thetaPrincipalValueSelection F S W)) := by
  constructor
  · intro h S hW
    let j := sLocalThetaToGlobal F S
    let P := sLocalThetaPrincipalValues F S (thetaPrincipalValueSelection F S W)
    have hj := sLocalThetaToGlobal_isClosedEmbedding F S
    have he : j ∘ P = globalWeilPrincipalValuesQuotient F W ∘ j :=
      funext fun q ↦ (globalThetaPrincipalValues_stage F S W hW q).symm
    have hc : IsClosedEmbedding (j ∘ P) := he.symm ▸ (h.comp hj)
    refine ⟨⟨hj.isEmbedding.isInducing.of_comp_iff.mp hc.isEmbedding.isInducing,
      sLocalThetaPrincipalValues_injective F S _⟩, ?_⟩
    have hr : range P = j ⁻¹' range (j ∘ P) := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩
        exact ⟨y,rfl⟩
      · rintro ⟨y,hy⟩
        exact ⟨y,hj.injective hy⟩
    rw [hr]
    exact hc.isClosed_range.preimage j.continuous
  · intro h
    obtain ⟨S,hS,h0,hcof⟩ := exists_globalThetaCofinalTower F W
    letI : PolynormableSpace ℂ (G F) :=
      polynormableSpace_complex_quotient (globalThetaOperator F).ker
    letI (n : ℕ) : PolynormableSpace ℂ (Q F (S n)) :=
      polynormableSpace_complex_quotient (sLocalThetaOperator F (S n)).ker
    let D := globalThetaQuotient_tower F S hS hcof
    let P := globalWeilPrincipalValuesQuotient F W
    let Pn (n : ℕ) := sLocalThetaPrincipalValues F (S n) (thetaPrincipalValueSelection F (S n) W)
    have hW (n : ℕ) : W ⊆ S n := h0.trans (hS (Nat.zero_le n))
    have hJ (n : ℕ) : IsClosedEmbedding (D.incl n) :=
      sLocalThetaToGlobal_isClosedEmbedding F (S n)
    have hP (n : ℕ) (q : Q F (S n)) : P (D.incl n q) = D.incl n (Pn n q) :=
      globalThetaPrincipalValues_stage F (S n) W (hW n) q
    have hr (n : ℕ) := sLocalThetaPrincipalValues_exists_retraction F (hS (Nat.le_succ n)) (hW n)
    choose R hleft hcomm using hr
    have hex (q : G F) : ∃ n x, D.incl n x = q := D.exhaust q
    have hfin {N : ℕ} (p : Seminorm ℂ (G F)) (hp : ∀ d, Continuous (p ∘ D.incl (N+d))) :
        Continuous p := by
      apply globalTheta_cofinal_seminorm_final F (S := fun d ↦ S (N+d))
        (fun A ↦ by
          obtain ⟨k,hk⟩ := hcof A
          exact ⟨k,hk.trans (hS (Nat.le_add_left k N))⟩) p
      exact hp
    obtain ⟨pr,hmem,hfix,hprP⟩ := commutingProjections_of_stageRetractions D.incl D.injective_incl
      (fun n ↦ D.transition (Nat.le_succ n)) (fun n ↦ D.incl_transition (Nat.le_succ n))
      R hleft P Pn hP hcomm hex (fun N ↦ hfin (N := N))
    exact closedEmbedding_endomorphism_of_stageProjections D.incl hJ P Pn
      (fun n ↦ h (S n) (hW n)) hP pr hmem hfix hprP hex
      (fun p hp ↦ hfin (N := 0) p (fun d ↦ by
        change Continuous (p ∘ sLocalThetaToGlobal F (S (0+d)))
        rw [Nat.zero_add]
        exact hp d))

/-- Closed embeddings for single-place operators imply the same conclusion
for every finite selection in the same stage. -/
theorem sLocalThetaPrincipalValues_closedEmbedding_of_singletons (S : Finset (Place F))
    (h : ∀ w : S, IsClosedEmbedding (sLocalThetaPrincipalValues F S {w})) (W : Finset S) :
    IsClosedEmbedding (sLocalThetaPrincipalValues F S W) := by
  induction W using Finset.induction_on with
  | empty =>
    have he : (sLocalThetaPrincipalValues F S ∅ : Q F S → Q F S) = id := by
      funext q
      obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [sLocalThetaPrincipalValues_mk]
      have h0 : sLocalWeilPrincipalValues F S ∅ = 1 := Finset.noncommProd_empty _ _
      rw [h0]
      rfl
    rw [he]
    exact IsClosedEmbedding.id
  | insert w W hw ih =>
    have he : (sLocalThetaPrincipalValues F S (insert w W) : Q F S → Q F S) =
        sLocalThetaPrincipalValues F S {w} ∘ sLocalThetaPrincipalValues F S W :=
      funext (sLocalThetaPrincipalValues_insert F S w W hw)
    rw [he]
    exact (h w).comp ih

private theorem frechet_closedEmbedding_of_closedRange {X : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (hX : IsFrechetTVS X) (P : X →L[ℂ] X) (hi : Injective P) (hc : IsClosed (range P)) :
    IsClosedEmbedding P := by
  let Y := P.toLinearMap.range
  have hY := isFrechetTVS_closedSubmodule hX Y hc
  obtain ⟨haX,hpX,hmX,hcX⟩ := hX
  obtain ⟨haY,hpY,hmY,hcY⟩ := hY
  letI : ContinuousSMul ℂ X := (PolynormableSpace.withSeminorms ℂ X).continuousSMul
  letI : ContinuousSMul ℂ Y := (PolynormableSpace.withSeminorms ℂ Y).continuousSMul
  letI : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  letI : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace Y := hcY
  letI : (uniformity Y).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
  let A : X →L[ℂ] Y := P.codRestrict Y (fun x ↦ ⟨x,rfl⟩)
  have hs : Surjective A := fun y ↦ by
    obtain ⟨x,hx⟩ := y.property
    exact ⟨x,Subtype.ext hx⟩
  have hI : Injective A := fun x y h ↦ hi (congrArg Subtype.val h)
  have hO := isOpenMap_of_surjective_complete_baire A hs
  have he := IsOpenEmbedding.of_continuous_injective_isOpenMap A.continuous hI hO
  exact ⟨IsEmbedding.subtypeVal.comp he.isEmbedding,hc⟩

/-- Closedness on the finite angular fixed spaces suffices for the
intrinsic local closed embedding. On each fixed space, the inverse is
continuous by the Fréchet open mapping theorem. -/
theorem sLocalThetaPrincipalValues_closedEmbedding_iff_angular (S : Finset (Place F)) (W : Finset S) :
    IsClosedEmbedding (sLocalThetaPrincipalValues F S W) ↔
      ∀ (H : ∀ w : S, Subgroup (w.val.adicCompletion F)ˣ),
        (∀ w, IsOpen (H w : Set (w.val.adicCompletion F)ˣ)) →
        (∀ w (u : H w), ‖u.val.val‖ = 1) →
        IsClosed ((sLocalThetaInvariantTestSpan F S H).subtypeL ⁻¹'
          range (sLocalThetaPrincipalValues F S W)) := by
  constructor
  · intro h H _ _
    exact h.isClosed_range.preimage (sLocalThetaInvariantTestSpan F S H).subtypeL.continuous
  · intro h
    let P := sLocalThetaPrincipalValues F S W
    obtain ⟨H,hH,hn,hanti,hex,hfin⟩ := sLocalTheta_exists_angularStages F S
    letI : T2Space (Q F S) := sLocalThetaQuotient_t2Space F S
    letI : PolynormableSpace ℂ (Q F S) := polynormableSpace_complex_quotient (sLocalThetaOperator F S).ker
    let X (n : ℕ) := sLocalThetaInvariantTestSpan F S (H n)
    let j (n : ℕ) := (X n).subtypeL
    let R (n : ℕ) := sLocalThetaAngularRetraction F S (H n) (hH n) (hn n)
    let pr (n : ℕ) := (j n).comp (R n)
    have hleft (n : ℕ) : LeftInverse (R n) (j n) :=
      sLocalThetaAngularRetraction_leftInverse F S (H n) (hH n) (hn n)
    have hpr (n : ℕ) (x : Q F S) : pr n (P x) = P (pr n x) := by
      apply sLocalThetaAngularAverage_commutes F S (H n) (hH n) (hn n) P _ x
      intro a q
      exact DFunLike.congr_fun (sLocalWeilPrincipalValuesQuotient_translate F S W P
        (sLocalThetaPrincipalValues_mk F S W) (QuotientGroup.mk (angularLocalIdele F S (H n) a))).eq q
    have hpres (n : ℕ) (x : X n) : P (j n x) ∈ X n := by
      have he : pr n (P (j n x)) = P (j n x) := by
        rw [hpr]
        change P (j n (R n (j n x))) = _
        rw [hleft n]
      exact he ▸ (R n (P (j n x))).property
    let A (n : ℕ) := (P.comp (j n)).codRestrict (X n) (hpres n)
    have hFr (n : ℕ) : IsFrechetTVS (X n) :=
      sLocalThetaInvariantTestSpan_isFrechet F S (H n) (hH n) (hn n)
    have hStage (n : ℕ) : IsClosedEmbedding (A n) := by
      apply frechet_closedEmbedding_of_closedRange (hFr n) _
        (fun x y he ↦ Subtype.ext (sLocalThetaPrincipalValues_injective F S W (congrArg Subtype.val he)))
      have he : range (A n) = j n ⁻¹' range P := by
        ext x
        constructor
        · rintro ⟨y,rfl⟩
          exact ⟨j n y,rfl⟩
        · rintro ⟨y,hy⟩
          refine ⟨R n y,Subtype.ext ?_⟩
          change P (pr n y) = j n x
          rw [← hpr, hy]
          exact congrArg (j n) (hleft n x)
      rw [he]
      exact h (H n) (hH n) (hn n)
    apply closedEmbedding_endomorphism_of_stageProjections j
      (fun n ↦ (hFr n).isClosedEmbedding (j n) IsEmbedding.subtypeVal)
      P A hStage (fun _ _ ↦ rfl) pr (fun n x ↦ ⟨R n x,rfl⟩) _ hpr _ hfin
    · intro n m hnm z
      have hz := sLocalThetaInvariantTestSpan_antitone F S (hanti hnm) z.property
      let y : X m := ⟨z.val,hz⟩
      exact congrArg (j m) (hleft m y)
    · intro x
      obtain ⟨n,hx⟩ := hex x
      exact ⟨n,⟨x,hx⟩,rfl⟩

/-- The image of one integral unit in the ordinary S-local class group. -/
def thetaPrincipalUnitClass (S : Finset (Place F)) (w : S) (u : U F w.val) : SIdeleQuotient F S :=
  QuotientGroup.mk (project F S (singleFiniteIdele F w.val u.val))

private theorem thetaPrincipalUnitClass_mul (S : Finset (Place F)) (w : S)
    (u v : U F w.val) :
    thetaPrincipalUnitClass F S w (u * v) =
      thetaPrincipalUnitClass F S w u * thetaPrincipalUnitClass F S w v := by
  let q := QuotientGroup.mk' (sUnitImage F S)
  change q (project F S (singleFiniteIdele F w.val (u.val * v.val))) = _
  rw [singleFiniteIdele_mul,map_mul,map_mul]
  rfl

/-- The uniformizer translation is restricted to the chosen coordinate. -/
def thetaPrincipalUniformizerClass (S : Finset (Place F)) (w : S) : SIdeleQuotient F S :=
  QuotientGroup.mk (project F S (singleFiniteIdele F w.val (chosenFiniteUniformizer F w.val)))

private theorem principalTranslateArgument_class (S : Finset (Place F)) (w : S) (u : U F w.val) :
    (QuotientGroup.mk (project F S (principalTranslateArgument F w.val u)) : SIdeleQuotient F S) =
      thetaPrincipalUniformizerClass F S w * thetaPrincipalUnitClass F S w u := by
  let q := QuotientGroup.mk' (sUnitImage F S)
  change q (project F S (principalTranslateArgument F w.val u)) = _
  rw [principalTranslateArgument_mul,map_mul,map_mul]
  rfl

/-- Haar projection onto the classes invariant under the integral units
in the selected coordinate. The formula defining it uses the already
descended principal value and inverse uniformizer translation. -/
def sLocalThetaPrincipalUnitAverage (S : Finset (Place F)) (w : S) : Q F S →L[ℂ] Q F S :=
  (sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w)⁻¹).comp
    (ContinuousLinearMap.id ℂ (Q F S) - sLocalThetaPrincipalValues F S {w})

theorem sLocalThetaPrincipalUnitAverage_pairing (S : Finset (Place F)) (w : S)
    (q : Q F S) (ℓ : Q F S →ₗ[ℂ] ℂ) :
    ℓ (sLocalThetaPrincipalUnitAverage F S w q) =
      ∫ u : U F w.val, ℓ (sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u) q)
        ∂principalUnitHaar F w.val := by
  let t := thetaPrincipalUniformizerClass F S w
  let B := ℓ.comp (sLocalThetaTranslate F S t⁻¹).toLinearMap
  change B (q - sLocalThetaPrincipalValues F S {w} q) = _
  rw [map_sub, sLocalThetaPrincipalValue_pairing F S w q B, sub_sub_cancel]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  change ℓ (sLocalThetaTranslate F S t⁻¹
    (sLocalThetaTranslate F S (QuotientGroup.mk (project F S (principalTranslateArgument F w.val u))) q)) = _
  rw [← sLocalThetaTranslate_mul,principalTranslateArgument_class]
  change ℓ (sLocalThetaTranslate F S (t⁻¹ * (t * thetaPrincipalUnitClass F S w u)) q) = _
  rw [inv_mul_cancel_left]

/-- The ordinary theta classes fixed by the units of one finite coordinate. -/
def sLocalPrincipalUnitFixed (S : Finset (Place F)) (w : S) : Set (Q F S) := {q |
  ∀ u : U F w.val, sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u) q = q}

theorem sLocalThetaPrincipalUnitAverage_fixed (S : Finset (Place F)) (w : S)
    (q : Q F S) (u : U F w.val) :
    sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u) (sLocalThetaPrincipalUnitAverage F S w q) =
      sLocalThetaPrincipalUnitAverage F S w q := by
  letI : MeasurableSpace (U F w.val) := borel _
  letI : BorelSpace (U F w.val) := ⟨rfl⟩
  let A := sLocalThetaPrincipalUnitAverage F S w
  let T := sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u)
  change T (A q) = A q
  by_contra hn
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hn)
  apply hℓ
  rw [map_sub]
  apply sub_eq_zero.mpr
  change (ℓ.comp T.toLinearMap) (A q) = ℓ (A q)
  rw [sLocalThetaPrincipalUnitAverage_pairing F S w q (ℓ.comp T.toLinearMap),
    sLocalThetaPrincipalUnitAverage_pairing F S w q ℓ]
  have he (a : U F w.val) : (ℓ.comp T.toLinearMap)
      (sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w a) q) =
      ℓ (sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w (u*a)) q) := by
    change ℓ (sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u)
      (sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w a) q)) = _
    rw [← sLocalThetaTranslate_mul, thetaPrincipalUnitClass_mul]
  simp_rw [he]
  exact integral_mul_left_eq_self (fun a : U F w.val ↦
    ℓ (sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w a) q)) u

theorem sLocalThetaPrincipalUnitAverage_eq_of_fixed (S : Finset (Place F)) (w : S)
    (q : Q F S) (hq : ∀ u : U F w.val, sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u) q = q) :
    sLocalThetaPrincipalUnitAverage F S w q = q := by
  by_contra hn
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hn)
  apply hℓ
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [sLocalThetaPrincipalUnitAverage_pairing]
  simp only [hq,integral_const,measureReal_def,principalUnitHaar_univ,ENNReal.toReal_one,one_smul]

/-- The quotient principal value splits into the identity on the kernel
of unit averaging and a uniformizer difference on the fixed subspace. -/
theorem sLocalThetaPrincipalValue_eq_sub_average (S : Finset (Place F)) (w : S) (q : Q F S) :
    sLocalThetaPrincipalValues F S {w} q =
      q - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w)
        (sLocalThetaPrincipalUnitAverage F S w q) := by
  change _ = q - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w)
    (sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w)⁻¹
      (q - sLocalThetaPrincipalValues F S {w} q))
  rw [← sLocalThetaTranslate_mul,mul_inv_cancel,sLocalThetaTranslate_one,sub_sub_cancel]

private theorem principalUnitAverage_commutes (S : Finset (Place F)) (w : S)
    (P : Q F S →L[ℂ] Q F S)
    (hP : ∀ u : U F w.val, ∀ q, P (sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u) q) =
      sLocalThetaTranslate F S (thetaPrincipalUnitClass F S w u) (P q)) (q : Q F S) :
    sLocalThetaPrincipalUnitAverage F S w (P q) = P (sLocalThetaPrincipalUnitAverage F S w q) := by
  by_contra hn
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_ne_zero ℂ (sub_ne_zero.mpr hn)
  apply hℓ
  rw [map_sub]
  apply sub_eq_zero.mpr
  have h := sLocalThetaPrincipalUnitAverage_pairing F S w q (ℓ.comp P.toLinearMap)
  rw [sLocalThetaPrincipalUnitAverage_pairing]
  simpa only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,hP] using h.symm

/-- Single-coordinate unit averaging commutes with every class translation. -/
theorem sLocalThetaPrincipalUnitAverage_translate (S : Finset (Place F)) (w : S)
    (c : SIdeleQuotient F S) (q : Q F S) :
    sLocalThetaPrincipalUnitAverage F S w (sLocalThetaTranslate F S c q) =
      sLocalThetaTranslate F S c (sLocalThetaPrincipalUnitAverage F S w q) :=
  principalUnitAverage_commutes F S w (sLocalThetaTranslate F S c) (fun u x ↦ by
    rw [← sLocalThetaTranslate_mul, ← sLocalThetaTranslate_mul]
    exact congrArg (fun d : SIdeleQuotient F S ↦ sLocalThetaTranslate F S d x)
      (mul_comm c (thetaPrincipalUnitClass F S w u))) q

/-- Membership in the single-place range is exactly membership of the
unit average in the uniformizer-difference range on the fixed subspace. -/
theorem sLocalThetaPrincipalValue_mem_range_iff_unitDifference (S : Finset (Place F)) (w : S)
    (q : Q F S) :
    q ∈ range (sLocalThetaPrincipalValues F S {w}) ↔
      sLocalThetaPrincipalUnitAverage F S w q ∈ range (fun y : sLocalPrincipalUnitFixed F S w ↦
        y.val - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) y.val) := by
  let A := sLocalThetaPrincipalUnitAverage F S w
  let P := sLocalThetaPrincipalValues F S {w}
  let T := sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w)
  have hA (x : Q F S) : A (A x) = A x :=
    sLocalThetaPrincipalUnitAverage_eq_of_fixed F S w (A x)
      (fun u ↦ sLocalThetaPrincipalUnitAverage_fixed F S w x u)
  have hP (x : Q F S) : P x = x - T (A x) := sLocalThetaPrincipalValue_eq_sub_average F S w x
  have hc (x : Q F S) : A (P x) = P (A x) := principalUnitAverage_commutes F S w P
    (fun u z ↦ DFunLike.congr_fun (sLocalWeilPrincipalValuesQuotient_translate F S {w} P
      (sLocalThetaPrincipalValues_mk F S {w}) (thetaPrincipalUnitClass F S w u)).eq z) x
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨⟨A x, fun u ↦ sLocalThetaPrincipalUnitAverage_fixed F S w x u⟩, ?_⟩
    change A x - T (A x) = A (P x)
    rw [hc,hP (A x),hA]
  · rintro ⟨y,hy⟩
    have hyA : A y.val = y.val := sLocalThetaPrincipalUnitAverage_eq_of_fixed F S w y.val y.property
    change y.val - T y.val = A q at hy
    refine ⟨q - A q + y.val, ?_⟩
    change P (q - A q + y.val) = q
    rw [hP,map_add,map_sub,hA,sub_self,zero_add,hyA]
    calc
      q - A q + y.val - T y.val = q - A q + (y.val - T y.val) := by abel
      _ = q := by rw [hy,sub_add_cancel]

/-- The one-place principal-value range is closed exactly when the
uniformizer-difference range on the unit-fixed subspace is closed. -/
theorem sLocalThetaPrincipalValue_isClosed_range_iff_unitDifference
    (S : Finset (Place F)) (w : S) :
    IsClosed (range (sLocalThetaPrincipalValues F S {w})) ↔
      IsClosed (range (fun y : sLocalPrincipalUnitFixed F S w ↦
        y.val - sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w) y.val)) := by
  letI : T2Space (Q F S) := sLocalThetaQuotient_t2Space F S
  let A := sLocalThetaPrincipalUnitAverage F S w
  let P := sLocalThetaPrincipalValues F S {w}
  let T := sLocalThetaTranslate F S (thetaPrincipalUniformizerClass F S w)
  let D (y : sLocalPrincipalUnitFixed F S w) := y.val - T y.val
  change IsClosed (range P) ↔ IsClosed (range D)
  have ha : ∀ x : sLocalPrincipalUnitFixed F S w, A x.val = x.val := fun x ↦
    sLocalThetaPrincipalUnitAverage_eq_of_fixed F S w x.val x.property
  have hc (x : Q F S) : A (P x) = P (A x) := principalUnitAverage_commutes F S w P
    (fun u z ↦ DFunLike.congr_fun (sLocalWeilPrincipalValuesQuotient_translate F S {w} P
      (sLocalThetaPrincipalValues_mk F S {w}) (thetaPrincipalUnitClass F S w u)).eq z) x
  have hpre : range P = A ⁻¹' range D :=
    Set.ext (sLocalThetaPrincipalValue_mem_range_iff_unitDifference F S w)
  have hD : range D = range P ∩ {x | A x = x} := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      have he : P y.val = D y := by
        change P y.val = y.val - T y.val
        rw [sLocalThetaPrincipalValue_eq_sub_average, show A y.val = y.val from ha y]
      rw [← he]
      exact ⟨⟨y.val,rfl⟩, (hc y.val).trans (congrArg P (ha y))⟩
    · rintro ⟨hx,hax⟩
      have h : A x ∈ range D := (Set.ext_iff.mp hpre x).mp hx
      rwa [hax] at h
  constructor
  · intro h
    rw [hD]
    exact h.inter (isClosed_eq A.continuous continuous_id)
  · intro h
    rw [hpre]
    exact h.preimage A.continuous

/-- A strict modulus contraction has no nonzero fixed vector on the
ordinary theta quotient. Evaluate along its expanding inverse orbit. -/
theorem sLocalThetaTranslate_eq_zero_of_fixed_of_norm_lt_one
    (S : Finset (Place F)) (a : (SAdeles F S)ˣ) (ha : sLocalIdeleNorm F S a < 1)
    (q : Q F S) (hq : sLocalThetaTranslate F S (QuotientGroup.mk a) q = q) : q = 0 := by
  obtain ⟨f,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  let N := (sLocalThetaOperator F S).ker
  let φ := sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val)
  have hfix (g : (SAdeles F S)ˣ) : φ (a⁻¹*g) = φ g := by
    have h := congrArg (sLocalThetaQuotientEval F S g) hq
    change sLocalThetaQuotientEval F S g (sLocalThetaTranslateIdeles F S a (Submodule.Quotient.mk f)) =
      sLocalThetaQuotientEval F S g (Submodule.Quotient.mk f) at h
    rw [sLocalThetaTranslateIdeles_mk] at h
    let π := QuotientGroup.mk' (sUnitImage F S)
    change sLocalThetaOperator F S (sLocalBruhatLeftTranslate F S a f) (π g) =
      sLocalThetaOperator F S f (π g) at h
    rw [sLocalThetaOperator_leftTranslate] at h
    change sLocalThetaOperator F S f ((π a)⁻¹ * π g) = _ at h
    rw [← map_inv, ← map_mul] at h
    exact h
  apply (Submodule.Quotient.mk_eq_zero N).mpr
  apply LinearMap.mem_ker.mpr
  funext c
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective c
  change φ g = 0
  have hpow (n : ℕ) : φ (a⁻¹ ^ n * g) = φ g := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_assoc,hfix,ih]
  let r := sLocalIdeleNorm F S
  have hpos (b : (SAdeles F S)ˣ) : 0 < r b :=
    ideleNorm_pos F (sLocalEmbed F S b)
  have ht : Tendsto (fun n : ℕ ↦ r (a⁻¹ ^ n * g)) atTop atTop := by
    have hr : 1 < (r a)⁻¹ := (one_lt_inv₀ (hpos a)).mpr ha
    simpa only [map_mul,map_pow,map_inv] using
      (tendsto_pow_atTop_atTop_of_one_lt hr).atTop_mul_const (hpos g)
  obtain ⟨p,_,hp⟩ := sLocalTheta_largeNorm_seminorm F S 1
  have hz : Tendsto (fun n : ℕ ↦ p f * (r (a⁻¹ ^ n * g))⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (tendsto_inv_atTop_zero.comp ht).const_mul (p f)
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply ge_of_tendsto hz
  filter_upwards [ht.eventually (eventually_ge_atTop 1)] with n hn
  have hb := hp f (a⁻¹ ^ n * g) hn
  change r (a⁻¹ ^ n * g)^1 * ‖φ (a⁻¹ ^ n * g)‖ ≤ p f at hb
  rw [pow_one,hpow,mul_comm] at hb
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (hpos _)).mpr hb
end
end Masullo
