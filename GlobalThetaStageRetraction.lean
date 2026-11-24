import SLocalThetaStageRetraction
import SLocalThetaTopology
import NuclearPermanence
import StrictInductiveBounds

open Bornology Function IsDedekindDomain NumberField Set Topology

open scoped Classical ENNReal NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev G := GlobalThetaQuotient F
private abbrev E (S : Finset (Place F)) := SLocalThetaQuotient F S

/-- A countable cofinal tower of theta stages containing a prescribed initial set. -/
theorem exists_globalThetaCofinalTower (A : Finset (Place F)) :
    ∃ S : ℕ → Finset (Place F), Monotone S ∧ A ⊆ S 0 ∧ ∀ T, ∃ n, T ⊆ S n := by
  letI := finitePlaces_countable F
  obtain ⟨e, he⟩ := exists_injective_nat (Place F)
  let finite (n : ℕ) : {v : Place F | e v < n}.Finite :=
    (finite_lt_nat n).preimage he.injOn
  let S (n : ℕ) := A ∪ (finite n).toFinset
  refine ⟨S, ?_, Finset.subset_union_left, ?_⟩
  · intro m n h
    apply Finset.union_subset_union_right
    intro v hv
    exact (finite n).mem_toFinset.mpr (((finite m).mem_toFinset.mp hv).trans_le h)
  · intro T
    refine ⟨T.sup e + 1, fun v hv ↦ Finset.mem_union_right A ((finite _).mem_toFinset.mpr ?_)⟩
    exact (Finset.le_sup hv).trans_lt (Nat.lt_succ_self _)

private theorem sLocalThetaTransition_apply_comp {A B C : Finset (Place F)}
    (hAB : A ⊆ B) (hBC : B ⊆ C) (q : E F A) :
    sLocalThetaTransition F hBC (sLocalThetaTransition F hAB q) =
      sLocalThetaTransition F (hAB.trans hBC) q :=
  DFunLike.congr_fun (sLocalThetaTransition_comp F hAB hBC) q

/-- The finite-stage retractions can be chosen compatibly along a countable
cofinal tower. Their extension is a continuous linear left inverse of insertion. -/
theorem sLocalThetaToGlobal_exists_retraction (A : Finset (Place F)) :
    ∃ R : G F →L[ℂ] E F A, LeftInverse R (sLocalThetaToGlobal F A) := by
  obtain ⟨S, hS, hA, hcof⟩ := exists_globalThetaCofinalTower F A
  let i {m n : ℕ} (h : m ≤ n) := sLocalThetaTransition F (hS h)
  have hex (n : ℕ) := sLocalThetaTransition_exists_retraction F (hS (Nat.le_succ n))
  let Q (n : ℕ) : E F (S (n + 1)) →L[ℂ] E F (S n) := (hex n).choose
  have hQ (n : ℕ) : LeftInverse (Q n) (i (Nat.le_succ n)) := (hex n).choose_spec
  obtain ⟨P, hP⟩ := sLocalThetaTransition_exists_retraction F hA
  let R (n : ℕ) : E F (S n) →L[ℂ] E F A := Nat.rec P (fun n r ↦ r.comp (Q n)) n
  have hc (m n : ℕ) (h : m ≤ n) (q : E F (S m)) : R n (i h q) = R m q := by
    induction n, h using Nat.le_induction with
    | base =>
      change R m (sLocalThetaTransition F (hS (le_refl m)) q) = R m q
      rw [sLocalThetaTransition_refl]
      rfl
    | succ n h ih =>
      rw [show i (h.trans (Nat.le_succ n)) q = i (Nat.le_succ n) (i h q) from
        (sLocalThetaTransition_apply_comp F (hS h) (hS (Nat.le_succ n)) q).symm]
      change R n (Q n (i (Nat.le_succ n) (i h q))) = _
      rw [hQ n, ih]
  let lift (T : Finset (Place F)) : E F T →L[ℂ] E F A :=
    (R (hcof T).choose).comp (sLocalThetaTransition F (hcof T).choose_spec)
  have hl (T : Finset (Place F)) (n : ℕ) (h : T ⊆ S n) (q : E F T) :
      lift T q = R n (sLocalThetaTransition F h q) := by
    let m := (hcof T).choose
    let k := max m n
    let hm : T ⊆ S m := (hcof T).choose_spec
    have hmk : m ≤ k := le_max_left _ _
    have hnk : n ≤ k := le_max_right _ _
    change R m (sLocalThetaTransition F hm q) = _
    rw [← hc m k hmk (sLocalThetaTransition F hm q),
      ← hc n k hnk (sLocalThetaTransition F h q)]
    exact congrArg (R k) ((sLocalThetaTransition_apply_comp F hm (hS hmk) q).trans
      (sLocalThetaTransition_apply_comp F h (hS hnk) q).symm)
  have hL (T U : Finset (Place F)) (h : T ⊆ U) (q : E F T) :
      lift U (sLocalThetaTransition F h q) = lift T q := by
    obtain ⟨n, hn⟩ := hcof U
    rw [hl U n hn, hl T n (h.trans hn), sLocalThetaTransition_apply_comp]
  letI : PolynormableSpace ℂ (E F A) :=
    polynormableSpace_complex_quotient (sLocalThetaOperator F A).ker
  obtain ⟨g, hg, _⟩ := globalThetaQuotient_existsUnique_lift F lift hL
  refine ⟨g, fun q ↦ ?_⟩
  rw [hg, hl A 0 hA]
  exact hP q

/-- The global quotient is Hausdorff because the continuous stage retractions
separate points on its exhaustive union of stages. -/
theorem globalThetaQuotient_t2Space : T2Space (G F) := by
  let R (A : Finset (Place F)) := (sLocalThetaToGlobal_exists_retraction F A).choose
  have hR (A : Finset (Place F)) : LeftInverse (R A) (sLocalThetaToGlobal F A) :=
    (sLocalThetaToGlobal_exists_retraction F A).choose_spec
  letI : ∀ A : Finset (Place F), T2Space (E F A) := sLocalThetaQuotient_t2Space F
  let L : G F →ₗ[ℂ] (∀ A : Finset (Place F), E F A) := LinearMap.pi (fun A ↦ (R A).toLinearMap)
  apply T2Space.of_injective_continuous (f := L)
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨A, _, _, x, rfl⟩ := globalThetaQuotient_exhausted_by_different_stages F ∅ q
    have hx : R A (sLocalThetaToGlobal F A x) = 0 := congrFun hq A
    rw [hR A] at hx
    rw [hx, map_zero]
  · exact continuous_pi (fun A ↦ (R A).continuous)

/-- Every finite theta stage is a complemented closed subspace of the actual
global theta quotient. -/
theorem sLocalThetaToGlobal_isClosedEmbedding (A : Finset (Place F)) :
    IsClosedEmbedding (sLocalThetaToGlobal F A) := by
  let j := sLocalThetaToGlobal F A
  obtain ⟨R, hR⟩ := sLocalThetaToGlobal_exists_retraction F A
  letI := globalThetaQuotient_t2Space F
  refine ⟨hR.isEmbedding R.continuous j.continuous, ?_⟩
  have he : range j = {q | j (R q) = q} := by
    ext q
    refine ⟨?_, fun h ↦ ⟨R q, h⟩⟩
    rintro ⟨x, rfl⟩
    exact congrArg j (hR x)
  rw [he]
  exact isClosed_eq (j.continuous.comp R.continuous) continuous_id

/-- On a cofinal sequence, the quotient still has the locally convex final
topology. -/
theorem globalThetaQuotient_continuous_of_cofinal {S : ℕ → Finset (Place F)}
    (hcof : ∀ T, ∃ n, T ⊆ S n)
    {R : Type*} [AddCommGroup R] [Module ℂ R] [TopologicalSpace R] [PolynormableSpace ℂ R]
    (L : G F →ₗ[ℂ] R)
    (hL : ∀ n, Continuous (L.comp (sLocalThetaToGlobal F (S n)).toLinearMap)) : Continuous L := by
  apply globalThetaQuotient_continuous_of_stages F
  intro T
  obtain ⟨n, hn⟩ := hcof T
  have he : L.comp (sLocalThetaToGlobal F T).toLinearMap =
      (L.comp (sLocalThetaToGlobal F (S n)).toLinearMap).comp (sLocalThetaTransition F hn).toLinearMap :=
    LinearMap.ext fun q ↦ congrArg L (sLocalThetaToGlobal_transition F hn q).symm
  rw [he]
  exact (hL n).comp (sLocalThetaTransition F hn).continuous

/-- The actual global theta quotient as the countable locally convex limit
of any cofinal increasing tower. -/
def globalThetaQuotient_tower (S : ℕ → Finset (Place F)) (hS : Monotone S)
    (hcof : ∀ T, ∃ n, T ⊆ S n) :
    LinearInductivePresentation (G F) (fun n ↦ E F (S n)) where
  incl n := sLocalThetaToGlobal F (S n)
  transition h := sLocalThetaTransition F (hS h)
  injective_incl n := sLocalThetaToGlobal_injective F (S n)
  incl_transition h x := sLocalThetaToGlobal_transition F (hS h) x
  exhaust q := by
    obtain ⟨T, _, _, x, hx⟩ := globalThetaQuotient_exhausted_by_different_stages F ∅ q
    obtain ⟨n, hn⟩ := hcof T
    exact ⟨n, sLocalThetaTransition F hn x, (sLocalThetaToGlobal_transition F hn x).trans hx⟩
  continuous_limit L :=
    ⟨fun h n ↦ h.comp (sLocalThetaToGlobal F (S n)).continuous,
      globalThetaQuotient_continuous_of_cofinal F hcof L⟩

/-- Every bounded subset of the global theta quotient comes from a bounded
subset of one finite theta stage. -/
theorem globalThetaQuotient_bounded_iff (B : Set (G F)) :
    IsVonNBounded ℂ B ↔
      ∃ (A : Finset (Place F)) (C : Set (E F A)),
        IsVonNBounded ℂ C ∧ sLocalThetaToGlobal F A '' C = B := by
  letI : T2Space (G F) := globalThetaQuotient_t2Space F
  letI : PolynormableSpace ℂ (G F) :=
    polynormableSpace_complex_quotient (globalThetaOperator F).ker
  letI : ∀ A : Finset (Place F), PolynormableSpace ℂ (E F A) :=
    fun A ↦ polynormableSpace_complex_quotient (sLocalThetaOperator F A).ker
  refine ⟨fun hB ↦ ?_, ?_⟩
  · obtain ⟨S, hS, _, hcof⟩ := exists_globalThetaCofinalTower F ∅
    let D := globalThetaQuotient_tower F S hS hcof
    have hcl (n : ℕ) : IsClosedEmbedding (D.transition (Nat.le_succ n)) :=
      sLocalThetaTransition_isClosedEmbedding F (hS (Nat.le_succ n))
    have he (n : ℕ) : IsEmbedding (D.incl n) :=
      (sLocalThetaToGlobal_isClosedEmbedding F (S n)).isEmbedding
    obtain ⟨n, C, hC, hCB⟩ := (D.strict_bounded_iff hcl he
      (globalThetaQuotient_continuous_of_cofinal F hcof) B).mp hB
    exact ⟨S n, C, hC, hCB⟩
  · rintro ⟨A, C, hC, rfl⟩
    exact hC.image (sLocalThetaToGlobal F A)

/-- The strong dual restricts to the compatible families of strong duals
on a cofinal tower, with the subspace topology from their product. -/
def globalThetaQuotient_strongDualRestriction (S : ℕ → Finset (Place F)) (hS : Monotone S)
    (hcof : ∀ T, ∃ n, T ⊆ S n) :
    StrongDual ℂ (G F) ≃L[ℂ] (globalThetaQuotient_tower F S hS hcof).CompatibleDual := by
  letI : T2Space (G F) := globalThetaQuotient_t2Space F
  letI : PolynormableSpace ℂ (G F) :=
    polynormableSpace_complex_quotient (globalThetaOperator F).ker
  letI : ∀ A : Finset (Place F), PolynormableSpace ℂ (E F A) :=
    fun A ↦ polynormableSpace_complex_quotient (sLocalThetaOperator F A).ker
  let D := globalThetaQuotient_tower F S hS hcof
  refine D.strongDualRestrictionOfStrict ?_ ?_ (globalThetaQuotient_continuous_of_cofinal F hcof)
  · exact fun n ↦ sLocalThetaTransition_isClosedEmbedding F (hS (Nat.le_succ n))
  · exact fun n ↦ (sLocalThetaToGlobal_isClosedEmbedding F (S n)).isEmbedding

/-- Compatibility of the strong dual restrictions is a closed condition
in the product of the stage duals. -/
theorem globalThetaQuotient_compatibleDual_isClosed (S : ℕ → Finset (Place F)) (hS : Monotone S)
    (hcof : ∀ T, ∃ n, T ⊆ S n) :
    letI (n : ℕ) : TopologicalSpace (StrongDual ℂ (E F (S n))) :=
      ContinuousLinearMap.topologicalSpace
    IsClosed ((globalThetaQuotient_tower F S hS hcof).CompatibleDual :
      Set (∀ n, StrongDual ℂ (E F (S n)))) := by
  letI (n : ℕ) : TopologicalSpace (StrongDual ℂ (E F (S n))) :=
    ContinuousLinearMap.topologicalSpace
  let D := globalThetaQuotient_tower F S hS hcof
  have he : (D.CompatibleDual : Set (∀ n, StrongDual ℂ (E F (S n)))) =
      ⋂ m : ℕ, ⋂ n : ℕ, ⋂ h : m ≤ n, ⋂ x : E F (S m),
        {g : ∀ n, StrongDual ℂ (E F (S n)) | g n (D.transition h x) = g m x} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq]
    rfl
  rw [he]
  refine isClosed_iInter fun m ↦ isClosed_iInter fun n ↦ isClosed_iInter fun h ↦
    isClosed_iInter fun x ↦ isClosed_eq ?_ ?_
  · exact (continuous_eval_const (D.transition h x)).comp (continuous_apply n)
  · exact (continuous_eval_const x).comp (continuous_apply m)

end

end Masullo
