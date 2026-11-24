import SLocalBruhatFrechet
import GlobalThetaStageRetraction

open Function IsDedekindDomain NumberField Set Topology

open scoped Classical NumberField SchwartzMap

namespace Masullo

noncomputable section

namespace LinearInductivePresentation

universe u v

variable {E : Type u} {X : ℕ → Type v}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]

variable (D : LinearInductivePresentation E X) (K : Submodule ℂ E)

private def restrictedQuotientTransition {m n : ℕ} (h : m ≤ n) :
    (X m ⧸ D.stageKernel K m) →L[ℂ] (X n ⧸ D.stageKernel K n) :=
  (D.stageKernel K m).liftQL ((D.stageKernel K n).mkQL.comp (D.transition h)) (by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change D.incl n (D.transition h x) ∈ K
    rw [D.incl_transition]
    exact hx)

/-- Quotienting an exhaustive locally convex tower gives the quotient maps on
its stages and the scalar final property for their intrinsic quotient topologies. -/
def quotientPresentation :
    LinearInductivePresentation (E ⧸ K) (fun n ↦ X n ⧸ D.stageKernel K n) where
  incl := D.quotientStageInclusion K
  transition h := restrictedQuotientTransition D K h
  injective_incl := D.quotientStageInclusion_injective K
  incl_transition h q := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    change K.mkQ (D.incl _ (D.transition h x)) = K.mkQ (D.incl _ x)
    rw [D.incl_transition]
  exhaust := D.quotientStageInclusion_exhaust K
  continuous_limit L := by
    refine ⟨fun h n ↦ h.comp (D.quotientStageInclusion K n).continuous, fun h ↦ ?_⟩
    apply K.isQuotientMap_mkQ.continuous_iff.mpr
    apply (D.continuous_limit (L.comp K.mkQ)).mpr
    intro n
    let π := (D.stageKernel K n).mkQL
    change Continuous ((L.comp K.mkQ).comp (D.incl n).toLinearMap)
    have he : (L.comp K.mkQ).comp (D.incl n).toLinearMap =
        (L.comp (D.quotientStageInclusion K n).toLinearMap).comp π.toLinearMap := by rfl
    rw [he]
    exact (h n).comp π.continuous

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
/-- The final topology for seminorms also descends along the stage quotients. -/
theorem quotientPresentation_seminorm_continuous
    (hfinal : ∀ p : Seminorm ℂ E, (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) → Continuous p)
    (p : Seminorm ℂ (E ⧸ K))
    (hp : ∀ n, Continuous (p.comp ((D.quotientPresentation K).incl n).toLinearMap)) :
    Continuous p := by
  apply K.isQuotientMap_mkQ.continuous_iff.mpr
  change Continuous (p.comp K.mkQ)
  apply hfinal
  intro n
  exact (hp n).comp (D.stageKernel K n).mkQL.continuous

end LinearInductivePresentation

universe u

variable (F : Type u) [Field F] [NumberField F]

private abbrev Place := HeightOneSpectrum (𝓞 F)
private abbrev Test (S : Finset (Place F)) := sLocalBruhatImage F S
private abbrev Theta (S : Finset (Place F)) := SLocalThetaQuotient F S

/-- Each actual S-local ordinary theta quotient has an exhaustive locally
convex final presentation by intrinsic Fréchet quotients of test stages. -/
theorem sLocalThetaQuotient_exists_frechetStages (S : Finset (Place F)) :
    ∃ (X : ℕ → Type u) (_ : ∀ n, AddCommGroup (X n)) (_ : ∀ n, Module ℂ (X n))
      (_ : ∀ n, TopologicalSpace (X n)) (D : LinearInductivePresentation (Theta F S) X),
      (∀ n, IsFrechetTVS (X n)) ∧
      (∀ p : Seminorm ℂ (Theta F S), (∀ n, Continuous (p.comp (D.incl n).toLinearMap)) →
        Continuous p) := by
  obtain ⟨_, _, D, hFr, _, _, hfinal⟩ := sLocalBruhat_exists_frechetPresentation F S
  let K := (sLocalThetaOperator F S).ker
  letI : T2Space (Theta F S) := sLocalThetaQuotient_t2Space F S
  have hK : IsClosed (K : Set (Test F S)) := by
    have he : (K : Set (Test F S)) = K.mkQL ⁻¹' {0} := by
      ext f
      exact (Submodule.Quotient.mk_eq_zero K).symm
    rw [he]
    exact isClosed_singleton.preimage K.mkQL.continuous
  refine ⟨_, _, _, _, D.quotientPresentation K, ?_, D.quotientPresentation_seminorm_continuous K hfinal⟩
  intro n
  exact isFrechetTVS_closedQuotient (hFr n) _ (hK.preimage (D.incl n).continuous)

/-- The S-local ordinary theta quotient at the archimedean stage is Fréchet. -/
theorem archStageThetaQuotient_isFrechet : IsFrechetTVS (Theta F ∅) := by
  let K := (sLocalThetaOperator F ∅).ker
  letI : T2Space (Theta F ∅) := sLocalThetaQuotient_t2Space F ∅
  apply isFrechetTVS_closedQuotient (archStageBruhat_isFrechet F) K
  have he : (K : Set (Test F ∅)) = K.mkQL ⁻¹' {0} := by
    ext f
    exact (Submodule.Quotient.mk_eq_zero K).symm
  rw [he]
  exact isClosed_singleton.preimage K.mkQL.continuous

/-- Translation by S-units reduces every finite valuation vector to
the fixed box of side length the class number. -/
theorem sUnitValuation_normalize (S : Finset (Place F)) (k : S → ℤ) :
    ∃ u : Additive (sIntegerRing F S)ˣ, ∀ v : S,
      0 ≤ k v - sUnitValuation F S u v ∧
      k v - sUnitValuation F S u v < Nat.card (ClassGroup (𝓞 F)) := by
  let h := Nat.card (ClassGroup (𝓞 F))
  have hh : (0 : ℤ) < h := by exact_mod_cast (Nat.card_pos (α := ClassGroup (𝓞 F)))
  let q (v : S) := k v / (h : ℤ)
  obtain ⟨u, hu⟩ := sUnitValuation_classNumber F S q
  refine ⟨u, fun v ↦ ?_⟩
  have hv : sUnitValuation F S u v = (h : ℤ) * (k v / (h : ℤ)) := by
    have he := congrFun hu v
    change sUnitValuation F S u v = h • q v at he
    simpa only [q, nsmul_eq_mul] using he
  rw [hv, show k v - (h : ℤ) * (k v / (h : ℤ)) = k v % (h : ℤ) by
    have he := Int.mul_ediv_add_emod (k v) (h : ℤ)
    omega]
  exact ⟨Int.emod_nonneg _ hh.ne', Int.emod_lt_of_pos _ hh⟩

/-- An S-unit translation does not change the S-local theta class. -/
theorem sLocalThetaTranslate_sUnit (S : Finset (Place F)) (u : (sIntegerRing F S)ˣ)
    (q : Theta F S) :
    sLocalThetaTranslate F S
        (QuotientGroup.mk (Units.map (sAdelesProjection F S).toMonoidHom
          (principalIdele F (sUnitToField F S u)))) q = q := by
  let g := Units.map (sAdelesProjection F S).toMonoidHom (principalIdele F (sUnitToField F S u))
  have hg : (QuotientGroup.mk g : SIdeleQuotient F S) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩
  apply sLocalThetaToGlobal_injective F S
  change sLocalThetaToGlobal F S (sLocalThetaTranslate F S (QuotientGroup.mk g) q) = _
  rw [hg]
  have h₁ : (QuotientGroup.mk (1 : (SAdeles F S)ˣ) : SIdeleQuotient F S) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.one_mem _)
  rw [← h₁, sLocalThetaToGlobal_translate_class, map_one, Subgroup.coe_one, map_one,
    globalThetaTranslate_one]
  rfl

end

end Masullo
