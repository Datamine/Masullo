import StrictInductiveTelescope
import FrechetFactorization
import QuotientDuals

open Bornology Filter Function Set Topology UniformSpace
open scoped Uniformity ENNReal

namespace Masullo

noncomputable section

/-- A closed quotient of a Fréchet space is Fréchet for the quotient topology. -/
theorem isFrechetTVS_closedQuotient {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechetTVS E) (M : Submodule ℂ E)
    (hM : IsClosed (M : Set E)) : IsFrechetTVS (E ⧸ M) := by
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hE
  letI : IsClosed (M : Set E) := hM
  refine ⟨inferInstance, polynormableSpace_complex_quotient M, ?_,
    QuotientAddGroup.completeSpace_right' E M.toAddSubgroup⟩
  letI : UniformSpace (E ⧸ M) := IsTopologicalAddGroup.rightUniformSpace (E ⧸ M)
  have hz : map M.mkQ (𝓝 (0 : E)) = 𝓝 (0 : E ⧸ M) := by
    simpa only [map_zero] using M.isOpenQuotientMap_mkQ.map_nhds_eq (0 : E)
  letI : (𝓝 (0 : E ⧸ M)).IsCountablyGenerated :=
    hz ▸ Filter.map.isCountablyGenerated (𝓝 (0 : E)) M.mkQ
  letI : (𝓤 (E ⧸ M)).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  exact UniformSpace.metrizableSpace

/-- Factorization through a stage, with the Fréchet hypotheses expressed using
the additive uniformities of the given topologies. -/
theorem frechet_factorization_of_isFrechetTVS
    {A E : Type*} {X : ℕ → Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    (hA : IsFrechetTVS A) (hX : ∀ n, IsFrechetTVS (X n))
    (u : A →L[ℂ] E) (j : ∀ n, X n →L[ℂ] E)
    (hinj : ∀ n, Injective (j n)) (hexhaust : ∀ x : E, ∃ n, x ∈ range (j n)) :
    ∃ (n : ℕ) (v : A →L[ℂ] X n), (j n).comp v = u := by
  obtain ⟨hadd, hpoly, hmetric, hcomplete⟩ := hA
  choose haddX hpolyX hmetricX hcompleteX using hX
  letI : ∀ n, IsTopologicalAddGroup (X n) := haddX
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  letI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace A := hcomplete
  letI : ContinuousSMul ℂ A := (PolynormableSpace.withSeminorms ℂ A).continuousSMul
  letI : ∀ n, UniformSpace (X n) := fun _ ↦ IsTopologicalAddGroup.rightUniformSpace _
  letI : ∀ n, IsUniformAddGroup (X n) := fun _ ↦ isUniformAddGroup_of_addCommGroup
  letI : ∀ n, CompleteSpace (X n) := hcompleteX
  letI : ∀ n, TopologicalSpace.MetrizableSpace (X n) := hmetricX
  letI : ∀ n, FirstCountableTopology (X n) := fun _ ↦ inferInstance
  letI : ∀ n, PolynormableSpace ℂ (X n) := hpolyX
  letI : ∀ n, ContinuousSMul ℂ (X n) :=
    fun n ↦ (PolynormableSpace.withSeminorms ℂ (X n)).continuousSMul
  exact frechet_factorization u j hinj hexhaust

namespace LinearInductivePresentation

universe u v w
variable {E : Type u} {X : ℕ → Type v} {Y : ℕ → Type w}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
variable (D : LinearInductivePresentation E X) (F : Submodule ℂ E)

/-- The part of a stage killed by the quotient map on the limit. -/
abbrev stageKernel (n : ℕ) : Submodule ℂ (X n) := F.comap (D.incl n).toLinearMap

/-- The continuous inclusion of the quotient of a stage into the quotient of the limit. -/
def quotientStageInclusion (n : ℕ) : (X n ⧸ D.stageKernel F n) →L[ℂ] (E ⧸ F) :=
  (D.stageKernel F n).liftQL (F.mkQL.comp (D.incl n))
    (fun _ hx ↦ (Submodule.Quotient.mk_eq_zero F).mpr hx)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
@[simp] theorem quotientStageInclusion_mk (n : ℕ) (x : X n) :
    D.quotientStageInclusion F n ((D.stageKernel F n).mkQ x) = F.mkQ (D.incl n x) :=
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
theorem quotientStageInclusion_injective (n : ℕ) : Injective (D.quotientStageInclusion F n) := by
  apply (LinearMap.ker_eq_bot (f := (D.quotientStageInclusion F n).toLinearMap)).mp
  refine le_antisymm ?_ bot_le
  intro y hy
  obtain ⟨x, rfl⟩ := (D.stageKernel F n).mkQ_surjective y
  rw [Submodule.mem_bot]
  apply (Submodule.Quotient.mk_eq_zero (D.stageKernel F n)).mpr
  exact (Submodule.Quotient.mk_eq_zero F).mp hy

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
theorem quotientStageInclusion_exhaust (y : E ⧸ F) :
    ∃ n, y ∈ range (D.quotientStageInclusion F n) := by
  obtain ⟨x, rfl⟩ := F.mkQ_surjective y
  obtain ⟨n, z, hz⟩ := D.exhaust x
  exact ⟨n, (D.stageKernel F n).mkQ z, by rw [quotientStageInclusion_mk, hz]⟩

omit [ContinuousSMul ℂ E] in
/-- Every continuous map from a Fréchet space to the quotient factors
continuously through a stage quotient. -/
theorem quotientStage_factorization {A : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    (hF : IsClosed (F : Set E)) (hX : ∀ n, IsFrechetTVS (X n))
    (hA : IsFrechetTVS A) (u : A →L[ℂ] E ⧸ F) :
    ∃ (m : ℕ) (f : A →L[ℂ] X m ⧸ D.stageKernel F m),
      (D.quotientStageInclusion F m).comp f = u := by
  letI : IsClosed (F : Set E) := hF
  exact frechet_factorization_of_isFrechetTVS hA
    (fun m ↦ isFrechetTVS_closedQuotient (hX m) (D.stageKernel F m)
      (hF.preimage (D.incl m).continuous))
    u (D.quotientStageInclusion F) (D.quotientStageInclusion_injective F)
    (D.quotientStageInclusion_exhaust F)

variable [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]

include D in
/-- Bounded lifting in C.1.5.13. Bounded subsets of the strict quotient limit
factor into a quotient of an ambient stage and lift there to bounded subsets. -/
theorem quotient_liftsBounded_of_strict
    (hF : IsClosed (F : Set E)) (Dq : LinearInductivePresentation (E ⧸ F) Y)
    (hX : ∀ n, IsFrechetTVS (X n)) (hN : ∀ n, NuclearLocallyConvex.{v, v} (X n))
    (hY : ∀ n, IsFrechetTVS (Y n))
    (hclosed : ∀ n, IsClosedEmbedding (Dq.transition (Nat.le_succ n)))
    (hemb : ∀ n, IsEmbedding (Dq.incl n))
    (hlimit : ∀ T : (E ⧸ F) →ₗ[ℂ] lp (fun _ : ℕ ↦ ℂ) ∞,
      (∀ n, Continuous (T.comp (Dq.incl n).toLinearMap)) → Continuous T)
    {B : Set (E ⧸ F)} (hB : IsVonNBounded ℂ B) :
    ∃ C : Set E, IsVonNBounded ℂ C ∧ F.mkQ '' C = B := by
  letI : IsClosed (F : Set E) := hF
  have hY' := hY
  choose hadd hpoly _ _ using hY'
  letI : ∀ n, IsTopologicalAddGroup (Y n) := hadd
  letI : ∀ n, PolynormableSpace ℂ (Y n) := hpoly
  letI (n : ℕ) : ContinuousSMul ℂ (Y n) :=
    (PolynormableSpace.withSeminorms ℂ (Y n)).continuousSMul
  obtain ⟨n, S, hS, rfl⟩ := (Dq.strict_bounded_iff hclosed hemb hlimit B).mp hB
  have hk (m : ℕ) : IsClosed (D.stageKernel F m : Set (X m)) :=
    hF.preimage (D.incl m).continuous
  obtain ⟨m, f, hf⟩ := D.quotientStage_factorization F hF hX (hY n) (Dq.incl n)
  obtain ⟨K, hK, hcover⟩ := nuclearFrechet_quotient_compactLift
    (D.stageKernel F m) (hk m) (hN m) (hX m) (hS.image f)
  let C := D.incl m '' K
  have hC : IsVonNBounded ℂ C := (hK.image (D.incl m).continuous).isVonNBounded ℂ
  let T := Dq.incl n '' S
  have hsub : T ⊆ F.mkQ '' C := by
    rintro y ⟨x, hx, rfl⟩
    have hmem : f x ∈ (D.stageKernel F m).mkQ '' K := by
      rw [hcover]
      exact subset_closure (mem_image_of_mem f hx)
    obtain ⟨z, hzK, hz⟩ := hmem
    refine ⟨D.incl m z, mem_image_of_mem (D.incl m) hzK, ?_⟩
    rw [← D.quotientStageInclusion_mk F m z, hz]
    exact DFunLike.congr_fun hf x
  exact ⟨C ∩ F.mkQ ⁻¹' T, hC.subset inter_subset_left, by
    rw [image_inter_preimage, inter_eq_right.mpr hsub]⟩

omit [ContinuousSMul ℂ E] in
/-- The ambient and quotient defining sequences can be reindexed together so
each stage on either side is contained in the corresponding next stage on the
other side after applying the quotient map. -/
theorem quotient_interleaving
    (hF : IsClosed (F : Set E))
    (Dq : LinearInductivePresentation (E ⧸ F) Y)
    (hX : ∀ n, IsFrechetTVS (X n)) (hY : ∀ n, IsFrechetTVS (Y n)) :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      (∀ n, F.mkQ '' range (D.incl (a n)) ⊆ range (Dq.incl (a (n+1)))) ∧
      (∀ n, range (Dq.incl (a n)) ⊆ F.mkQ '' range (D.incl (a (n+1)))) := by
  letI : IsClosed (F : Set E) := hF
  have hupper (n : ℕ) :
      ∃ m, F.mkQ '' range (D.incl n) ⊆ range (Dq.incl m) := by
    obtain ⟨m, f, hf⟩ := frechet_factorization_of_isFrechetTVS (hX n)
      hY (F.mkQL.comp (D.incl n)) Dq.incl Dq.injective_incl Dq.exhaust
    refine ⟨m, ?_⟩
    rintro y ⟨z, ⟨x, hx⟩, hy⟩
    exact ⟨f x, (DFunLike.congr_fun hf x).trans ((congrArg F.mkQ hx).trans hy)⟩
  have hlower (n : ℕ) :
      ∃ m, range (Dq.incl n) ⊆ F.mkQ '' range (D.incl m) := by
    obtain ⟨m, f, hf⟩ := D.quotientStage_factorization F hF hX (hY n) (Dq.incl n)
    refine ⟨m, ?_⟩
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := (D.stageKernel F m).mkQ_surjective (f y)
    refine ⟨D.incl m x, mem_range_self x, ?_⟩
    rw [← D.quotientStageInclusion_mk F m x, hx]
    exact DFunLike.congr_fun hf y
  choose upper hUpper using hupper
  choose lower hLower using hlower
  let a : ℕ → ℕ := Nat.rec 0 (fun _ k ↦ max (k+1) (max (upper k) (lower k)))
  refine ⟨a, strictMono_nat_of_lt_succ (fun n ↦
    lt_of_lt_of_le (Nat.lt_succ_self (a n)) (le_max_left _ _)), ?_, ?_⟩
  · intro n
    exact (hUpper (a n)).trans (Dq.range_incl_mono ((le_max_left _ _).trans (le_max_right _ _)))
  · intro n
    exact (hLower (a n)).trans
      (image_mono (D.range_incl_mono ((le_max_right _ _).trans (le_max_right _ _))))

end LinearInductivePresentation

end

end Masullo
