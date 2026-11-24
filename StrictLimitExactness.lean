import InductiveLimitDuals
import StrictLimitKernel
import NuclearPermanence
import Mathlib.Algebra.Exact.Basic

open Function Set Topology

namespace Masullo

section Algebraic

variable {E₀ E₁ E₂ : Type*} {A₀ A₁ A₂ : ℕ → Type*}
  [AddCommGroup E₀] [Module ℂ E₀] [TopologicalSpace E₀]
  [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
  [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
  [∀ n, AddCommGroup (A₀ n)] [∀ n, Module ℂ (A₀ n)] [∀ n, TopologicalSpace (A₀ n)]
  [∀ n, AddCommGroup (A₁ n)] [∀ n, Module ℂ (A₁ n)] [∀ n, TopologicalSpace (A₁ n)]
  [∀ n, AddCommGroup (A₂ n)] [∀ n, Module ℂ (A₂ n)] [∀ n, TopologicalSpace (A₂ n)]

/-- Exactness of a compatible sequence on exhausted stages gives algebraic
exactness on the three inductive limits. -/
theorem exact_of_inductive_presentations
    (D₀ : LinearInductivePresentation E₀ A₀) (D₁ : LinearInductivePresentation E₁ A₁)
    (D₂ : LinearInductivePresentation E₂ A₂)
    (j : E₀ →L[ℂ] E₁) (q : E₁ →L[ℂ] E₂)
    (jₙ : ∀ n, A₀ n →L[ℂ] A₁ n) (qₙ : ∀ n, A₁ n →L[ℂ] A₂ n)
    (hj : ∀ n, j.comp (D₀.incl n) = (D₁.incl n).comp (jₙ n))
    (hq : ∀ n, q.comp (D₁.incl n) = (D₂.incl n).comp (qₙ n))
    (hji : ∀ n, Injective (jₙ n)) (hex : ∀ n, Exact (jₙ n) (qₙ n))
    (hqs : ∀ n, Surjective (qₙ n)) :
    Injective j ∧ Exact j q ∧ Surjective q := by
  have hj' (n : ℕ) (z : A₀ n) : j (D₀.incl n z) = D₁.incl n (jₙ n z) :=
    DFunLike.congr_fun (hj n) z
  have hq' (n : ℕ) (z : A₁ n) : q (D₁.incl n z) = D₂.incl n (qₙ n z) :=
    DFunLike.congr_fun (hq n) z
  refine ⟨(injective_iff_map_eq_zero j).mpr ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, z, rfl⟩ := D₀.exhaust x
    rw [hj', ← (D₁.incl n).map_zero] at hx
    have hz : z = 0 := hji n (by simpa only [map_zero] using D₁.injective_incl n hx)
    rw [hz, map_zero]
  · intro x
    constructor
    · intro hx
      obtain ⟨n, z, rfl⟩ := D₁.exhaust x
      rw [hq', ← (D₂.incl n).map_zero] at hx
      obtain ⟨w, hw⟩ := (hex n z).mp (D₂.injective_incl n hx)
      exact ⟨D₀.incl n w, (hj' n w).trans (congrArg (D₁.incl n) hw)⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨n, z, rfl⟩ := D₀.exhaust y
      rw [hj', hq', (hex n (jₙ n z)).mpr (mem_range_self _), map_zero]
  · intro x
    obtain ⟨n, z, rfl⟩ := D₂.exhaust x
    obtain ⟨y, rfl⟩ := hqs n z
    exact ⟨D₁.incl n y, hq' n y⟩

end Algebraic

section Quotient

variable {E F : Type*} {X Y : ℕ → Type*}
  [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]

/-- A compatible surjection to a locally convex final limit is a quotient
when it is a quotient on every stage. -/
theorem quotient_of_inductive_presentations
    (D : LinearInductivePresentation E X) (C : LinearInductivePresentation F Y)
    (q : E →L[ℂ] F) (qₙ : ∀ n, X n →L[ℂ] Y n)
    (h : ∀ n, q.comp (D.incl n) = (C.incl n).comp (qₙ n))
    (hqo : ∀ n, IsOpenQuotientMap (qₙ n))
    (hfinal : ∀ p : Seminorm ℂ F,
      (∀ n, Continuous (p.comp (C.incl n).toLinearMap)) → Continuous p) :
    IsOpenQuotientMap q := by
  have hs : Surjective q := by
    intro x
    obtain ⟨n, y, rfl⟩ := C.exhaust x
    obtain ⟨z, rfl⟩ := (hqo n).surjective y
    exact ⟨D.incl n z, DFunLike.congr_fun (h n) z⟩
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  let K := q.ker
  letI : PolynormableSpace ℂ (E ⧸ K) := polynormableSpace_complex_quotient K
  let e : (E ⧸ K) ≃ₗ[ℂ] F := q.toLinearMap.quotKerEquivOfSurjective hs
  have he (x : E) : e (K.mkQL x) = q x :=
    q.toLinearMap.quotKerEquivOfSurjective_apply_mk hs x
  have hce : Continuous e :=
    K.isOpenQuotientMap_mkQL.continuous_comp_iff.mp (q.continuous.congr (fun x => (he x).symm))
  have hcinv (n : ℕ) : Continuous (fun y : Y n => e.symm (C.incl n y)) := by
    apply (hqo n).continuous_comp_iff.mp
    exact (K.mkQL.continuous.comp (D.incl n).continuous).congr (fun x => by
      change K.mkQL (D.incl n x) = e.symm (C.incl n (qₙ n x))
      have hx : q (D.incl n x) = C.incl n (qₙ n x) := DFunLike.congr_fun (h n) x
      rw [← hx, ← he, e.symm_apply_apply])
  have hcont : Continuous e.symm :=
    (PolynormableSpace.withSeminorms ℂ (E ⧸ K)).continuous_of_continuous_comp e.symm.toLinearMap
      (fun p => hfinal (p.val.comp e.symm.toLinearMap) (fun n => p.property.comp (hcinv n)))
  let L : (E ⧸ K) ≃L[ℂ] F := ⟨e, hce, hcont⟩
  exact ⟨hs, q.continuous, (show (q : E → F) = L ∘ K.mkQL from funext fun x => (he x).symm) ▸
    (L.toHomeomorph.isOpenMap.comp K.isOpenQuotientMap_mkQL.isOpenMap)⟩

end Quotient

noncomputable section

variable {E₀ E₁ E₂ : Type*} {A₀ A₁ A₂ : ℕ → Type*}
  [AddCommGroup E₀] [Module ℂ E₀] [TopologicalSpace E₀] [PolynormableSpace ℂ E₀]
  [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂] [T1Space E₂]
  [∀ n, AddCommGroup (A₀ n)] [∀ n, Module ℂ (A₀ n)] [∀ n, TopologicalSpace (A₀ n)]
  [∀ n, AddCommGroup (A₁ n)] [∀ n, Module ℂ (A₁ n)] [∀ n, TopologicalSpace (A₁ n)]
  [∀ n, AddCommGroup (A₂ n)] [∀ n, Module ℂ (A₂ n)] [∀ n, TopologicalSpace (A₂ n)]

/-- Closed embeddings on the kernels pass to the strict limit when the
quotient stage images are closed and the middle limit has the final topology. -/
theorem closedEmbedding_of_exact_inductive_presentations
    (D₀ : LinearInductivePresentation E₀ A₀) (D₁ : LinearInductivePresentation E₁ A₁)
    (D₂ : LinearInductivePresentation E₂ A₂)
    (j : E₀ →L[ℂ] E₁) (q : E₁ →L[ℂ] E₂)
    (jₙ : ∀ n, A₀ n →L[ℂ] A₁ n) (qₙ : ∀ n, A₁ n →L[ℂ] A₂ n)
    (hj : ∀ n, j.comp (D₀.incl n) = (D₁.incl n).comp (jₙ n))
    (hq : ∀ n, q.comp (D₁.incl n) = (D₂.incl n).comp (qₙ n))
    (hji : ∀ n, IsEmbedding (jₙ n)) (hex : ∀ n, Exact (jₙ n) (qₙ n))
    (hqs : ∀ n, Surjective (qₙ n))
    (hFr : ∀ n, IsFrechetTVS (A₁ n)) (hEmb : ∀ n, IsEmbedding (D₁.incl n))
    (hClosed : ∀ n, IsClosed (range (D₂.incl n)))
    (hFinal : ∀ r : Seminorm ℂ E₁,
      (∀ n, Continuous (r.comp (D₁.incl n).toLinearMap)) → Continuous r) :
    IsClosedEmbedding j := by
  obtain ⟨hinj, hExact, hsurj⟩ := exact_of_inductive_presentations
    D₀ D₁ D₂ j q jₙ qₙ hj hq (fun n => (hji n).injective) hex hqs
  have hj' (n : ℕ) (z : A₀ n) : j (D₀.incl n z) = D₁.incl n (jₙ n z) :=
    DFunLike.congr_fun (hj n) z
  have hq' (n : ℕ) (z : A₁ n) : q (D₁.incl n z) = D₂.incl n (qₙ n z) :=
    DFunLike.congr_fun (hq n) z
  let K := q.ker
  let eQ : (E₁ ⧸ K) ≃ₗ[ℂ] E₂ := q.toLinearMap.quotKerEquivOfSurjective hsurj
  have hQV (x : E₁) : eQ (K.mkQ x) = q x :=
    q.toLinearMap.quotKerEquivOfSurjective_apply_mk hsurj x
  have hQ : Continuous eQ := K.isQuotientMap_mkQ.continuous_iff.mpr
    (q.continuous.congr fun x => (hQV x).symm)
  have hImg (n : ℕ) : IsClosed (K.mkQ '' range (D₁.incl n)) := by
    have hEq : K.mkQ '' range (D₁.incl n) = eQ ⁻¹' range (D₂.incl n) := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨qₙ n x, (hQV _).trans (hq' n x) |>.symm⟩
      · rintro ⟨y, hy⟩
        obtain ⟨x, rfl⟩ := hqs n y
        exact ⟨D₁.incl n x, mem_range_self _, eQ.injective
          ((hQV _).trans ((hq' n x).trans hy))⟩
    rw [hEq]
    exact (hClosed n).preimage hQ
  let J : E₀ →L[ℂ] K := j.codRestrict K (fun x => (hExact (j x)).mpr (mem_range_self x))
  have hJ : Bijective J := ⟨fun _ _ h => hinj (congrArg Subtype.val h), fun x => by
    obtain ⟨y, hy⟩ := (hExact x.val).mp x.property
    exact ⟨y, Subtype.ext hy⟩⟩
  let e := LinearEquiv.ofBijective J.toLinearMap hJ
  have hInv (n : ℕ) : Continuous (fun x => e.symm (D₁.kernelStageInclusion K n x)) := by
    let v : D₁.stageKernel K n → (jₙ n).toLinearMap.range := fun x => ⟨x.val, by
      apply (hex n x.val).mp
      apply D₂.injective_incl n
      rw [map_zero, ← hq']
      exact x.property⟩
    have hv : Continuous v := continuous_subtype_val.subtype_mk _
    let a := LinearEquiv.ofInjective (jₙ n).toLinearMap (hji n).injective
    have ha : Continuous a.symm := (hji n).isInducing.continuous_iff.mpr
      (continuous_subtype_val.congr fun x => (congrArg Subtype.val (a.apply_symm_apply x)).symm)
    apply ((D₀.incl n).continuous.comp (ha.comp hv)).congr
    intro x
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change j (D₀.incl n (a.symm (v x))) = D₁.incl n x.val
    rw [hj' n]
    exact congrArg (D₁.incl n) (congrArg Subtype.val (a.apply_symm_apply (v x)))
  have hce : Continuous e.symm :=
    (PolynormableSpace.withSeminorms ℂ E₀).continuous_of_continuous_comp e.symm.toLinearMap
      (fun p => by
        obtain ⟨r, hr, he⟩ := D₁.kernel_seminorm_extension_of_closedStageImages K q.isClosed_ker
          hFr hEmb hImg hFinal (p.val.comp e.symm.toLinearMap)
          (fun n => p.property.comp (hInv n))
        rw [← he]
        exact hr.comp continuous_subtype_val)
  let L : E₀ ≃L[ℂ] K := ⟨e, J.continuous, hce⟩
  exact (q.isClosed_ker.isClosedEmbedding_subtypeVal.comp L.toHomeomorph.isClosedEmbedding :
    IsClosedEmbedding (Subtype.val ∘ L))

end

end Masullo
