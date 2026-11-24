import SeminormGluing

open Bornology Function Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

namespace LinearInductivePresentation

universe u v w
variable {E : Type u} {X : ℕ → Type v} {Y : ℕ → Type w}
variable [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
variable (D : LinearInductivePresentation E X) (F : Submodule ℂ E)

/-- The kernel stage included into the ambient kernel with its subspace topology. -/
def kernelStageInclusion (n : ℕ) : D.stageKernel F n →L[ℂ] F :=
  ((D.incl n).comp (D.stageKernel F n).subtypeL).codRestrict F fun x ↦ x.property

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
/-- When all stage images in the quotient are closed, every seminorm on the
kernel that is continuous on its stages extends continuously to the limit. -/
theorem kernel_seminorm_extension_of_closedStageImages
    (hF : IsClosed (F : Set E)) (hX : ∀ n, IsFrechetTVS (X n))
    (hEmb : ∀ n, IsEmbedding (D.incl n))
    (hImage : ∀ n, IsClosed (F.mkQ '' range (D.incl n)))
    (hlimit : ∀ r : Seminorm ℂ E,
      (∀ n, Continuous (r.comp (D.incl n).toLinearMap)) → Continuous r)
    (p : Seminorm ℂ F) (hp : ∀ n, Continuous (p.comp (D.kernelStageInclusion F n).toLinearMap)) :
    ∃ r : Seminorm ℂ E, Continuous r ∧ r.comp F.subtype = p := by
  let K := D.stageKernel F
  let P (n : ℕ) := p.comp (D.kernelStageInclusion F n).toLinearMap
  have hK (n : ℕ) : IsClosed (K n : Set (X n)) := hF.preimage (D.incl n).continuous
  have hpoly (n : ℕ) : PolynormableSpace ℂ (X n) := by
    obtain ⟨_, h, _, _⟩ := hX n
    exact h
  letI : ∀ n, PolynormableSpace ℂ (X n) := hpoly
  let Ext (n : ℕ) := {r : Seminorm ℂ (X n) // Continuous r ∧ r.comp (K n).subtype = P n}
  have hinit : Nonempty (Ext 0) := by
    obtain ⟨r, hr, he⟩ := exists_continuousSeminorm_extension (K 0).subtypeL
      IsEmbedding.subtypeVal (P 0) (hp 0)
    exact ⟨⟨r, hr, he⟩⟩
  have hnext (n : ℕ) (s : Ext n) : ∃ r : Ext (n+1),
      r.val.comp (D.transition (Nat.le_succ n)).toLinearMap = s.val := by
    let j := D.transition (Nat.le_succ n)
    let S := j.toLinearMap.range
    let T := K (n+1)
    let d := F.mkQL.comp (D.incl (n+1))
    have hemb : IsEmbedding j := by
      apply (hEmb (n+1)).of_comp_iff.mp
      exact (show (D.incl (n+1)) ∘ j = D.incl n from funext (D.incl_transition _)).symm ▸ hEmb n
    have hS : IsClosed (S : Set (X (n+1))) := by
      obtain ⟨_, _, hm, _⟩ := hX (n+1)
      letI : IsTopologicalAddGroup (X (n+1)) :=
        (PolynormableSpace.withSeminorms ℂ (X (n+1))).topologicalAddGroup
      exact ((hX n).isClosedEmbedding j hemb).isClosed_range
    have hSum : (↑(S ⊔ T) : Set (X (n+1))) = d ⁻¹' (F.mkQ '' range (D.incl n)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨_, ⟨a, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
        have hb0 : d b = 0 := (Submodule.Quotient.mk_eq_zero F).mpr hb
        have ha : d (j a) = F.mkQ (D.incl n a) := congrArg F.mkQ (D.incl_transition _ a)
        exact ⟨D.incl n a, mem_range_self a, by
          change F.mkQ (D.incl n a) = d (j a+b)
          rw [map_add, ha, hb0, add_zero]⟩
      · rintro ⟨_, ⟨a, rfl⟩, ha⟩
        have he : d (j a) = d x := (congrArg F.mkQ (D.incl_transition _ a)).trans ha
        have hb0 : d (x-j a) = 0 := by rw [map_sub, he, sub_self]
        refine Submodule.mem_sup.mpr ⟨j a, ⟨a, rfl⟩, x-j a,
          (Submodule.Quotient.mk_eq_zero F).mp hb0, ?_⟩
        exact add_sub_cancel .. |>.trans (by rfl)
    let e := LinearEquiv.ofInjective j.toLinearMap hemb.injective
    have he : Continuous e.symm := by
      apply (hemb.isInducing.continuous_iff).mpr
      exact continuous_subtype_val.congr (fun x ↦ congrArg Subtype.val (e.apply_symm_apply x).symm)
    let q := s.val.comp e.symm.toLinearMap
    have hcompat (x : X (n+1)) (hxS : x ∈ S) (hxT : x ∈ T) :
        q ⟨x, hxS⟩ = P (n+1) ⟨x, hxT⟩ := by
      obtain ⟨a, rfl⟩ := hxS
      have haK : a ∈ K n := by
        change D.incl n a ∈ F
        rw [← D.incl_transition (Nat.le_succ n) a]
        exact hxT
      change s.val (e.symm (e a)) = _
      rw [LinearEquiv.symm_apply_apply]
      have hsa := DFunLike.congr_fun s.property.2 (⟨a, haK⟩ : K n)
      change s.val a = p (D.kernelStageInclusion F n ⟨a, haK⟩) at hsa
      rw [hsa]
      exact congrArg p (Subtype.ext (D.incl_transition (Nat.le_succ n) a).symm)
    obtain ⟨r, hr, hrS, hrT⟩ := exists_continuousSeminorm_glue (hX (n+1)) S T hS
      (hK (n+1)) (hSum ▸ (hImage n).preimage d.continuous) q (P (n+1))
      (s.property.1.comp he) (hp (n+1)) hcompat
    refine ⟨⟨r, hr, hrT⟩, ?_⟩
    ext x
    have h := DFunLike.congr_fun hrS (e x)
    change r (j x) = s.val (e.symm (e x)) at h
    change r (j x) = s.val x
    simpa only [LinearEquiv.symm_apply_apply] using h
  let r : ∀ n, Ext n := Nat.rec hinit.some (fun n s ↦ (hnext n s).choose)
  have hcompatible (m n : ℕ) (h : m ≤ n) (x : X m) :
      (r n).val (D.transition h x) = (r m).val x := by
    induction n, h using Nat.le_induction with
    | base => rw [D.transition_id]
    | succ n h ih =>
      rw [← D.transition_comp h (Nat.le_succ n)]
      exact (DFunLike.congr_fun (hnext n (r n)).choose_spec _).trans ih
  obtain ⟨R, hR⟩ := D.exists_seminorm_of_compatible (fun n ↦ (r n).val) hcompatible
  refine ⟨R, hlimit R (fun n ↦ by rw [hR]; exact (r n).property.1), ?_⟩
  ext x
  obtain ⟨n, y, hy⟩ := D.exhaust x.val
  have hyK : y ∈ K n := by
    change D.incl n y ∈ F
    rw [hy]
    exact x.property
  have hRy := DFunLike.congr_fun (hR n) y
  have hry := DFunLike.congr_fun (r n).property.2 (⟨y, hyK⟩ : K n)
  change R (D.incl n y) = (r n).val y at hRy
  change (r n).val y = p (D.kernelStageInclusion F n ⟨y, hyK⟩) at hry
  exact (congrArg R hy.symm).trans (hRy.trans (hry.trans (congrArg p (Subtype.ext hy))))

variable [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]

omit [ContinuousSMul ℂ E] in
/-- For a strict Fréchet quotient, stagewise continuous seminorms on the
kernel are continuous in its induced topology. The adapted stages have
closed quotient images and remain cofinal in the original limit. -/
theorem kernel_seminorm_continuous_of_strictQuotient
    (hF : IsClosed (F : Set E)) (Dq : LinearInductivePresentation (E ⧸ F) Y)
    (hX : ∀ n, IsFrechetTVS (X n)) (hY : ∀ n, IsFrechetTVS (Y n))
    (hEmb : ∀ n, IsEmbedding (D.incl n)) (hEmbQ : ∀ n, IsEmbedding (Dq.incl n))
    (hlimit : ∀ r : Seminorm ℂ E,
      (∀ n, Continuous (r.comp (D.incl n).toLinearMap)) → Continuous r)
    (p : Seminorm ℂ F) (hp : ∀ n, Continuous (p.comp (D.kernelStageInclusion F n).toLinearMap)) :
    Continuous p := by
  obtain ⟨a, ha, hClosed, hImg, hCov⟩ := D.quotient_adaptedStages F Dq hF hX hY hEmbQ
  let A := D.adaptedQuotientStage F Dq a
  let i := D.adaptedQuotientInclusion F Dq a
  have hi (n : ℕ) : IsEmbedding (i n) := (hEmb _).comp IsEmbedding.subtypeVal
  let e (n : ℕ) := LinearEquiv.ofInjective (i (n+1)).toLinearMap (hi (n+1)).injective
  let f (n : ℕ) : X n →ₗ[ℂ] A (n+1) :=
    (e n).symm.toLinearMap.comp ((D.incl n).toLinearMap.codRestrict _ (fun x ↦ hCov n (mem_range_self x)))
  have hf (n : ℕ) (x : X n) : i (n+1) (f n x) = D.incl n x :=
    congrArg Subtype.val ((e n).apply_symm_apply _)
  have hfc (n : ℕ) : Continuous (f n) := by
    apply ((hi (n+1)).isInducing.continuous_iff).mpr
    exact (D.incl n).continuous.congr (fun x ↦ (hf n x).symm)
  let P : LinearInductivePresentation E (fun n ↦ ↥(A n)) :=
    { incl := i
      transition := fun h ↦ D.adaptedQuotientTransition F Dq a ha.monotone h
      injective_incl := fun n ↦ (hi n).injective
      incl_transition := fun h x ↦ D.adaptedQuotientInclusion_transition F Dq a ha.monotone h x
      exhaust := fun x ↦ by
        obtain ⟨n, hx⟩ := D.exhaust x
        exact ⟨n+1, hCov n hx⟩
      continuous_limit := fun l ↦
        ⟨fun h n ↦ h.comp (i n).continuous, fun h ↦ (D.continuous_limit l).mpr fun n ↦ by
          exact ((h (n+1)).comp (hfc n)).congr (fun x ↦ congrArg l (hf n x))⟩ }
  have hP (r : Seminorm ℂ E) (hr : ∀ n, Continuous (r.comp (P.incl n).toLinearMap)) :
      Continuous r := hlimit r fun n ↦ ((hr (n+1)).comp (hfc n)).congr
        (fun x ↦ congrArg r (hf n x))
  have hA (n : ℕ) : IsFrechetTVS (A n) := isFrechetTVS_closedSubmodule (hX _) _ (hClosed n)
  letI : IsClosed (F : Set E) := hF
  have hClosedImg (n : ℕ) : IsClosed (F.mkQ '' range (P.incl n)) := by
    change IsClosed (F.mkQ '' range (i n))
    rw [hImg]
    exact ((hY _).isClosedEmbedding _ (hEmbQ _)).isClosed_range
  have hpA (n : ℕ) : Continuous (p.comp (P.kernelStageInclusion F n).toLinearMap) := by
    let J := D.stageKernel F (a (2*n+1))
    let t : P.stageKernel F n →L[ℂ] J :=
      ((A n).subtypeL.comp (P.stageKernel F n).subtypeL).codRestrict J fun x ↦ x.property
    exact ((hp (a (2*n+1))).comp t.continuous).congr (fun _ ↦ rfl)
  obtain ⟨r, hr, he⟩ := P.kernel_seminorm_extension_of_closedStageImages F hF hA hi
    hClosedImg hP p hpA
  rw [← he]
  exact hr.comp continuous_subtype_val

/-- The canonical strict presentation of a kernel once the stagewise
seminorm test holds in the induced topology. -/
def kernelPresentation
    (hK : ∀ p : Seminorm ℂ F,
      (∀ n, Continuous (p.comp (D.kernelStageInclusion F n).toLinearMap)) → Continuous p) :
    LinearInductivePresentation F (fun n ↦ ↥(D.stageKernel F n)) where
  incl := D.kernelStageInclusion F
  transition {m n} h :=
    ((D.transition h).comp (D.stageKernel F m).subtypeL).codRestrict (D.stageKernel F n) (fun x ↦ by
      change D.incl n (D.transition h x.val) ∈ F
      rw [D.incl_transition]
      exact x.property)
  injective_incl n := fun _ _ h ↦ Subtype.ext (D.injective_incl n (congrArg Subtype.val h))
  incl_transition h x := Subtype.ext (D.incl_transition h x.val)
  exhaust x := by
    obtain ⟨n, y, hy⟩ := D.exhaust x.val
    have hyK : y ∈ D.stageKernel F n := by
      change D.incl n y ∈ F
      rw [hy]
      exact x.property
    exact ⟨n, ⟨y, hyK⟩, Subtype.ext hy⟩
  continuous_limit l := ⟨fun hl n ↦ hl.comp (D.kernelStageInclusion F n).continuous, fun hl ↦ by
    apply (PolynormableSpace.withSeminorms ℂ ℂ).continuous_of_continuous_comp
    intro p
    exact hK (p.val.comp l) (fun n ↦ p.property.comp (hl n))⟩

/-- Corollary C.1.5.13. For a closed subspace of a strict inductive limit of
nuclear Fréchet spaces, a strict Fréchet quotient implies bounded lifting and
the kernel is the strict locally convex limit of its nuclear Fréchet stages. -/
theorem strict_kernel_of_strictQuotient
    [PolynormableSpace ℂ E]
    (hF : IsClosed (F : Set E)) (Dq : LinearInductivePresentation (E ⧸ F) Y)
    (hX : ∀ n, IsFrechetTVS (X n)) (hN : ∀ n, NuclearLocallyConvex.{v, v} (X n))
    (hY : ∀ n, IsFrechetTVS (Y n))
    (hEmb : ∀ n, IsEmbedding (D.incl n)) (hEmbQ : ∀ n, IsEmbedding (Dq.incl n))
    (hlimit : ∀ r : Seminorm ℂ E,
      (∀ n, Continuous (r.comp (D.incl n).toLinearMap)) → Continuous r)
    (hlimitQ : ∀ r : Seminorm ℂ (E ⧸ F),
      (∀ n, Continuous (r.comp (Dq.incl n).toLinearMap)) → Continuous r) :
    (∀ B : Set (E ⧸ F), IsVonNBounded ℂ B →
      ∃ C : Set E, IsVonNBounded ℂ C ∧ F.mkQ '' C = B) ∧
    (inferInstance : TopologicalSpace F) =
      locallyConvexFinalTopology (fun n ↦ (D.kernelStageInclusion F n).toLinearMap) ∧
    ∃ K : LinearInductivePresentation F (fun n ↦ ↥(D.stageKernel F n)),
      (∀ n, K.incl n = D.kernelStageInclusion F n) ∧
      (∀ n, IsClosedEmbedding (K.transition (Nat.le_succ n))) ∧
      (∀ n, IsFrechetTVS (D.stageKernel F n) ∧ NuclearLocallyConvex.{v, v} (D.stageKernel F n)) := by
  letI : IsClosed (F : Set E) := hF
  letI : PolynormableSpace ℂ (E ⧸ F) := polynormableSpace_complex_quotient F
  have hk (n : ℕ) : IsFrechetTVS (D.stageKernel F n) :=
    isFrechetTVS_closedSubmodule (hX n) _ (hF.preimage (D.incl n).continuous)
  have hEmbTrQ (n : ℕ) : IsEmbedding (Dq.transition (Nat.le_succ n)) := by
    apply (hEmbQ (n+1)).of_comp_iff.mp
    exact (show (Dq.incl (n+1)) ∘ Dq.transition (Nat.le_succ n) = Dq.incl n from
      funext (Dq.incl_transition _)).symm ▸ hEmbQ n
  have hClosedTrQ (n : ℕ) : IsClosedEmbedding (Dq.transition (Nat.le_succ n)) := by
    obtain ⟨_, _, _, _⟩ := hY (n+1)
    exact (hY n).isClosedEmbedding _ (hEmbTrQ n)
  have hK := D.kernel_seminorm_continuous_of_strictQuotient F hF Dq hX hY hEmb hEmbQ hlimit
  let K := D.kernelPresentation F hK
  refine ⟨fun B hB ↦ D.quotient_liftsBounded_of_strict F hF Dq hX hN hY hClosedTrQ hEmbQ
    (fun T hT ↦ (PolynormableSpace.withSeminorms ℂ _).continuous_of_continuous_comp T
      (fun p ↦ hlimitQ (p.val.comp T) (fun n ↦ p.property.comp (hT n)))) hB,
    ?_, ⟨K, fun _ ↦ rfl, ?_, fun n ↦ ⟨hk n, nuclearLocallyConvex_submodule (hN n) _⟩⟩⟩
  · let i (n : ℕ) := (D.kernelStageInclusion F n).toLinearMap
    let t₀ : TopologicalSpace F := inferInstance
    let t : TopologicalSpace F := locallyConvexFinalTopology i
    letI : TopologicalSpace F := t₀
    apply le_antisymm
    · apply continuous_id_iff_le.mp
      change Continuous[t₀, t] (id : F → F)
      exact @WithSeminorms.continuous_of_continuous_comp ℂ ℂ F F (FinalSeminorm i)
        _ _ _ _ _ _ (RingHom.id ℂ) _ _ t₀ _ t (locallyConvexFinal_withSeminorms i)
        (LinearMap.id : F →ₗ[ℂ] F) (fun p ↦ hK p.val p.property)
    · apply continuous_id_iff_le.mp
      change Continuous[t, t₀] (id : F → F)
      have hAdd (n : ℕ) : IsTopologicalAddGroup (D.stageKernel F n) := (hk n).choose
      letI : ∀ n, IsTopologicalAddGroup (D.stageKernel F n) := hAdd
      exact (locallyConvexFinal_continuous_iff i (LinearMap.id : F →ₗ[ℂ] F)).mpr
        (fun n ↦ (D.kernelStageInclusion F n).continuous)
  · intro n
    have hi (k : ℕ) : IsEmbedding (K.incl k) := by
      apply IsEmbedding.subtypeVal.of_comp_iff.mp
      exact (hEmb k).comp IsEmbedding.subtypeVal
    have hemb : IsEmbedding (K.transition (Nat.le_succ n)) := by
      apply (hi (n+1)).of_comp_iff.mp
      exact (show (K.incl (n+1)) ∘ K.transition (Nat.le_succ n) = K.incl n from
        funext (K.incl_transition _)).symm ▸ hi n
    obtain ⟨_, _, _, _⟩ := hk (n+1)
    exact (hk n).isClosedEmbedding _ hemb

end LinearInductivePresentation

end

end Masullo
