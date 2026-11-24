import StrictQuotientStages

open Filter Function Set Topology UniformSpace
open scoped Pointwise

namespace Masullo

noncomputable section

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

private def fiberInf (f : A →ₗ[ℂ] B) (p : Seminorm ℂ A) (y : B) : ℝ :=
  ⨅ x : {x : A // f x = y}, p x.1

private theorem fiberInf_le (f : A →ₗ[ℂ] B) (p : Seminorm ℂ A) (x : A) :
    fiberInf f p (f x) ≤ p x := by
  change (⨅ z : {z : A // f z = f x}, p z.1) ≤ p (⟨x, rfl⟩ : {z : A // f z = f x}).1
  apply ciInf_le
  exact ⟨0, by rintro _ ⟨z, rfl⟩; exact apply_nonneg p z.1⟩

private theorem le_fiberInf (f : A →ₗ[ℂ] B) (hf : Surjective f) (p : Seminorm ℂ A)
    {a : ℝ} {y : B} (h : ∀ x : A, f x = y → a ≤ p x) :
    a ≤ fiberInf f p y := by
  haveI : Nonempty {x : A // f x = y} := ⟨⟨(hf y).choose, (hf y).choose_spec⟩⟩
  exact le_ciInf fun x ↦ h x.1 x.2

/-- The infimum of a seminorm over the fibers of a linear surjection. -/
private def quotientSeminorm (f : A →ₗ[ℂ] B) (hf : Surjective f) (p : Seminorm ℂ A) :
    Seminorm ℂ B := by
  refine Seminorm.of (fiberInf f p) (fun y z ↦ ?_) (fun c y ↦ ?_)
  · apply sub_le_iff_le_add.mp
    apply le_fiberInf f hf p
    intro x hx
    apply sub_le_iff_le_add.mpr
    rw [add_comm (p x)]
    apply sub_le_iff_le_add.mp
    apply le_fiberInf f hf p
    intro w hw
    have he : f (x+w) = y+z := by rw [map_add, hx, hw]
    apply sub_le_iff_le_add.mpr
    rw [add_comm (p w)]
    exact (he ▸ fiberInf_le f p (x+w)).trans (map_add_le_add p x w)
  · obtain rfl | hc := eq_or_ne c 0
    · rw [zero_smul, norm_zero, zero_mul]
      exact le_antisymm (by simpa only [map_zero] using fiberInf_le f p (0 : A))
        (le_fiberInf f hf p fun x _ ↦ apply_nonneg p x)
    · change fiberInf f p (c • y) = ‖c‖ * fiberInf f p y
      unfold fiberInf
      rw [Real.mul_iInf_of_nonneg (norm_nonneg c)]
      let scale (x : {x : A // f x = y}) : {x : A // f x = c • y} :=
        ⟨c • x.1, by rw [map_smul, x.2]⟩
      symm
      refine Surjective.iInf_congr scale ?_ ?_
      · intro x
        refine ⟨⟨c⁻¹ • x.1, by rw [map_smul, x.2, inv_smul_smul₀ hc]⟩, ?_⟩
        exact Subtype.ext (smul_inv_smul₀ hc x.1)
      · intro x
        exact map_smul_eq_mul p c x.1

private theorem quotientSeminorm_le (f : A →ₗ[ℂ] B) (hf : Surjective f) (p : Seminorm ℂ A) (x : A) :
    quotientSeminorm f hf p (f x) ≤ p x := fiberInf_le f p x

private theorem le_quotientSeminorm (f : A →ₗ[ℂ] B) (hf : Surjective f) (p : Seminorm ℂ A)
    {b : ℝ} {y : B} (h : ∀ x : A, f x = y → b ≤ p x) :
    b ≤ quotientSeminorm f hf p y := le_fiberInf f hf p h

private theorem quotientSeminorm_continuous [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalAddGroup A] (f : A →ₗ[ℂ] B) (hf : IsQuotientMap f)
    (p : Seminorm ℂ A) (hp : Continuous p) : Continuous (quotientSeminorm f hf.surjective p) := by
  apply hf.continuous_iff.mpr
  change Continuous ((quotientSeminorm f hf.surjective p).comp f)
  exact Seminorm.continuous_of_le hp (quotientSeminorm_le f hf.surjective p)

/-- The pullback of the quotient seminorm vanishes on the submodule.
Its balls are the saturations of the original balls. -/
theorem exists_seminorm_thickening (p : Seminorm ℂ A) (S : Submodule ℂ A) :
    ∃ q : Seminorm ℂ A, q ≤ p ∧ (∀ x ∈ S, q x = 0) ∧
      ∀ r, q.ball 0 r = (S : Set A) + p.ball 0 r := by
  let pQ := quotientSeminorm S.mkQ S.mkQ_surjective p
  let q := pQ.comp S.mkQ
  have hle (x : A) : q x ≤ p x := quotientSeminorm_le S.mkQ S.mkQ_surjective p x
  refine ⟨q, hle, ?_, fun r ↦ ?_⟩
  · intro x hx
    change pQ (S.mkQ x) = 0
    have hz : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
    rw [hz, map_zero]
  · ext x
    rw [Seminorm.mem_ball_zero]
    constructor
    · intro hx
      have hex : ∃ z, S.mkQ z = S.mkQ x ∧ p z < r := by
        by_contra! hn
        exact hx.not_ge (le_quotientSeminorm S.mkQ S.mkQ_surjective p hn)
      obtain ⟨z, hz, hpz⟩ := hex
      have hxz : x - z ∈ S := (Submodule.Quotient.mk_eq_zero S).mp
        (by change S.mkQ (x-z) = 0; rw [map_sub, hz, sub_self])
      exact ⟨x-z, hxz, z, p.mem_ball_zero.mpr hpz, sub_add_cancel x z⟩
    · rintro ⟨s, hs, z, hz, rfl⟩
      have he : q (s+z) = q z := by
        change pQ (S.mkQ (s+z)) = pQ (S.mkQ z)
        have hs0 : S.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hs
        rw [map_add, hs0, zero_add]
      rw [he]
      exact (hle z).trans_lt (p.mem_ball_zero.mp hz)

/-- Compatible continuous seminorms on two closed subspaces of a Fréchet
space extend simultaneously when the sum of the subspaces is closed. -/
theorem exists_continuousSeminorm_glue {V : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] (hV : IsFrechetTVS V) (S T : Submodule ℂ V)
    (hS : IsClosed (S : Set V)) (hT : IsClosed (T : Set V))
    (hSum : IsClosed ((S ⊔ T : Submodule ℂ V) : Set V))
    (p : Seminorm ℂ S) (q : Seminorm ℂ T) (hp : Continuous p) (hq : Continuous q)
    (hcompat : ∀ x (hs : x ∈ S) (ht : x ∈ T), p ⟨x, hs⟩ = q ⟨x, ht⟩) :
    ∃ r : Seminorm ℂ V, Continuous r ∧ r.comp S.subtype = p ∧ r.comp T.subtype = q := by
  let U := S ⊔ T
  have ⟨hadd, hpoly, hmetric, hcomplete⟩ := hV
  letI : ContinuousSMul ℂ V := (PolynormableSpace.withSeminorms ℂ V).continuousSMul
  letI : UniformSpace V := IsTopologicalAddGroup.rightUniformSpace V
  letI : IsUniformAddGroup V := isUniformAddGroup_of_addCommGroup
  letI : CompleteSpace V := hcomplete
  letI : CompleteSpace S := hS.isComplete.completeSpace_coe
  letI : CompleteSpace T := hT.isComplete.completeSpace_coe
  letI : CompleteSpace U := hSum.isComplete.completeSpace_coe
  letI : IsUniformAddGroup S := S.toAddSubgroup.isUniformAddGroup
  letI : IsUniformAddGroup T := T.toAddSubgroup.isUniformAddGroup
  letI : IsUniformAddGroup U := U.toAddSubgroup.isUniformAddGroup
  letI : FirstCountableTopology S := IsInducing.subtypeVal.firstCountableTopology
  letI : FirstCountableTopology T := IsInducing.subtypeVal.firstCountableTopology
  letI : FirstCountableTopology U := IsInducing.subtypeVal.firstCountableTopology
  letI : (uniformity U).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace U := inferInstance
  let i : S →L[ℂ] U := S.subtypeL.codRestrict U (fun x ↦ (show S ≤ U from le_sup_left) x.property)
  let j : T →L[ℂ] U := T.subtypeL.codRestrict U (fun x ↦ (show T ≤ U from le_sup_right) x.property)
  let f : S × T →L[ℂ] U := i.coprod j
  have hf : Surjective f := by
    intro x
    obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp x.property
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext he⟩
  letI : @CompleteSpace (S × T) (IsTopologicalAddGroup.rightUniformSpace (S × T)) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  have hopen : IsOpenQuotientMap f :=
    ⟨hf, f.continuous, isOpenMap_of_surjective_complete_baire f hf⟩
  let hquot := hopen.isQuotientMap
  let pq := p.comp (LinearMap.fst ℂ S T) + q.comp (LinearMap.snd ℂ S T)
  let s := quotientSeminorm f.toLinearMap hquot.surjective pq
  have hsc : Continuous s := quotientSeminorm_continuous _ hquot pq
    ((hp.comp continuous_fst).add (hq.comp continuous_snd))
  have hsS (x : S) : s (i x) = p x := by
    apply le_antisymm
    · have h := quotientSeminorm_le f.toLinearMap hquot.surjective pq (x, 0)
      simpa [s, f, pq, add_apply] using h
    · apply le_quotientSeminorm
      rintro ⟨a, b⟩ he
      have hv : (a : V) + (b : V) = x := congrArg Subtype.val he
      have hbS : (b : V) ∈ S := by
        rw [show (b : V) = (x : V) - a by rw [← hv, add_sub_cancel_left]]
        exact S.sub_mem x.property a.property
      have hsum : a + (⟨b, hbS⟩ : S) = x := Subtype.ext hv
      calc
        p x = p (a + ⟨b, hbS⟩) := congrArg p hsum.symm
        _ ≤ p a + p ⟨b, hbS⟩ := map_add_le_add p _ _
        _ = pq (a, b) := by rw [hcompat b hbS b.property]; rfl
  have hsT (x : T) : s (j x) = q x := by
    apply le_antisymm
    · have h := quotientSeminorm_le f.toLinearMap hquot.surjective pq (0, x)
      simpa [s, f, pq, add_apply] using h
    · apply le_quotientSeminorm
      rintro ⟨a, b⟩ he
      have hv : (a : V) + (b : V) = x := congrArg Subtype.val he
      have haT : (a : V) ∈ T := by
        rw [show (a : V) = (x : V) - b by rw [← hv, add_sub_cancel_right]]
        exact T.sub_mem x.property b.property
      have hsum : (⟨a, haT⟩ : T) + b = x := Subtype.ext hv
      calc
        q x = q (⟨a, haT⟩ + b) := congrArg q hsum.symm
        _ ≤ q ⟨a, haT⟩ + q b := map_add_le_add q _ _
        _ = pq (a, b) := by rw [← hcompat a a.property haT]; rfl
  obtain ⟨r, hr, hru⟩ := exists_continuousSeminorm_extension U.subtypeL
    IsEmbedding.subtypeVal s hsc
  refine ⟨r, hr, ?_, ?_⟩
  · ext x
    exact (DFunLike.congr_fun hru (i x)).trans (hsS x)
  · ext x
    exact (DFunLike.congr_fun hru (j x)).trans (hsT x)

end

end Masullo
