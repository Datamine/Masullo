import ClassicalSchwartzNuclear
import AbsoluteBasisDuality
import PettisBounds
import NuclearApproximation

/-!
# Strong reflexivity of nuclear Fréchet spaces

The compact disk argument follows the Apache-2.0 original proof in
`RiemannMasullo/Ch02_AdelicTheta/Sec1.lean` at
`23cbb63d9a34c2ae8ab0ebd86074ea4c2a056978`.
-/

open Bornology Filter Function Set Topology UniformSpace
open scoped NNReal Pointwise SchwartzMap

namespace Masullo

noncomputable section

universe u

section StrongBidual

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

omit [PolynormableSpace ℂ E] [T2Space E] in
private theorem strongDual_bounded_seminorm [BarrelledSpace ℂ E]
    {S : Set (StrongDual ℂ E)} (hS : IsVonNBounded ℂ S) :
    ∃ p : Seminorm ℂ E, Continuous p ∧ ∀ f ∈ S, ∀ x, ‖f x‖ ≤ p x := by
  let f (i : S) : E →L[ℂ] ℂ := i.val
  have hb (x : E) : IsVonNBounded ℂ (range fun i : S ↦ f i x) := by
    have h := ContinuousLinearMap.isVonNBounded_image2_apply hS
      (isVonNBounded_singleton (𝕜 := ℂ) x)
    exact h.subset (by
      rintro _ ⟨i, rfl⟩
      exact mem_image2_of_mem i.property (mem_singleton x))
  have he := PolynormableSpace.banach_steinhaus (𝓕 := f) hb
  obtain ⟨p, hp, h⟩ :=
    ((norm_withSeminorms ℂ ℂ).uniformEquicontinuous_iff_exists_continuous_seminorm
      (fun i : S ↦ (f i).toLinearMap)).mp he 0
  exact ⟨p, hp, fun l hl x ↦ h ⟨l, hl⟩ x⟩

omit [PolynormableSpace ℂ E] [T2Space E] in
private theorem strongBidualEvaluation_continuous [BarrelledSpace ℂ E] :
    Continuous (strongBidualEvaluation (E := E)) := by
  apply strongDual_withBoundedSeminorms.continuous_of_continuous_comp
  intro B
  obtain ⟨p, hp, h⟩ := strongDual_bounded_seminorm B.property
  apply Seminorm.continuous_of_le hp
  intro x
  change strongDualBoundedSeminorm B (strongBidualEvaluation x) ≤ p x
  rw [strongDualBoundedSeminorm_apply]
  exact Real.iSup_le (fun f ↦ h f f.property x) (apply_nonneg p x)

omit [T2Space E] in
private theorem strongBidualEvaluation_surjective [CompleteSpace E]
    (hN : NuclearLocallyConvex.{u, u} E) : Surjective (strongBidualEvaluation (E := E)) := by
  letI : Module ℝ E := Module.restrictScalars ℝ ℂ E
  letI : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  letI : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  intro L
  have hU : L ⁻¹' Metric.closedBall 0 1 ∈ 𝓝 (0 : StrongDual ℂ E) :=
    L.continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact Metric.closedBall_mem_nhds _ zero_lt_one)
  obtain ⟨⟨B, r⟩, ⟨hB, hr⟩, ht⟩ :=
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall).mem_iff.mp hU
  let C := convexHull ℝ (Metric.closedBall (0 : ℂ) r⁻¹ • insert 0 B)
  have hC : Convex ℝ C := convex_convexHull ℝ _
  have hCB : IsCompact (Metric.closedBall (0 : ℂ) r⁻¹ • insert 0 (closure B)) := by
    rw [← Set.image2_smul, ← Set.image_prod]
    exact ((isCompact_closedBall _ _).prod
      ((nuclearLocallyConvex_totallyBounded hN hB).closure.isCompact_of_isClosed isClosed_closure |>.insert 0)).image
      (continuous_fst.smul continuous_snd)
  have hCK : IsCompact (closure C) := by
    apply hCB.totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure |>.of_isClosed_subset
      isClosed_closure
    apply closure_mono (convexHull_mono _)
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x, insert_subset_insert subset_closure hx, rfl⟩
  have hzero : (0 : E) ∈ C := subset_convexHull ℝ _
    ⟨0, Metric.mem_closedBall_self (inv_nonneg.mpr hr.le), 0, mem_insert _ _, zero_smul _ _⟩
  have hclosure : (L.toLinearMap : WeakAlgebraicBidual E) ∈ closure (weakBidualEval E '' C) := by
    apply weakBidual_mem_closure_of_le hC
    intro f t hf
    change (L f).re ≤ t
    have ht₀ : 0 < t := by simpa using hf 0 hzero
    have hfB (x : E) (hx : x ∈ B) : ‖f x‖ ≤ r * t := by
      obtain ⟨a, ha, he⟩ := Complex.exists_norm_mul_eq_self (f x)
      have ha₀ : a ≠ 0 := norm_ne_zero_iff.mp (ha ▸ one_ne_zero)
      let c : ℂ := (r : ℂ)⁻¹ * a⁻¹
      have hc : c ∈ Metric.closedBall (0 : ℂ) r⁻¹ := by
        rw [mem_closedBall_zero_iff]
        simp only [c, norm_mul, norm_inv, Complex.norm_of_nonneg hr.le, ha, inv_one, mul_one, le_rfl]
      have hxC : c • x ∈ C := subset_convexHull ℝ _ ⟨c, hc, x, mem_insert_of_mem _ hx, rfl⟩
      have hb := hf (c • x) hxC
      have he' : f (c • x) = ((r⁻¹ * ‖f x‖ : ℝ) : ℂ) := by
        rw [map_smul, smul_eq_mul]
        dsimp only [c]
        rw [mul_assoc]
        nth_rw 1 [← he]
        rw [← mul_assoc a⁻¹, inv_mul_cancel₀ ha₀, one_mul, Complex.ofReal_mul, Complex.ofReal_inv]
      rw [he', Complex.ofReal_re] at hb
      exact ((inv_mul_le_iff₀ hr).mp hb.le)
    have htest : (t : ℂ)⁻¹ • f ∈ L ⁻¹' Metric.closedBall 0 1 := by
      apply ht
      intro x hx
      rw [mem_closedBall_zero_iff, smul_apply, norm_smul, norm_inv,
        Complex.norm_of_nonneg ht₀.le, inv_mul_le_iff₀ ht₀]
      exact (hfB x hx).trans_eq (mul_comm _ _)
    change L ((t : ℂ)⁻¹ • f) ∈ Metric.closedBall 0 1 at htest
    rw [mem_closedBall_zero_iff, map_smul, norm_smul, norm_inv, Complex.norm_of_nonneg ht₀.le,
      inv_mul_le_iff₀ ht₀, mul_one] at htest
    exact (Complex.re_le_norm _).trans htest
  rw [← (weakBidual_convex_closure E hC).2 hCK] at hclosure
  obtain ⟨x, _, hx⟩ := hclosure
  refine ⟨x, ContinuousLinearMap.ext fun f ↦ ?_⟩
  exact DFunLike.congr_fun (F := Module.Dual ℂ (StrongDual ℂ E)) hx f

/-- Evaluation identifies a complete barrelled nuclear space with its strong bidual. -/
theorem strongBidual_equiv_of_nuclear [BarrelledSpace ℂ E] [CompleteSpace E]
    (hN : NuclearLocallyConvex.{u, u} E) :
    ∃ e : E ≃L[ℂ] StrongDual ℂ (StrongDual ℂ E), ∀ x f, e x f = f x := by
  let j := strongBidualEvaluation (E := E)
  have hj : Injective j := by
    intro x y hxy
    by_contra hn
    obtain ⟨p, hp⟩ := (PolynormableSpace.withSeminorms ℂ E).separating_of_T1 (x - y)
      (sub_ne_zero.mpr hn)
    obtain ⟨f, hf, _⟩ := seminorm_support p.val p.property (x - y)
    have he : f x = f y := DFunLike.congr_fun hxy f
    exact hp (by simpa [map_sub, he] using hf.symm)
  let e := LinearEquiv.ofBijective j ⟨hj, strongBidualEvaluation_surjective hN⟩
  refine ⟨⟨e, strongBidualEvaluation_continuous, ?_⟩, fun _ _ ↦ rfl⟩
  let W := PolynormableSpace.withSeminorms ℂ E
  change Continuous e.symm.toLinearMap
  refine (@WithSeminorms.continuous_of_continuous_comp ℂ ℂ (StrongDual ℂ (StrongDual ℂ E))
    E _ _ _ _ _ _ _ (RingHom.id ℂ) _ _ _ _ _ W e.symm.toLinearMap) ?_
  intro p
  let B : {B : Set (StrongDual ℂ E) // IsVonNBounded ℂ B} :=
    ⟨{f | ∀ x, ‖f x‖ ≤ p.val x}, strongDual_seminorm_test_bounded p.val p.property⟩
  have hB : Continuous (strongDualBoundedSeminorm B) :=
    strongDual_withBoundedSeminorms.continuous_seminorm B
  apply Seminorm.continuous_of_le hB
  intro L
  obtain ⟨f, hf, hdom⟩ := seminorm_support p.val p.property (e.symm L)
  have hmem : f ∈ B.val := hdom
  have hval : f (e.symm L) = L f := by
    exact DFunLike.congr_fun (e.apply_symm_apply L) f
  change p.val (e.symm L) ≤ strongDualBoundedSeminorm B L
  rw [← hf, hval, strongDualBoundedSeminorm_apply]
  have hbd : BddAbove (range fun g : B.val ↦ ‖L g‖) := by
    obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp (B.property.image L)
    exact ⟨C, forall_mem_range.mpr fun g ↦ hC _ ⟨g, g.property, rfl⟩⟩
  exact le_ciSup hbd (⟨f, hmem⟩ : B.val)

end StrongBidual

/-- Proposition 2.1.1.6. Evaluation gives the strong reflexivity of classical
complex Schwartz functions on a finite-dimensional real vector space. -/
theorem classicalSchwartz_reflexive (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    ∃ e : 𝓢(V, ℂ) ≃L[ℂ] StrongDual ℂ (StrongDual ℂ 𝓢(V, ℂ)), ∀ f L, e f L = L f := by
  let h := classicalSchwartz_nuclear.{u, u} V
  letI : PolynormableSpace ℂ 𝓢(V, ℂ) := h.2.1
  letI : BarrelledSpace ℂ 𝓢(V, ℂ) := isFrechetTVS_barrelled (classicalSchwartz_isFrechet V)
  letI : CompleteSpace 𝓢(V, ℂ) := completeSpace_schwartzMap
  exact strongBidual_equiv_of_nuclear h

/-- Proposition 2.1.1.6. The Euclidean Schwartz space is nuclear, Fréchet
and reflexive. Its strong dual is complete, nuclear and Montel. -/
theorem euclideanSchwartz_structure (m : ℕ) :
    let E := 𝓢(EuclideanSpace ℝ (Fin m), ℂ)
    NuclearLocallyConvex.{0, 0} E ∧ IsFrechetTVS E ∧
      (∃ e : E ≃L[ℂ] StrongDual ℂ (StrongDual ℂ E), ∀ x f, e x f = f x) ∧
      CompleteSpace (StrongDual ℂ E) ∧ NuclearLocallyConvex.{0, 0} (StrongDual ℂ E) ∧
      MontelSpace ℂ (StrongDual ℂ E) := by
  let V := EuclideanSpace ℝ (Fin m)
  exact ⟨classicalSchwartz_nuclear V, classicalSchwartz_isFrechet V, classicalSchwartz_reflexive V,
    classicalSchwartz_strongDual_complete V, classicalSchwartz_strongDual_nuclear V,
    classicalSchwartz_strongDual_montel V⟩

end

end Masullo
