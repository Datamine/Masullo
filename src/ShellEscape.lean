import AdelicBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LpSeminorm.Count

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical ContDiff ENNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev FinAdeles := FiniteAdeleRing (𝓞 F) F

private theorem exists_nonnegative_bruhat :
    ∃ (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : FiniteBruhat F),
      HasCompactSupport φ ∧ (∀ a, 0 ≤ (bruhatTensor F φ ψ a).re) ∧
      bruhatTensor F φ ψ 1 = 1 := by
  obtain ⟨u, _, huc, hu, hub, hu₁⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (s := univ) (x := (1 : mixedEmbedding.mixedSpace F)) univ_mem
  let v (x : mixedEmbedding.mixedSpace F) : ℂ := (u x : ℂ)
  have hvC : HasCompactSupport v := huc.comp_left Complex.ofReal_zero
  have hvD : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp hu
  let φ := hvC.toSchwartzMap hvD
  obtain ⟨S, hS, hSc, hS₁⟩ := finiteAdeles_exists_compactClopen_one (F := F)
  let ψ₀ (a : FinAdeles F) : ℂ := if a ∈ S then 1 else 0
  have hLoc : IsLocallyConstant ψ₀ := by
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro c
    by_cases hc₁ : c = 1
    · subst c
      have he : ψ₀ ⁻¹' ({1} : Set ℂ) = S := by
        ext a
        by_cases ha : a ∈ S <;> simp [ψ₀, ha]
      rw [he]
      exact hSc.2
    by_cases hc₀ : c = 0
    · subst c
      have he : ψ₀ ⁻¹' ({0} : Set ℂ) = Sᶜ := by
        ext a
        by_cases ha : a ∈ S <;> simp [ψ₀, ha]
      rw [he]
      exact hSc.1.isOpen_compl
    have he : ψ₀ ⁻¹' {c} = ∅ := by
      ext a
      by_cases ha : a ∈ S <;> simp [ψ₀, ha, ne_comm.mp hc₁, ne_comm.mp hc₀]
    rw [he]
    exact isOpen_empty
  have hC : HasCompactSupport ψ₀ := hS.of_isClosed_subset isClosed_closure
    (closure_minimal (fun a ha => by
      by_contra! hx
      exact ha (by simp [ψ₀, hx])) hSc.1)
  let ψ : FiniteBruhat F := ⟨⟨ψ₀, hLoc⟩, hC⟩
  refine ⟨φ, ψ, hvC, ?_, ?_⟩
  · intro a
    change 0 ≤ ((u (mixedArch a) : ℂ) * ψ₀ a.2).re
    by_cases ha : a.2 ∈ S
    · simpa [ψ₀, ha] using (hub (mem_range_self (mixedArch a))).1
    · simp [ψ₀, ha]
  · change (u (mixedArch (1 : Adeles F)) : ℂ) * ψ₀ 1 = 1
    simp [hu₁, ψ₀, hS₁]

private def scalingUnit (n : ℕ) : Fˣ :=
  Units.mk0 (n.succ : F) (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))

private theorem arch_nat_mul (n : ℕ) (a : Adeles F) :
    mixedArch (((principalIdele F (scalingUnit F n)).val) * a) =
      (n.succ : ℝ) • mixedArch a := by
  rw [map_mul]
  have h : (principalIdele F (scalingUnit F n)).val = (n.succ : Adeles F) :=
    map_natCast (algebraMap F (Adeles F)) n.succ
  rw [h, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

private def unitMulHomeomorph {R : Type*} [CommRing R] [TopologicalSpace R] [ContinuousMul R]
    (u : Rˣ) : R ≃ₜ R where
  toFun a := (u : R) * a
  invFun a := (↑u⁻¹ : R) * a
  left_inv a := by simp [← mul_assoc]
  right_inv a := by simp [← mul_assoc]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

private theorem dilation_bruhat (φ : 𝓢(mixedEmbedding.mixedSpace F, ℂ)) (ψ : FiniteBruhat F) (n : ℕ) :
    (fun a : Adeles F => bruhatTensor F φ ψ ((principalIdele F (scalingUnit F n)).val * a)) ∈
      bruhatSubmodule F := by
  let c := Units.mk0 (n.succ : ℝ) (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  let e : mixedEmbedding.mixedSpace F ≃L[ℝ] mixedEmbedding.mixedSpace F := (DistribMulAction.toLinearEquiv ℝ (mixedEmbedding.mixedSpace F) c).toContinuousLinearEquiv
  let h : FinAdeles F ≃ₜ FinAdeles F :=
    unitMulHomeomorph (Units.map (algebraMap F (FinAdeles F)) (scalingUnit F n))
  let χ : FiniteBruhat F :=
    ⟨LocallyConstant.comap ⟨h, h.continuous⟩ ψ.toLocallyConstant, ψ.compactSupport.comp_homeomorph h⟩
  convert bruhatTensor_mem F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) χ using 1
  funext a
  have ha := arch_nat_mul F n a
  change φ (mixedArch ((principalIdele F (scalingUnit F n)).val * a)) * _ =
    φ ((n.succ : ℝ) • mixedArch a) * _
  rw [ha]
  rfl

/-- Moving a fixed positive pure Bruhat test along principal ideles preserves
its orbit sum and its absolute orbit mass while converging to zero pointwise.
This is the defect in the limit claim of Proposition 11.1.1.2. -/
theorem adelicShell_escape :
    ∃ (f : ℕ → Adeles F → ℂ) (C : ℝ), 0 < C ∧
      (∀ n, f n ∈ bruhatSubmodule F) ∧
      (∀ g : Idele F, ∀ᶠ n in atTop, f n g.val = 0) ∧
      (∀ n, Summable (fun ξ : Fˣ => ‖thetaSummand F (f n) 1 ξ‖) ∧
        (∑' ξ : Fˣ, ‖thetaSummand F (f n) 1 ξ‖) = C ∧
        1 ≤ (thetaOnIdeles F (f n) 1).re) := by
  obtain ⟨φ, ψ, hc, hpos, hone⟩ := exists_nonnegative_bruhat F
  let a := bruhatTensor F φ ψ
  let f (n : ℕ) (x : Adeles F) := a ((principalIdele F (scalingUnit F n)).val * x)
  have hs : Summable (fun ξ : Fˣ => ‖thetaSummand F a 1 ξ‖) :=
    pure_theta_absolutely_summable φ ψ 1
  have h₁ : thetaSummand F a 1 (1 : Fˣ) = 1 := by simpa [thetaSummand] using hone
  let C : ℝ := ∑' ξ : Fˣ, ‖thetaSummand F a 1 ξ‖
  have hC : 1 ≤ C := by
    have hb := hs.le_tsum (1 : Fˣ) (fun ξ _ => norm_nonneg (thetaSummand F a 1 ξ))
    simpa [C, h₁] using hb
  refine ⟨f, C, zero_lt_one.trans_le hC, dilation_bruhat F φ ψ, ?_, ?_⟩
  · intro g
    obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).mp hc.isBounded
    have hne : mixedArch g.val ≠ 0 := by
      have hI : IsUnit (mixedArch g.val) := g.isUnit.map mixedArch
      exact hI.ne_zero
    have hg : Tendsto (fun n : ℕ => ‖(n.succ : ℝ) • mixedArch g.val‖) atTop atTop := by
      have hN (n : ℕ) : ‖(n.succ : ℝ)‖ = (n.succ : ℝ) :=
        Real.norm_of_nonneg (Nat.cast_nonneg n.succ)
      simp_rw [norm_smul, hN]
      have hT : Tendsto (fun n : ℕ => (n.succ : ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
      exact Filter.Tendsto.atTop_mul_const (norm_pos_iff.mpr hne) hT
    filter_upwards [hg.eventually_gt_atTop R] with n hn
    have h0 : φ ((n.succ : ℝ) • mixedArch g.val) = 0 := by
      by_contra hnz
      exact (not_lt_of_ge (hR _ (subset_closure hnz))) hn
    change φ (mixedArch ((principalIdele F (scalingUnit F n)).val * g.val)) * _ = 0
    rw [arch_nat_mul, h0, zero_mul]
  · intro n
    let e : Fˣ ≃ Fˣ := Equiv.mulLeft (scalingUnit F n)
    have hshift (ξ : Fˣ) : thetaSummand F (f n) 1 ξ = thetaSummand F a 1 (e ξ) := by
      simp [f, thetaSummand, e, map_mul, Units.val_mul]
    have hnr : Summable (fun ξ : Fˣ => (thetaSummand F a 1 ξ).re) :=
      Complex.reCLM.summable (hs.of_norm)
    have hgt := hnr.le_tsum (1 : Fˣ) (fun ξ _ => hpos ((principalIdele F ξ * 1).val))
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [hshift]
      exact (e.summable_iff.mpr hs : Summable ((fun ξ : Fˣ => ‖thetaSummand F a 1 ξ‖) ∘ e))
    · simp_rw [hshift]
      exact e.tsum_eq (fun ξ : Fˣ => ‖thetaSummand F a 1 ξ‖)
    · unfold thetaOnIdeles
      simp_rw [hshift]
      rw [Equiv.tsum_eq e _, Complex.re_tsum hs.of_norm]
      simpa only [h₁, Complex.one_re] using hgt

/-- On the Borel region `{1}` with its point mass, the escaped shells do
not converge in even the (L^1) norm, despite their pointwise zero limit
and uniform absolute orbit mass. -/
theorem adelicShell_escape_L1 [MeasurableSpace (Idele F)] [MeasurableSingletonClass (Idele F)] :
    ∃ (f : ℕ → Adeles F → ℂ) (C : ℝ), 0 < C ∧
      (∀ n, f n ∈ bruhatSubmodule F) ∧
      (∀ g : Idele F, Tendsto (fun n => f n g.val) atTop (𝓝 0)) ∧
      (∀ n, (∑' ξ : Fˣ, ‖thetaSummand F (f n) 1 ξ‖) = C) ∧
      ¬ Tendsto (fun n => eLpNorm (thetaOnIdeles F (f n)) 1
        ((Measure.dirac (1 : Idele F)).restrict {1})) atTop (𝓝 0) := by
  obtain ⟨f, C, hC, hf, hpoint, hmass⟩ := adelicShell_escape F
  refine ⟨f, C, hC, hf, fun g => tendsto_const_nhds.congr' ((hpoint g).mono fun _ h => h.symm),
    fun n => (hmass n).2.1, ?_⟩
  have hν : (Measure.dirac (1 : Idele F)).restrict {1} = Measure.dirac 1 := by
    simp [Measure.restrict_singleton]
  rw [hν]
  intro h
  have hB (n : ℕ) : (1 : ℝ≥0∞) ≤ eLpNorm (thetaOnIdeles F (f n)) 1 (Measure.dirac 1) := by
    rw [eLpNorm_dirac _ _ one_ne_zero, ← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((hmass n).2.2.trans (Complex.re_le_norm _))
  have hx : (1 : ℝ≥0∞) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds h (Eventually.of_forall hB)
  exact one_ne_zero (hx.antisymm zero_le)

end

end Masullo
