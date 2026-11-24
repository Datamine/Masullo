import AdelicHomogeneousTheta
import AdelicFourierClosure

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Arch := mixedEmbedding.mixedSpace F
private abbrev Degree := Module.finrank ℚ F

private theorem radial_arch (t : Multiplicative ℝ) (a : Adeles F) :
    mixedArch ((ideleExpSection F t).val * a) =
      Real.exp (Multiplicative.toAdd t / Degree F) • mixedArch a := by
  rw [map_mul]
  change InfiniteAdeleRing.ringEquiv_mixedSpace F (ideleExpSection F t).val.1 * _ = _
  rw [ideleExpSection_mixed, smul_mul_assoc, one_mul]

private theorem radial_finite (t : Multiplicative ℝ) (g : Idele F) (ξ : Fˣ) :
    (principalIdele F ξ * (ideleExpSection F t * g)).val.2 =
      (principalIdele F ξ * g).val.2 := by
  change (principalIdele F ξ).val.2 * ((ideleExpSection F t).val.2 * g.val.2) = _
  rw [(ideleExpSection_components F t).2, one_mul]
  rfl

private theorem radial_scale_rpow (t : Multiplicative ℝ) (a : ℝ) :
    (Real.exp (Multiplicative.toAdd t / Degree F)) ^ ((Degree F : ℝ) * a) =
      Real.exp (Multiplicative.toAdd t * a) := by
  have hd : (Degree F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Module.finrank_pos (R := ℚ) (M := F)).ne'
  rw [← Real.exp_mul]
  congr 1
  field_simp

private def archGrowthSeminorm (m : ℕ) : Seminorm ℂ (𝓢(Arch F, ℂ)) :=
  SchwartzMap.seminorm ℂ 0 0 + SchwartzMap.seminorm ℂ m 0

private theorem archGrowthSeminorm_continuous (m : ℕ) : Continuous (archGrowthSeminorm F m) := by
  let h := schwartz_withSeminorms ℂ (Arch F) ℂ
  exact (h.continuous_seminorm (0, 0)).add (h.continuous_seminorm (m, 0))

private theorem archGrowthSeminorm_rpow_le (p : ℝ) (hp : 0 ≤ p) (φ : 𝓢(Arch F, ℂ))
    (x : Arch F) : ‖x‖ ^ p * ‖φ x‖ ≤ archGrowthSeminorm F ⌈p⌉₊ φ := by
  change _ ≤ SchwartzMap.seminorm ℂ 0 0 φ + SchwartzMap.seminorm ℂ ⌈p⌉₊ 0 φ
  rcases le_total ‖x‖ 1 with h | h
  · exact (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one (norm_nonneg _) h hp)).trans
      ((SchwartzMap.norm_le_seminorm ℂ φ x).trans (le_add_of_nonneg_right (apply_nonneg _ _)))
  · exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le h (Nat.le_ceil p)) (norm_nonneg _)).trans (by
      rw [Real.rpow_natCast]
      exact (SchwartzMap.norm_pow_mul_le_seminorm ℂ φ ⌈p⌉₊ x).trans
        (le_add_of_nonneg_left (apply_nonneg _ _)))

set_option maxHeartbeats 1600000 in
/-- The finite support and a compact family of base ideles give a weighted theta estimate controlled by an archimedean Schwartz seminorm.
The real exponent can approach one from above. -/
theorem pure_theta_radial_power_bound (ψ : FiniteBruhat F) {K : Set (Idele F)} (hK : IsCompact K)
    (a : ℝ) (ha : 1 < a) : ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (φ : 𝓢(Arch F, ℂ)) (t : Multiplicative ℝ), ∀ g ∈ K,
      Real.exp (Multiplicative.toAdd t * a) *
        (∑' ξ, ‖thetaSummand F (bruhatTensor F φ ψ) (ideleExpSection F t * g) ξ‖) ≤
        C * archGrowthSeminorm F m φ := by
  obtain ⟨d, hd, hclear⟩ := compact_idele_support_common_denominator hK ψ.compactSupport
  let dF := algebraMap (𝓞 F) F d
  have hdF : dF ≠ 0 := (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr hd
  let L := mixedEmbedding.integerLattice F
  let active : Set Fˣ := {ξ | ∃ g ∈ K, ψ.toLocallyConstant (principalIdele F ξ * g).val.2 ≠ 0}
  have hintegral (ξ : active) : dF * (ξ.val : F) ∈ (algebraMap (𝓞 F) F).range := by
    obtain ⟨g, hg, hn⟩ := ξ.property
    exact hclear g hg ξ.val (subset_closure hn)
  let j (ξ : active) : L := ⟨mixedEmbedding F (dF * (ξ.val : F)), by
    obtain ⟨a, ha⟩ := hintegral ξ
    exact ⟨a, congrArg (mixedEmbedding F) ha⟩⟩
  have hj : Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact mul_left_cancel₀ hdF (mixedEmbedding_injective F (congrArg Subtype.val hab))
  have hj₀ (ξ : active) : 0 < ‖j ξ‖ := by
    rw [norm_pos_iff]
    intro h
    have hz : mixedEmbedding F (dF * (ξ.val : F)) = 0 := congrArg Subtype.val h
    exact (mul_ne_zero hdF ξ.val.ne_zero)
      ((map_eq_zero_iff _ (mixedEmbedding_injective F)).mp hz)
  have hArch : Continuous (mixedArch (F := F)) :=
    (infiniteAdele_toMixed_continuous F).comp continuous_fst
  have hInv : Continuous (fun g : Idele F => mixedArch g.inv) :=
    hArch.comp Units.continuous_coe_inv
  obtain ⟨R, hR, hRbound⟩ := (hK.image hInv).isBounded.exists_pos_norm_le
  obtain ⟨M, hM, hψ⟩ := norm_finiteBruhat_bounded ψ
  let A := ‖mixedEmbedding F dF‖ * R
  let p : ℝ := (Degree F : ℝ) * a
  have hd0 : 0 < (Degree F : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hp : 0 ≤ p := mul_nonneg hd0.le (zero_lt_one.trans ha).le
  have hRank : Module.finrank ℤ L = Degree F := by
    rw [ZLattice.rank ℝ L, mixedEmbedding.finrank]
  have hpRank : (Module.finrank ℤ L : ℝ) < p := by
    rw [hRank]
    exact lt_mul_of_one_lt_right hd0 ha
  let w (ξ : active) := ‖j ξ‖ ^ (-p)
  have hw : Summable w := (ZLattice.summable_norm_rpow L (-p) (by linarith)).comp_injective hj
  have hw₀ (ξ : active) : 0 ≤ w ξ := Real.rpow_nonneg (norm_nonneg _) _
  refine ⟨⌈p⌉₊, M * A ^ p * (∑' ξ, w ξ), by
    exact mul_nonneg (by dsimp [A]; positivity) (tsum_nonneg hw₀), ?_⟩
  intro φ t g hg
  let scale := Real.exp (Multiplicative.toAdd t / Degree F)
  let E := Real.exp (Multiplicative.toAdd t * a)
  have hscale : 0 < scale := Real.exp_pos _
  have hE : scale ^ p = E := radial_scale_rpow F t a
  let W := active.indicator (fun ξ => if h : ξ ∈ active then w ⟨ξ, h⟩ else 0)
  have hW : Summable W := by
    apply (summable_subtype_iff_indicator (s := active)).mp
    exact hw.congr fun ξ => by simp [ξ.property]
  let f := bruhatTensor F φ ψ
  have hsum := (adelicThetaNorm_summable F (bruhatTensor_mem F φ ψ) (ideleExpSection F t * g)).mul_left E
  let C := M * A ^ p * archGrowthSeminorm F ⌈p⌉₊ φ
  have hle (ξ : Fˣ) : E * ‖thetaSummand F f (ideleExpSection F t * g) ξ‖ ≤ C * W ξ := by
    by_cases hξ : ξ ∈ active
    · let b := (principalIdele F ξ * g).val
      let z := mixedArch b
      have hbase : mixedEmbedding F (ξ : F) = mixedArch g.inv * z := by
        change mixedEmbedding F (ξ : F) = mixedArch g.inv *
          mixedArch (algebraMap F (Adeles F) (ξ : F) * g.val)
        rw [← map_mul, mul_left_comm, g.inv_val, mul_one, mixedArch_on_diagonal]
      have hJ : ‖j ⟨ξ, hξ⟩‖ ≤ A * ‖z‖ := by
        change ‖mixedEmbedding F (dF * (ξ : F))‖ ≤ _
        rw [map_mul, hbase]
        calc
          _ ≤ ‖mixedEmbedding F dF‖ * ‖mixedArch g.inv * z‖ := norm_mul_le _ _
          _ ≤ ‖mixedEmbedding F dF‖ * (R * ‖z‖) :=
            mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (hRbound _ ⟨g, hg, rfl⟩) (norm_nonneg _))) (norm_nonneg _)
          _ = _ := by rw [mul_assoc]
      have hφ : E * ‖φ (scale • z)‖ * ‖j ⟨ξ, hξ⟩‖ ^ p ≤
          A ^ p * archGrowthSeminorm F ⌈p⌉₊ φ := by
        calc
          _ ≤ (scale ^ p * ‖φ (scale • z)‖) * (A * ‖z‖) ^ p := by
            rw [hE]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (norm_nonneg _) hJ hp) (by positivity)
          _ = A ^ p * (‖scale • z‖ ^ p * ‖φ (scale • z)‖) := by
            have hA : 0 ≤ A := by dsimp [A]; positivity
            rw [norm_smul, Real.norm_of_nonneg hscale.le,
              Real.mul_rpow hA (norm_nonneg _), Real.mul_rpow hscale.le (norm_nonneg _)]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (archGrowthSeminorm_rpow_le F p hp φ _) (by dsimp [A]; positivity)
      have hpoint : mixedArch (principalIdele F ξ * (ideleExpSection F t * g)).val = scale • z := by
        rw [mul_left_comm, Units.val_mul, radial_arch]
      have hφ' : E * ‖φ (scale • z)‖ ≤ (A ^ p * archGrowthSeminorm F ⌈p⌉₊ φ) * w ⟨ξ, hξ⟩ := by
        change _ ≤ _ * (‖j ⟨ξ, hξ⟩‖ ^ (-p))
        rw [Real.rpow_neg (hj₀ ⟨ξ, hξ⟩).le, ← div_eq_mul_inv]
        exact (le_div_iff₀ (Real.rpow_pos_of_pos (hj₀ _) _)).mpr hφ
      change E * ‖φ (mixedArch (principalIdele F ξ * (ideleExpSection F t * g)).val) *
        ψ.toLocallyConstant (principalIdele F ξ * (ideleExpSection F t * g)).val.2‖ ≤ _
      rw [hpoint, radial_finite, norm_mul, ← mul_assoc]
      have hWξ : W ξ = w ⟨ξ, hξ⟩ := by simp [W, hξ]
      rw [hWξ]
      calc
        _ ≤ ((A ^ p * archGrowthSeminorm F ⌈p⌉₊ φ) * w ⟨ξ, hξ⟩) * M :=
          mul_le_mul hφ' (hψ _) (norm_nonneg _) (by dsimp [A]; positivity)
        _ = C * w ⟨ξ, hξ⟩ := by dsimp [C]; ring
    · have hz : ψ.toLocallyConstant (principalIdele F ξ * g).val.2 = 0 := by
        by_contra hn
        exact hξ ⟨g, hg, hn⟩
      change E * ‖φ (mixedArch (principalIdele F ξ * (ideleExpSection F t * g)).val) *
        ψ.toLocallyConstant (principalIdele F ξ * (ideleExpSection F t * g)).val.2‖ ≤ _
      rw [radial_finite, hz, mul_zero, norm_zero, mul_zero]
      simp [W, hξ]
  have hWt : (∑' ξ, W ξ) = ∑' ξ, w ξ := by
    rw [← tsum_subtype]
    exact tsum_congr fun ξ => by simp [ξ.property]
  calc
    _ = ∑' ξ, E * ‖thetaSummand F f (ideleExpSection F t * g) ξ‖ := (tsum_mul_left).symm
    _ ≤ ∑' ξ, C * W ξ := hsum.tsum_le_tsum hle (hW.mul_left C)
    _ = _ := by rw [tsum_mul_left, hWt]; dsimp [C]; ring


/-- The sum of absolute values of the nonzero adelic theta terms on the
actual idele class group. -/
def adelicThetaAbs (f : Adeles F → ℂ) : IdeleClass F → ℝ :=
  Quotient.lift (fun g => ∑' ξ, ‖thetaSummand F f g ξ‖) (fun x y h => by
    change (QuotientGroup.leftRel (principalIdeles F)).r x y at h
    rw [QuotientGroup.leftRel_apply] at h
    obtain ⟨a, ha⟩ := h
    have hy : y = principalIdele F a * x := by rw [ha, mul_comm (x⁻¹ * y), mul_inv_cancel_left]
    rw [hy]
    simpa only [thetaSummand, Equiv.coe_mulRight, map_mul, mul_assoc] using
      ((Equiv.mulRight a).tsum_eq (fun ξ => ‖thetaSummand F f x ξ‖)).symm)

@[simp] theorem adelicThetaAbs_mk (f : Adeles F → ℂ) (g : Idele F) :
    adelicThetaAbs F f (ideleClassMap F g) = ∑' ξ, ‖thetaSummand F f g ξ‖ := rfl

theorem adelicThetaAbs_continuous {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F) :
    Continuous (adelicThetaAbs F f) :=
  QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp (adelicThetaNorm_continuous F hf)

theorem norm_adelicTheta_le_abs {f : Adeles F → ℂ} (hf : f ∈ bruhatSubmodule F)
    (q : IdeleClass F) : ‖adelicTheta F f q‖ ≤ adelicThetaAbs F f q := by
  obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
  exact norm_tsum_le_tsum_norm (adelicThetaNorm_summable F hf g)

private theorem pure_theta_power_class (ψ : FiniteBruhat F) (σ : ℝ) (hσ : 1 < σ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : 𝓢(Arch F, ℂ)) (q : IdeleClass F),
        ideleClassNorm F q ^ σ * adelicThetaAbs F (bruhatTensor F φ ψ) q ≤
          C * archGrowthSeminorm F m φ := by
  let v : InfinitePlace F := Classical.choice inferInstance
  choose r hr using ideleNormOne_idealClass_surjective F
  let D := ideleFundamentalDomain F v r
  let K : Set (Idele F) := Subtype.val '' closure D
  have hK : IsCompact K :=
    (ideleFundamentalDomain_topology F v r).1.image continuous_subtype_val
  obtain ⟨m, C, hC, hb⟩ := pure_theta_radial_power_bound F ψ hK σ hσ
  refine ⟨m, C, hC, fun φ q => ?_⟩
  let t := ideleClassLogNorm F q
  have ht : Real.exp (Multiplicative.toAdd t * σ) = ideleClassNorm F q ^ σ :=
    (Real.rpow_def_of_pos (ideleClassNorm_pos F q) σ).symm
  obtain ⟨a, ha⟩ := (normOneIdelesToClasses_openQuotient F).surjective (ideleClassNormOnePart F q)
  obtain ⟨b, hb', _⟩ := ideleFundamentalDomain_unique F v r hr a
  let g := principalNormOne F b * a
  have hg : g.val ∈ K := ⟨g, subset_closure hb', rfl⟩
  have hp : ideleClassMap F (principalIdele F b) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨b, rfl⟩
  have hga : ideleClassMap F g.val = (ideleClassNormOnePart F q).val := by
    change ideleClassMap F (principalIdele F b * a.val) = _
    rw [map_mul, hp]
    exact (one_mul (ideleClassMap F a.val)).trans (congrArg Subtype.val ha)
  have hrep : ideleClassMap F (ideleExpSection F t * g.val) = q := by
    rw [map_mul, hga]
    exact (mul_comm (ideleClassMap F (ideleExpSection F t)) (ideleClassNormOnePart F q).val).trans
      ((ideleClassSplit F).symm_apply_apply q)
  simpa only [ht, ← adelicThetaAbs_mk F, hrep] using hb φ t g.val hg

private def thetaAbsSeminorm (q : IdeleClass F) : Seminorm ℂ (GlobalBruhat F) := by
  let v (f : GlobalBruhat F) := (GlobalBruhat.algebraicEquiv F f).val
  refine Seminorm.of (fun f => adelicThetaAbs F (v f) q) (fun f h => ?_) (fun c f => ?_)
  · obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
    have hf := adelicThetaNorm_summable F (GlobalBruhat.algebraicEquiv F f).property g
    have hh := adelicThetaNorm_summable F (GlobalBruhat.algebraicEquiv F h).property g
    have hsum := adelicThetaNorm_summable F (GlobalBruhat.algebraicEquiv F (f + h)).property g
    simp only [adelicThetaAbs_mk]
    change _ ≤ (∑' ξ, ‖thetaSummand F (GlobalBruhat.algebraicEquiv F f).val g ξ‖) +
      ∑' ξ, ‖thetaSummand F (GlobalBruhat.algebraicEquiv F h).val g ξ‖
    rw [← hf.tsum_add hh]
    refine hsum.tsum_le_tsum (fun ξ => ?_) (hf.add hh)
    change ‖thetaSummand F (v (f + h)) g ξ‖ ≤ _
    simpa only [v, map_add, thetaSummand, Submodule.coe_add, Pi.add_apply] using
      norm_add_le (v f (principalIdele F ξ * g).val) (v h (principalIdele F ξ * g).val)
  · obtain ⟨g, rfl⟩ := ideleClassMap_surjective F q
    simp only [adelicThetaAbs_mk, v, map_smul, Submodule.coe_smul_of_tower, thetaSummand,
      Pi.smul_apply, smul_eq_mul, norm_mul, tsum_mul_left]

private def thetaPowerWeight (σ : ℝ) (q : IdeleClass F) : ℝ≥0 :=
  ⟨ideleClassNorm F q ^ σ, Real.rpow_nonneg (ideleClassNorm_pos F q).le σ⟩

private def thetaPowerFamily (σ : ℝ) (q : IdeleClass F) : Seminorm ℂ (GlobalBruhat F) :=
  thetaPowerWeight F σ q • thetaAbsSeminorm F q

private theorem thetaPowerFamily_pure_bound (ψ : FiniteBruhat F) (σ : ℝ) (hσ : 1 < σ) :
    ∃ m : ℕ, ∃ C : ℝ≥0, ∀ (φ : 𝓢(Arch F, ℂ)) (q : IdeleClass F),
      thetaPowerFamily F σ q (GlobalBruhat.pure F ψ φ) ≤
        (C : ℝ) * archGrowthSeminorm F m φ := by
  obtain ⟨m, C, hC, h⟩ := pure_theta_power_class F ψ σ hσ
  exact ⟨m, ⟨C, hC⟩, h⟩

private theorem thetaPowerFamily_bounded (σ : ℝ) (hσ : 1 < σ) :
    BddAbove (range (thetaPowerFamily F σ)) := by
  apply Seminorm.bddAbove_range_iff.mpr
  intro f
  let e := GlobalBruhat.algebraicEquiv F
  have hspan (u : Adeles F → ℂ) (hu : u ∈ bruhatSubmodule F) :
      BddAbove (range (fun q => thetaPowerFamily F σ q (e.symm ⟨u, hu⟩))) := by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨φ, ψ, rfl⟩ := hu
      obtain ⟨m, C, h⟩ := thetaPowerFamily_pure_bound F ψ σ hσ
      exact ⟨(C : ℝ) * archGrowthSeminorm F m φ, forall_mem_range.mpr (h φ)⟩
    | zero =>
      exact ⟨0, forall_mem_range.mpr fun q => by
        change thetaPowerFamily F σ q (e.symm 0) ≤ 0
        rw [map_zero, map_zero]⟩
    | add u v hu hv ihu ihv =>
      obtain ⟨A, hA⟩ := ihu
      obtain ⟨B, hB⟩ := ihv
      refine ⟨A + B, forall_mem_range.mpr fun q => ?_⟩
      change thetaPowerFamily F σ q (e.symm (⟨u, hu⟩ + ⟨v, hv⟩)) ≤ _
      rw [map_add]
      exact (map_add_le_add _ _ _).trans
        (add_le_add (hA (mem_range_self q)) (hB (mem_range_self q)))
    | smul c u hu ihu =>
      obtain ⟨A, hA⟩ := ihu
      refine ⟨‖c‖ * A, forall_mem_range.mpr fun q => ?_⟩
      change thetaPowerFamily F σ q (e.symm (c • ⟨u, hu⟩)) ≤ _
      rw [map_smul, map_smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hA (mem_range_self q)) (norm_nonneg _)
  have h := hspan (e f).val (e f).property
  change BddAbove (range (fun q => thetaPowerFamily F σ q (e.symm (e f)))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- A single continuous seminorm on the actual Schwartz–Bruhat space controls
each prescribed power of the modulus times the full absolute orbit sum. -/
theorem adelicTheta_power_seminorm (σ : ℝ) (hσ : 1 < σ) :
    ∃ p : Seminorm ℂ (GlobalBruhat F), Continuous p ∧
      ∀ f : GlobalBruhat F, ∀ q : IdeleClass F,
        ideleClassNorm F q ^ σ * adelicThetaAbs F (GlobalBruhat.algebraicEquiv F f).val q ≤ p f := by
  let p := ⨆ q, thetaPowerFamily F σ q
  have hb := thetaPowerFamily_bounded F σ hσ
  refine ⟨p, GlobalBruhat.continuous_seminorm_of_pure F p ?_, fun f q => ?_⟩
  · intro ψ
    obtain ⟨m, C, h⟩ := thetaPowerFamily_pure_bound F ψ σ hσ
    let r : Seminorm ℂ (𝓢(Arch F, ℂ)) := C • archGrowthSeminorm F m
    have hr : Continuous r := continuous_const.mul (archGrowthSeminorm_continuous F m)
    apply Seminorm.continuous_of_le (p := p.comp (GlobalBruhat.pure F ψ)) hr
    intro φ
    change p (GlobalBruhat.pure F ψ φ) ≤ (C : ℝ) * archGrowthSeminorm F m φ
    rw [Seminorm.iSup_apply hb]
    exact ciSup_le (h φ)
  · exact (le_ciSup hb q) f

/-- Any power of the modulus with exponent strictly above one controls
the full absolute orbit sum at every modulus, uniformly on bounded families. -/
theorem adelicTheta_power_bounded (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B)
    (σ : ℝ) (hσ : 1 < σ) : ∃ C : ℝ, 0 < C ∧
      ∀ f ∈ B, ∀ q : IdeleClass F,
        ideleClassNorm F q ^ σ * adelicThetaAbs F (GlobalBruhat.algebraicEquiv F f).val q ≤ C := by
  obtain ⟨p, hp, h⟩ := adelicTheta_power_seminorm F σ hσ
  obtain ⟨C, hC, hCbound⟩ := (PolynormableSpace.withSeminorms ℂ (GlobalBruhat F))
    |>.isVonNBounded_iff_seminorm_bounded.mp hB ⟨p, hp⟩
  exact ⟨C, hC, fun f hf q => (h f q).trans (hCbound f hf).le⟩

/-- The large-modulus estimate in Theorem 2.2.3.4 holds for every bounded
family, including for the full sum of absolute values. -/
theorem adelicTheta_largeNorm_bounded (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B)
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ f ∈ B, ∀ q : IdeleClass F, 1 ≤ ideleClassNorm F q →
        ideleClassNorm F q ^ N * adelicThetaAbs F (GlobalBruhat.algebraicEquiv F f).val q ≤ C := by
  have hN : 1 < (N : ℝ) + 2 := by
    have h : 0 ≤ (N : ℝ) := by positivity
    linarith
  obtain ⟨C, hC, h⟩ := adelicTheta_power_bounded F B hB ((N : ℝ) + 2) hN
  refine ⟨C, hC, fun f hf q hq => ?_⟩
  refine le_trans ?_ (h f hf q)
  have hw : ideleClassNorm F q ^ N ≤ ideleClassNorm F q ^ ((N : ℝ) + 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  exact mul_le_mul_of_nonneg_right hw (apply_nonneg (thetaAbsSeminorm F q) f)

/-- The three theta decay estimates of Theorem 2.2.3.4, uniformly on bounded
families with modulus threshold one. The two-sided estimate uses the tests
whose two zero terms vanish. -/
theorem adelicTheta_decay_bounded (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B)
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ q : IdeleClass F,
      let u := (GlobalBruhat.algebraicEquiv F f).val
      let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
      let m := ideleClassNorm F q
      (1 ≤ m → ‖adelicTheta F u q‖ ≤ C * (m ^ N)⁻¹) ∧
      (m ≤ 1 → ‖adelicTheta F u q - m⁻¹ • v 0 + u 0‖ ≤ C * m ^ N) ∧
      (u 0 = 0 → v 0 = 0 → ‖adelicTheta F u q‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log m|)) := by
  let T := GlobalBruhat.fourier F
  obtain ⟨L, hL, hLarge⟩ := adelicTheta_largeNorm_bounded F B hB N
  obtain ⟨S, hS, hSmall⟩ := adelicTheta_largeNorm_bounded F (T '' B)
    (hB.image T) (N + 1)
  refine ⟨max L S, hL.trans_le (le_max_left _ _), fun f hf q => ?_⟩
  dsimp only
  let u := GlobalBruhat.algebraicEquiv F f
  let v := GlobalBruhat.algebraicEquiv F (T f)
  let m := ideleClassNorm F q
  have hm : 0 < m := ideleClassNorm_pos F q
  have hlarge (hq : 1 ≤ m) : ‖adelicTheta F u.val q‖ ≤ max L S * (m ^ N)⁻¹ := by
    have hp : 0 < m ^ N := pow_pos hm _
    have hh : m ^ N * ‖adelicTheta F u.val q‖ ≤ max L S :=
      (mul_le_mul_of_nonneg_left (norm_adelicTheta_le_abs F u.property q) hp.le).trans
        ((hLarge f hf q hq).trans (le_max_left _ _))
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
  have hsmall (hq : m ≤ 1) :
      ‖adelicTheta F u.val q - m⁻¹ • v.val 0 + u.val 0‖ ≤ max L S * m ^ N := by
    have hi : 1 ≤ ideleClassNorm F q⁻¹ := by
      rw [map_inv]
      exact (one_le_inv₀ hm).mpr hq
    have hz : adelicTheta F u.val q - m⁻¹ • v.val 0 + u.val 0 =
        m⁻¹ • adelicTheta F v.val q⁻¹ := by
      have he := congrFun (adelicTheta_riemannRoch F u.property).2 q
      rw [← GlobalBruhat.fourier_apply F f] at he
      change adelicTheta F u.val q = m⁻¹ • adelicTheta F v.val q⁻¹ +
        m⁻¹ • v.val 0 - u.val 0 at he
      rw [he]
      abel
    rw [hz, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hm.le)]
    have Hp : 0 < m⁻¹ ^ (N + 1) := pow_pos (inv_pos.mpr hm) _
    have hh : ideleClassNorm F q⁻¹ ^ (N + 1) * ‖adelicTheta F v.val q⁻¹‖ ≤ max L S :=
      (mul_le_mul_of_nonneg_left (norm_adelicTheta_le_abs F v.property q⁻¹)
        (pow_nonneg (le_of_lt (ideleClassNorm_pos F q⁻¹)) _)).trans
        ((hSmall (T f) (mem_image_of_mem T hf) q⁻¹ hi).trans (le_max_right L S))
    rw [map_inv] at hh
    have hh' : ‖adelicTheta F v.val q⁻¹‖ ≤ max L S * m ^ (N + 1) := by
      have hd : ‖adelicTheta F v.val q⁻¹‖ ≤ max L S / (m⁻¹ ^ (N + 1)) := by
        apply (le_div_iff₀ Hp).mpr
        rw [mul_comm]
        exact hh
      simpa only [div_eq_mul_inv, inv_pow, inv_inv] using hd
    calc
      _ ≤ m⁻¹ * (max L S * m ^ (N + 1)) := mul_le_mul_of_nonneg_left hh' (inv_nonneg.mpr hm.le)
      _ = max L S * m ^ N := by
        rw [pow_succ]
        calc
          _ = (m⁻¹ * m) * (max L S * m ^ N) := by ring
          _ = _ := by rw [inv_mul_cancel₀ hm.ne', one_mul]
  refine ⟨hlarge, hsmall, fun hu hv => ?_⟩
  change u.val 0 = 0 at hu
  change v.val 0 = 0 at hv
  rcases le_total 1 m with hm' | hm'
  · have he : Real.exp (-(N : ℝ) * |Real.log m|) = (m ^ N)⁻¹ := by
      rw [abs_of_nonneg (Real.log_nonneg hm'), neg_mul, Real.exp_neg, Real.exp_nat_mul,
        Real.exp_log hm]
    rw [he]
    exact hlarge hm'
  · have he : Real.exp (-(N : ℝ) * |Real.log m|) = m ^ N := by
      rw [abs_of_nonpos (Real.log_nonpos hm.le hm'), neg_mul_neg, Real.exp_nat_mul, Real.exp_log hm]
    rw [he]
    simpa only [hv, hu, smul_zero, sub_zero, add_zero] using hsmall hm'

/-- The pointwise decay estimates follow by specializing the bounded-family
version to a singleton, with the same modulus threshold one. -/
theorem adelicTheta_decay (f : GlobalBruhat F) (N : ℕ) :
    let u := (GlobalBruhat.algebraicEquiv F f).val
    let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
    Continuous (adelicTheta F u) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ q : IdeleClass F,
        let m := ideleClassNorm F q
        (1 ≤ m → ‖adelicTheta F u q‖ ≤ C * (m ^ N)⁻¹) ∧
        (m ≤ 1 → ‖adelicTheta F u q - m⁻¹ • v 0 + u 0‖ ≤ C * m ^ N) ∧
        (u 0 = 0 → v 0 = 0 → ‖adelicTheta F u q‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log m|)) := by
  obtain ⟨C, hC, h⟩ := adelicTheta_decay_bounded F {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f) N
  exact ⟨(adelicTheta_riemannRoch F (GlobalBruhat.algebraicEquiv F f).property).1,
    C, hC, h f (mem_singleton _)⟩

/-- Every closed strip strictly to the right of one has a common integrable
logarithmic envelope for the weighted absolute theta sum. -/
theorem adelicTheta_zeta_strip_seminorm (a b : ℝ)
    (ha : 1 < a) (hab : a ≤ b) :
    ∃ (p : Seminorm ℂ (GlobalBruhat F)) (c : ℝ), Continuous p ∧ 0 < c ∧
      ∀ (f : GlobalBruhat F) (q : IdeleClass F) (σ : ℝ), a ≤ σ → σ ≤ b →
        ideleClassNorm F q ^ σ * adelicThetaAbs F (GlobalBruhat.algebraicEquiv F f).val q ≤
          p f * Real.exp (-c * |Real.log (ideleClassNorm F q)|) := by
  let l := (a + 1) / 2
  let h := b + 1
  let c := min (a - l) (h - b)
  have hl : 1 < l := by dsimp [l]; linarith
  have hh : 1 < h := by dsimp [h]; linarith
  have hc : 0 < c := lt_min (by dsimp [l]; linarith) (by dsimp [h]; linarith)
  obtain ⟨p, hpC, hp⟩ := adelicTheta_power_seminorm F l hl
  obtain ⟨r, hrC, hr⟩ := adelicTheta_power_seminorm F h hh
  refine ⟨p + r, c, hpC.add hrC, hc, fun f q σ hσa hσb => ?_⟩
  let C := p f + r f
  change _ ≤ C * _
  let v := Real.log (ideleClassNorm F q)
  let W := adelicThetaAbs F (GlobalBruhat.algebraicEquiv F f).val q
  have hpos := ideleClassNorm_pos F q
  have hrescale (u : ℝ) :
      ideleClassNorm F q ^ σ * W =
        Real.exp ((σ - u) * v) * (ideleClassNorm F q ^ u * W) := by
    rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hpos, ← mul_assoc, ← Real.exp_add]
    change Real.exp (v * σ) * W = Real.exp ((σ - u) * v + v * u) * W
    congr 2
    ring
  rcases le_total v 0 with hv | hv
  · change _ ≤ C * Real.exp (-c * |v|)
    rw [hrescale l, abs_of_nonpos hv, neg_mul_neg, mul_comm C]
    have hbound : ideleClassNorm F q ^ l * W ≤ C :=
      (hp f q).trans (le_add_of_nonneg_right (apply_nonneg r f))
    apply mul_le_mul _ hbound
      (mul_nonneg (Real.rpow_nonneg hpos.le _) (apply_nonneg (thetaAbsSeminorm F q) f)) (Real.exp_nonneg _)
    apply Real.exp_le_exp.mpr
    have hcv : c ≤ σ - l := (min_le_left (a - l) (h - b)).trans (by linarith)
    exact mul_le_mul_of_nonpos_right hcv hv
  · change _ ≤ C * Real.exp (-c * |v|)
    rw [hrescale h, abs_of_nonneg hv, mul_comm C]
    have hbound : ideleClassNorm F q ^ h * W ≤ C :=
      (hr f q).trans (le_add_of_nonneg_left (apply_nonneg p f))
    apply mul_le_mul _ hbound
      (mul_nonneg (Real.rpow_nonneg hpos.le _) (apply_nonneg (thetaAbsSeminorm F q) f)) (Real.exp_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith [min_le_right (a - l) (h - b)]) hv
/-- The strip seminorm gives a separate integrable majorant for each test. -/
theorem adelicTheta_zeta_strip_majorant (f : GlobalBruhat F) (a b : ℝ)
    (ha : 1 < a) (hab : a ≤ b) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ q : IdeleClass F, ∀ σ : ℝ, a ≤ σ → σ ≤ b →
        ideleClassNorm F q ^ σ * adelicThetaAbs F (GlobalBruhat.algebraicEquiv F f).val q ≤
          C * Real.exp (-c * |Real.log (ideleClassNorm F q)|) := by
  obtain ⟨p, c, _, hc, hp⟩ := adelicTheta_zeta_strip_seminorm F a b ha hab
  exact ⟨p f, c, apply_nonneg p f, hc, hp f⟩

private abbrev K := normOneIdeleClass F

local instance : MeasurableSpace (K F) := borel _
local instance : BorelSpace (K F) := ⟨rfl⟩

/-- The uniform large-modulus bound for the global homogeneous theta average,
as in Theorems 2.2.5.4 and 3.4.2.2. The constant works for all compact
norm-one characters, since every character has modulus one. -/
theorem adelicHomogeneousTheta_largeNorm_bounded (ν : Measure (K F)) [ν.IsHaarMeasure]
    (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f ∈ B, ∀ (ω : PontryaginDual (K F)) (q : IdeleClass F), 1 ≤ ideleClassNorm F q →
        ‖adelicHomogeneousTheta F ν ω (GlobalBruhat.algebraicEquiv F f).val q‖ ≤
          C * (ideleClassNorm F q ^ N)⁻¹ := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨A, hA, hb⟩ := adelicTheta_largeNorm_bounded F B hB N
  let mass := ν.real univ
  have hmass : 0 ≤ mass := ENNReal.toReal_nonneg
  refine ⟨A * (mass + 1), by positivity, fun f hf ω q hq => ?_⟩
  let u := (GlobalBruhat.algebraicEquiv F f)
  let r := (ideleClassNorm F q ^ N)⁻¹
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hlocal (k : K F) :
      ‖((ω k : Circle) : ℂ) * adelicTheta F u.val (k.val * q)‖ ≤ A * r := by
    have hnorm : ideleClassNorm F (k.val * q) = ideleClassNorm F q := by
      rw [map_mul, show ideleClassNorm F k.val = 1 from k.property, one_mul]
    rw [norm_mul, Circle.norm_coe, one_mul]
    refine (norm_adelicTheta_le_abs F u.property _).trans ?_
    have hk := hb f hf (k.val * q) (hnorm.symm ▸ hq)
    rw [hnorm] at hk
    exact (le_div_iff₀ (pow_pos (ideleClassNorm_pos F q) N)).mpr (by rwa [mul_comm]) |>.trans_eq
      (div_eq_mul_inv _ _)
  calc
    ‖adelicHomogeneousTheta F ν ω u.val q‖ ≤ A * r * mass :=
      norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hlocal)
    _ = A * mass * r := mul_right_comm _ _ _
    _ ≤ A * (mass + 1) * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA.le) hr

/-- Uniform small-modulus estimates for the compact character averages.
The constant term retains the chosen norm-one Haar mass. -/
theorem adelicHomogeneousTheta_smallNorm_bounded (ν : Measure (K F)) [ν.IsHaarMeasure]
    (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f ∈ B, ∀ (ω : PontryaginDual (K F)) (q : IdeleClass F), ideleClassNorm F q ≤ 1 →
        let u := (GlobalBruhat.algebraicEquiv F f).val
        let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
        ‖adelicHomogeneousTheta F ν ω u q -
          (if ω = 1 then ν.real univ • ((ideleClassNorm F q)⁻¹ • v 0 - u 0) else 0)‖ ≤
            C * ideleClassNorm F q ^ N := by
  letI := normOneIdeleClass_compact F
  letI : IsFiniteMeasure ν := ⟨isCompact_univ.measure_lt_top⟩
  obtain ⟨A, hA, hb⟩ := adelicTheta_decay_bounded F B hB N
  let mass := ν.real univ
  have hmass : 0 ≤ mass := ENNReal.toReal_nonneg
  refine ⟨A * (mass + 1), by positivity, fun f hf ω q hq => ?_⟩
  dsimp only
  let u := GlobalBruhat.algebraicEquiv F f
  let v := GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)
  let m := ideleClassNorm F q
  let z : ℂ := m⁻¹ • v.val 0 - u.val 0
  let χ (k : K F) : ℂ := ω k
  let a (k : K F) := χ k * adelicTheta F u.val (k.val * q)
  let b (k : K F) := χ k * z
  have hχ : Continuous χ := continuous_subtype_val.comp ω.continuous
  have hθ := adelicTheta_continuous F (bruhat_theta_continuous_and_invariant u.property).1
  have hproj : Continuous (fun k : K F => k.val) := continuous_subtype_val
  have htranslate : Continuous (fun k : K F => k.val * q) := hproj.mul continuous_const
  have ha : Continuous a := hχ.mul (hθ.comp htranslate)
  have hb' : Continuous b := hχ.mul continuous_const
  have hconst : (∫ k, b k ∂ν) = if ω = 1 then mass • z else 0 := by
    change (∫ k, χ k * z ∂ν) = _
    rw [integral_mul_const]
    have hc := integral_character_pair ν (1 : PontryaginDual (K F)) ω
    simp only [PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul] at hc
    change (∫ k, χ k ∂ν) = _ at hc
    rw [hc]
    by_cases hω : ω = 1 <;> simp [hω, Eq.comm, Complex.real_smul, mass]
  have hnorm (k : K F) : ideleClassNorm F (k.val * q) = m := by
    rw [map_mul, show ideleClassNorm F k.val = 1 from k.property, one_mul]
  have hbound (k : K F) : ‖a k - b k‖ ≤ A * m ^ N := by
    change ‖χ k * adelicTheta F u.val (k.val * q) - χ k * z‖ ≤ _
    rw [← mul_sub, norm_mul, show ‖χ k‖ = 1 from Circle.norm_coe _, one_mul]
    rw [show adelicTheta F u.val (k.val * q) - z =
      adelicTheta F u.val (k.val * q) - m⁻¹ • v.val 0 + u.val 0 by dsimp [z]; abel]
    have h := (hb f hf (k.val * q)).2.1 ((hnorm k).trans_le hq)
    rwa [hnorm k] at h
  change ‖(∫ k, a k ∂ν) - (if ω = 1 then mass • z else 0)‖ ≤ _
  rw [← hconst, ← integral_sub
    (ha.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hb'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  calc
    _ ≤ A * m ^ N * mass :=
      norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hbound)
    _ = A * mass * m ^ N := mul_right_comm _ _ _
    _ ≤ A * (mass + 1) * m ^ N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA.le)
        (pow_nonneg (ideleClassNorm_pos F q).le _)

/-- Corrected Theorem 3.4.2.2. The homogeneous theta estimates are
uniform on bounded families. The term for the trivial character carries the
volume of the norm-one class group for the chosen Haar measure. -/
theorem adelicHomogeneousTheta_decay_bounded (ν : Measure (K F)) [ν.IsHaarMeasure]
    (B : Set (GlobalBruhat F)) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ (ω : PontryaginDual (K F)),
      let u := (GlobalBruhat.algebraicEquiv F f).val
      let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
      Continuous (adelicHomogeneousTheta F ν ω u) ∧ ∀ q : IdeleClass F,
        let m := ideleClassNorm F q
        (1 ≤ m → ‖adelicHomogeneousTheta F ν ω u q‖ ≤ C * (m ^ N)⁻¹) ∧
        (m ≤ 1 → ‖adelicHomogeneousTheta F ν ω u q -
          (if ω = 1 then ν.real univ • (m⁻¹ • v 0 - u 0) else 0)‖ ≤ C * m ^ N) := by
  obtain ⟨A, hA, hlarge⟩ := adelicHomogeneousTheta_largeNorm_bounded F ν B hB N
  obtain ⟨D, -, hsmall⟩ := adelicHomogeneousTheta_smallNorm_bounded F ν B hB N
  refine ⟨max A D, hA.trans_le (le_max_left _ _), fun f hf ω => ?_⟩
  refine ⟨adelicHomogeneousTheta_continuous F ν ω (GlobalBruhat.algebraicEquiv F f).property,
    fun q => ⟨fun h => (hlarge f hf ω q h).trans ?_, fun h => (hsmall f hf ω q h).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (inv_nonneg.mpr (pow_nonneg (ideleClassNorm_pos F q).le _))
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (ideleClassNorm_pos F q).le _)

/-- The two pointwise estimates, with the same mass correction, follow
by using a singleton bounded family. -/
theorem adelicHomogeneousTheta_decay (ν : Measure (K F)) [ν.IsHaarMeasure]
    (f : GlobalBruhat F) (ω : PontryaginDual (K F)) (N : ℕ) :
    let u := (GlobalBruhat.algebraicEquiv F f).val
    let v := (GlobalBruhat.algebraicEquiv F (GlobalBruhat.fourier F f)).val
    Continuous (adelicHomogeneousTheta F ν ω u) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ q : IdeleClass F,
        let m := ideleClassNorm F q
        (1 ≤ m → ‖adelicHomogeneousTheta F ν ω u q‖ ≤ C * (m ^ N)⁻¹) ∧
        (m ≤ 1 → ‖adelicHomogeneousTheta F ν ω u q -
          (if ω = 1 then ν.real univ • (m⁻¹ • v 0 - u 0) else 0)‖ ≤ C * m ^ N) := by
  obtain ⟨C, hC, h⟩ := adelicHomogeneousTheta_decay_bounded F ν {f}
    (isVonNBounded_singleton (𝕜 := ℂ) f) N
  exact ⟨(h f (mem_singleton _) ω).1, C, hC, (h f (mem_singleton _) ω).2⟩

end

end Masullo
