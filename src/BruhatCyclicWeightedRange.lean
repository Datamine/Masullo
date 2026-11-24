import BruhatCyclicDifferenceRange
import ModulatedDecayTranslations

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 1200000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

private theorem bruhatSchwartz_mem_geometricTail
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (δ : G) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1) (f : BruhatSchwartz G) :
    (fun x ↦ ∑' n : ℕ, ((ρ ^ n : ℝ) : ℂ) • f.val (δ ^ n * x)) ∈
      bruhatSchwartzSubmodule (G := G) := by
  obtain ⟨p, u, hu⟩ := f.property
  obtain ⟨Q, hpQ⟩ := exists_wholeBruhatStage_refinement m hm hms p
  let P := Q.val.1
  let q := Q.val.2
  let z := p.transition Q.val hpQ u
  have hz : Q.val.realize z = f.val :=
    (congrArg Subtype.val (p.inclusion_transition Q.val hpQ u)).trans hu
  let A := ElementaryLCAModel q.realDim q.torusDim q.latticeRank q.finiteFactor
  let e : Multiplicative A →ₜ* P.StageQuotient := q.equiv.symm
  let lM := (P.descendHom m (P.modulation_eq_one_on_kernel m)).comp e
  let l : A →+ ℝ := lM.toMonoidHom.toAdditive
  have hl : IsProperMap l := (P.descendModulation_isProperMap m hm).comp
    q.equiv.symm.toHomeomorph.isProperMap
  let lift : G →* P.upper.val :=
    { toFun := fun x ↦ ⟨x, Q.property.symm ▸ Subgroup.mem_top x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ ↦ Subtype.ext rfl }
  let φ := (P.stageCoordinates q).toMonoidHom.comp lift
  let s : A := (φ δ).toAdd
  let v : Q.val.Space := ⟨_, elementaryGeometricTail_mem l hl s ρ hρ hρ' z⟩
  have hval (x : G) : z (φ x).toAdd = f.val x :=
    (P.realizeSchwartz_apply_of_mem q z (lift x)).symm.trans (congrFun hz x)
  have hshift (x : G) (n : ℕ) : (φ (δ ^ n * x)).toAdd = (φ x).toAdd + (n : ℤ) • s := by
    rw [map_mul, map_pow, toAdd_mul, toAdd_pow, natCast_zsmul, add_comm]
  refine ⟨Q.val, v, funext fun x ↦ ?_⟩
  change P.realizeSchwartz q v (lift x).val = _
  rw [P.realizeSchwartz_apply_of_mem]
  change (∑' n : ℕ, ((ρ ^ n : ℝ) : ℂ) • z ((φ x).toAdd + (n : ℤ) • s)) = _
  have hv (n : ℕ) : z ((φ x).toAdd + (n : ℤ) • s) = f.val (δ ^ n * x) := by
    rw [← hshift x n, hval]
  simp_rw [hv]

private theorem weighted_forward_tail_mem
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (δ : G) (a : ℝ) (ha : 0 < a * (m δ).toAdd) (f : G → ℂ)
    (hf : modulatedExponentialWeight m a f ∈ bruhatSchwartzSubmodule (G := G)) :
    modulatedExponentialWeight m a (fun x ↦ ∑' n : ℕ, f (δ ^ n * x)) ∈
      bruhatSchwartzSubmodule (G := G) := by
  let ρ := Real.exp (-(a * (m δ).toAdd))
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ' : ρ < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  let F : BruhatSchwartz G := ⟨_, hf⟩
  have hG := bruhatSchwartz_mem_geometricTail m hm hms δ ρ hρ hρ' F
  refine (show modulatedExponentialWeight m a (fun x ↦ ∑' n : ℕ, f (δ ^ n * x)) =
    fun x ↦ ∑' n : ℕ, ((ρ ^ n : ℝ) : ℂ) • F.val (δ ^ n * x) from ?_) ▸ ?_
  · funext x
    simp only [F, modulatedExponentialWeight_apply]
    simp_rw [Complex.real_smul, smul_eq_mul, ← tsum_mul_left]
    apply tsum_congr
    intro n
    have hl : (m (δ ^ n * x)).toAdd = (n : ℝ) * (m δ).toAdd + (m x).toAdd := by
      simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul]
    change _ = ((Real.exp (-(a * (m δ).toAdd)) ^ n *
      Real.exp (a * (m (δ ^ n * x)).toAdd) : ℝ) : ℂ) * _
    rw [← Real.exp_nat_mul, ← Real.exp_add, hl]
    congr 3
    ring
  · exact hG

/-- The ordinary preimage of a cyclic difference inherits every exponential
Schwartz–Bruhat weight of its difference. -/
theorem bruhatSchwartzDifference_inherits_weight
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (γ : G) (hγ : 0 < (m γ).toAdd) (a : ℝ) (v : BruhatSchwartz G)
    (hf : modulatedExponentialWeight m a (bruhatSchwartzDifference γ v).val ∈
      bruhatSchwartzSubmodule (G := G)) :
    modulatedExponentialWeight m a v.val ∈ bruhatSchwartzSubmodule (G := G) := by
  let f := bruhatSchwartzDifference γ v
  have hzero (x : G) : bruhatSchwartz_cyclicOrbitSum m γ hγ x f = 0 :=
    mem_iInter.mp (bruhatSchwartzDifference_range_eq_commonKernel m hm hms γ hγ ▸
      (show f ∈ ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) from ⟨v, rfl⟩)) x
  obtain ⟨u, hu, ht⟩ := bruhatSchwartzDifference_eq_of_orbitSum_zero m hm hms γ hγ f hzero
  have hi : Injective (bruhatSchwartzDifference γ) := by
    simpa only [bruhatSchwartzDifferenceProduct, ContinuousLinearMap.comp_id] using
      bruhatSchwartzDifferenceProduct_injective m [γ] (by simpa using hγ)
  have hv : u = v := hi hu
  have hforward (x : G) : v.val x = ∑' n : ℕ, f.val (γ ^ n * x) := hv ▸ ht x
  have hbackward (x : G) : v.val x = -(∑' n : ℕ, f.val (γ ^ (-(n : ℤ) - 1) * x)) :=
    (hforward x).trans ((bruhatSchwartz_cyclicDifference_two_tails m γ hγ f hzero).1 x)
  rcases lt_trichotomy 0 a with h | rfl | h
  · rw [funext hforward]
    exact weighted_forward_tail_mem m hm hms γ a (mul_pos h hγ) f.val hf
  · convert v.property using 1
    ext x
    rw [modulatedExponentialWeight_apply, zero_mul, Real.exp_zero, one_smul]
  · let F : BruhatSchwartz G := ⟨_, hf⟩
    let f' (x : G) := f.val (γ⁻¹ * x)
    have hneg : 0 < a * (m γ⁻¹).toAdd := by
      rw [map_inv, toAdd_inv]
      exact mul_pos_of_neg_of_neg h (neg_neg_of_pos hγ)
    have hshift : modulatedExponentialWeight m a f' ∈ bruhatSchwartzSubmodule (G := G) := by
      let u' := bruhatSchwartz_translate γ F
      have hmem := (bruhatSchwartzSubmodule (G := G)).smul_mem
        (Real.exp (a * (m γ).toAdd) : ℂ) u'.property
      convert hmem using 1
      funext x
      change Real.exp (a * (m x).toAdd) • f.val (γ⁻¹ * x) =
        (Real.exp (a * (m γ).toAdd) : ℂ) • u'.val x
      rw [show u'.val x = F.val (γ⁻¹ * x) from bruhatSchwartz_translate_apply γ F x]
      change _ = (Real.exp (a * (m γ).toAdd) : ℂ) •
        (Real.exp (a * (m (γ⁻¹ * x)).toAdd) • f.val (γ⁻¹ * x))
      simp only [Complex.real_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
      congr 3
      ring
    have htail := weighted_forward_tail_mem m hm hms γ⁻¹ a hneg f' hshift
    have he (x : G) : v.val x = -(∑' n : ℕ, f' ((γ⁻¹) ^ n * x)) := by
      rw [hbackward]
      congr 1
      apply tsum_congr
      intro n
      dsimp only [f']
      rw [show -(n : ℤ) - 1 = -(1 + (n : ℤ)) by omega, zpow_neg, zpow_add, zpow_one,
        mul_inv_rev, zpow_natCast, inv_pow]
      ac_rfl
    rw [funext he]
    change modulatedExponentialWeight m a (-(fun x ↦ ∑' n : ℕ, f' (γ⁻¹ ^ n * x))) ∈ _
    rw [map_neg]
    exact (bruhatSchwartzSubmodule (G := G)).neg_mem htail

private theorem modulatedDecay_zeroWeight_mem (m : G →ₜ* Multiplicative ℝ)
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (f : ModulatedExponentialInductive m I) :
    f.val ∈ bruhatSchwartzSubmodule (G := G) := by
  have h := (Submodule.mem_iInf _).mp (ModulatedExponentialInductive.algebraicEquiv f).property
    ⟨0, h0⟩
  change modulatedExponentialWeight m 0 f.val ∈ bruhatSchwartzSubmodule at h
  have hz : modulatedExponentialWeight m 0 f.val = f.val := by
    funext x
    rw [modulatedExponentialWeight_apply, zero_mul, Real.exp_zero, one_smul]
  rwa [hz] at h

/-- The inclusion at zero is continuous for the weighted inductive topology. -/
def modulatedDecay_zeroInclusion (m : G →ₜ* Multiplicative ℝ) (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) :
    ModulatedExponentialInductive m I →L[ℂ] BruhatSchwartz G := by
  let L : ModulatedExponentialInductive m I →ₗ[ℂ] BruhatSchwartz G :=
    { toFun := fun f ↦ ⟨f.val, modulatedDecay_zeroWeight_mem m I h0 f⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  refine ⟨L, (locallyConvexFinal_continuous_iff
    (fun p : WholeBruhatStage G ↦ ModulatedExponentialInductive.stageMap (m := m) (I := I) p) L).2
    fun p ↦ ?_⟩
  let z : I := ⟨0, h0⟩
  have he : (fun f : WholeBruhatDecayStage m I p ↦
      L (ModulatedExponentialInductive.stageMap (m := m) (I := I) p f)) =
        p.val.inclusionCLM ∘ WholeBruhatDecayStage.twist p z := by
    funext f
    apply Subtype.ext
    change f.val = p.val.realize (WholeBruhatDecayStage.twist p z f)
    rw [WholeBruhatDecayStage.realize_twist]
    funext x
    change f.val x = modulatedExponentialWeight m 0 f.val x
    rw [modulatedExponentialWeight_apply, zero_mul, Real.exp_zero, one_smul]
  change Continuous (fun f : WholeBruhatDecayStage m I p ↦
      L (ModulatedExponentialInductive.stageMap (m := m) (I := I) p f))
  rw [he]
  exact p.val.inclusionCLM.continuous.comp ((WholeBruhatDecayStage.continuous_iff
    (id : WholeBruhatDecayStage m I p → _)).mp continuous_id z)

/-- With zero in the weight interval, a test belongs to the range of the
cyclic difference on the full weighted space exactly when its ordinary
orbit sums vanish. The same preimage works for all weights. -/
theorem modulatedDecay_cyclicDifference_exists_iff
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (γ : G) (hγ : 0 < (m γ).toAdd)
    (f : ModulatedExponentialInductive m I) :
    let F := modulatedDecay_zeroInclusion m I h0 f
    (∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x F = 0) ↔
      ∃ v : ModulatedExponentialInductive m I,
        (∀ x, v.val x - v.val (γ * x) = f.val x) ∧
        ∀ x, v.val x = ∑' n : ℕ, f.val (γ ^ n * x) := by
  intro F
  constructor
  · intro hzero
    obtain ⟨u, hu, htail⟩ := bruhatSchwartzDifference_eq_of_orbitSum_zero m hm hms γ hγ F hzero
    have hw : u.val ∈ modulatedExponentialDecaySubmodule m I := by
      apply (Submodule.mem_iInf _).mpr
      intro a
      have hfa := (Submodule.mem_iInf _).mp (ModulatedExponentialInductive.algebraicEquiv f).property a
      have hfu : modulatedExponentialWeight m a F.val ∈ bruhatSchwartzSubmodule (G := G) := hfa
      exact bruhatSchwartzDifference_inherits_weight m hm hms γ hγ a u (hu.symm ▸ hfu)
    let v := ModulatedExponentialInductive.algebraicEquiv.symm ⟨u.val, hw⟩
    refine ⟨v, fun x ↦ ?_, htail⟩
    change u.val x - u.val (γ * x) = F.val x
    rw [← bruhatSchwartzDifference_apply, hu]
  · rintro ⟨v, hv, _⟩ x
    let w : BruhatSchwartz G := ⟨v.val, modulatedDecay_zeroWeight_mem m I h0 v⟩
    have he (y : G) : (bruhatSchwartzDifference γ w).val y = F.val y := by
      rw [bruhatSchwartzDifference_apply]
      exact hv y
    have hw : bruhatSchwartzDifference γ w = F := Subtype.ext (funext he)
    have hR : F ∈ ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) := ⟨w, hw⟩
    rw [bruhatSchwartzDifference_range_eq_commonKernel m hm hms γ hγ] at hR
    exact mem_iInter.mp hR x

/-- The weighted preimage preserves the character on every subgroup,
in particular on the norm-one subgroup. -/
theorem modulatedDecay_cyclicDifference_exists_isotypic
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (γ : G) (hγ : 0 < (m γ).toAdd)
    (f : ModulatedExponentialInductive m I)
    (hzero : ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x (modulatedDecay_zeroInclusion m I h0 f) = 0)
    {K : Subgroup G} (χ : PontryaginDual K)
    (hf : ∀ (a : K) x, f.val (a.val⁻¹ * x) = (χ a : ℂ) * f.val x) :
    ∃ v : ModulatedExponentialInductive m I,
      (∀ x, v.val x - v.val (γ * x) = f.val x) ∧
        ∀ (a : K) x, v.val (a.val⁻¹ * x) = (χ a : ℂ) * v.val x := by
  obtain ⟨v, hv, htail⟩ := (modulatedDecay_cyclicDifference_exists_iff m hm hms I h0 γ hγ f).1 hzero
  refine ⟨v, hv, fun a x ↦ ?_⟩
  have he (n : ℕ) : f.val (γ ^ n * (a.val⁻¹ * x)) = (χ a : ℂ) * f.val (γ ^ n * x) := by
    rw [mul_left_comm, hf]
  rw [htail, htail]
  simp_rw [he]
  rw [tsum_mul_left]

/-- A finite product of positive-period differences cannot create an
exponential weight absent from its ordinary Schwartz preimage. -/
theorem bruhatSchwartzDifferenceProduct_inherits_weight
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (gs : List G) (hgs : ∀ g ∈ gs, 0 < (m g).toAdd) (a : ℝ) (v : BruhatSchwartz G)
    (hf : modulatedExponentialWeight m a (bruhatSchwartzDifferenceProduct gs v).val ∈
      bruhatSchwartzSubmodule (G := G)) :
    modulatedExponentialWeight m a v.val ∈ bruhatSchwartzSubmodule (G := G) := by
  induction gs with
  | nil => exact hf
  | cons g gs ih =>
    apply ih (fun t ht ↦ hgs t (.tail _ ht))
    exact bruhatSchwartzDifference_inherits_weight m hm hms g (hgs g (.head _)) a
      (bruhatSchwartzDifferenceProduct gs v) hf

/-- The full weighted difference range is closed for the actual final
locally convex topology. -/
theorem modulatedDecay_cyclicDifference_isClosed_range
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)
    (I : Set ℝ) (h0 : (0 : ℝ) ∈ I) (γ : G) (hγ : 0 < (m γ).toAdd) :
    IsClosed {f : ModulatedExponentialInductive m I |
      ∃ v : ModulatedExponentialInductive m I, ∀ x, v.val x - v.val (γ * x) = f.val x} := by
  have h (f : ModulatedExponentialInductive m I) :
      (∃ v : ModulatedExponentialInductive m I, ∀ x, v.val x - v.val (γ * x) = f.val x) ↔
        ∀ x, bruhatSchwartz_cyclicOrbitSum m γ hγ x (modulatedDecay_zeroInclusion m I h0 f) = 0 := by
    refine ⟨fun ⟨v, hv⟩ ↦ ?_, fun hzero ↦ ?_⟩
    · let hv₀ := modulatedDecay_zeroInclusion m I h0 v
      have he (x : G) : (bruhatSchwartzDifference γ hv₀).val x =
          (modulatedDecay_zeroInclusion m I h0 f).val x := by
        rw [bruhatSchwartzDifference_apply]
        exact hv x
      have hmem : modulatedDecay_zeroInclusion m I h0 f ∈
          ((bruhatSchwartzDifference γ).range : Set (BruhatSchwartz G)) :=
        ⟨hv₀, Subtype.ext (funext he)⟩
      rw [bruhatSchwartzDifference_range_eq_commonKernel m hm hms γ hγ] at hmem
      exact fun x ↦ mem_iInter.mp hmem x
    · obtain ⟨v, hv, _⟩ := (modulatedDecay_cyclicDifference_exists_iff m hm hms I h0 γ hγ f).1 hzero
      exact ⟨v, hv⟩
  simp_rw [h, ofPred_forall]
  exact isClosed_iInter fun x ↦ isClosed_eq
    ((bruhatSchwartz_cyclicOrbitSum m γ hγ x).continuous.comp
      (modulatedDecay_zeroInclusion m I h0).continuous) continuous_const

end

end Masullo
