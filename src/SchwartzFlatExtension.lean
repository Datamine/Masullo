import SchwartzFlatJetBounds
import SchwartzComplete
import FrechetFactorization
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Asymptotics Filter Set Topology
open scoped Classical ContDiff SchwartzMap

namespace Masullo

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Zero extension across a hyperplane is smooth and flat when the jets on
the complement vanish at least quadratically in the defining coordinate. -/
theorem smooth_flat_zeroExtend_of_jet_bounds (p : E →L[ℝ] D) (g : E → ℂ)
    (hg : ContDiffOn ℝ ∞ g {x | p x ≠ 0})
    (hbound : ∀ n : ℕ, ∃ C ≥ 0, ∀ x : E, p x ≠ 0 → ‖p x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n g x‖ ≤ C * ‖p x‖ ^ 2) :
    let g₀ := {x | p x ≠ 0}.indicator g
    ContDiff ℝ ∞ g₀ ∧ ∀ n : ℕ,
      iteratedFDeriv ℝ n g₀ = {x | p x ≠ 0}.indicator (iteratedFDeriv ℝ n g) := by
  let U := {x | p x ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun p.continuous continuous_const
  let J (n : ℕ) := U.indicator (iteratedFDeriv ℝ n g)
  have hnear (n : ℕ) {x : E} (hx : x ∈ U) : J n =ᶠ[𝓝 x] iteratedFDeriv ℝ n g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  have hdiff (n : ℕ) (x : E) (hx : x ∉ U) :
      HasFDerivAt (J n) (0 : E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) ℂ) x := by
    have hx0 : p x = 0 := by simpa [U] using hx
    obtain ⟨C, hC, hCbound⟩ := hbound n
    have hN : ∀ᶠ y in 𝓝 x, ‖p y‖ < 1 :=
      (isOpen_lt p.continuous.norm continuous_const).mem_nhds (by simp [hx0])
    have hO : J n =O[𝓝 x] fun y ↦ ‖y - x‖ ^ 2 := by
      apply IsBigO.of_bound (C * ‖p‖ ^ 2)
      filter_upwards [hN] with y hy
      by_cases hy0 : y ∈ U
      · change p y ≠ 0 at hy0
        have hp : ‖p y‖ ≤ ‖p‖ * ‖y - x‖ := by
          simpa only [map_sub, hx0, sub_zero] using p.le_opNorm (y - x)
        rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖y-x‖ ^ 2)]
        change ‖U.indicator (iteratedFDeriv ℝ n g) y‖ ≤ _
        rw [indicator_of_mem hy0]
        calc
          _ ≤ C * ‖p y‖ ^ 2 := hCbound y hy0 hy.le
          _ ≤ C * (‖p‖ * ‖y - x‖) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp _) hC
          _ = _ := by rw [mul_pow, mul_assoc]
      · change ‖U.indicator (iteratedFDeriv ℝ n g) y‖ ≤ _
        rw [indicator_of_notMem hy0, norm_zero]
        positivity
    exact hO.hasFDerivAt (by decide : 1 < 2)
  have hJ (n : ℕ) : iteratedFDeriv ℝ n (U.indicator g) = J n := by
    induction n with
    | zero =>
      funext x
      by_cases hx : x ∈ U
      · have he : U.indicator g =ᶠ[𝓝 x] g := by
          filter_upwards [hU.mem_nhds hx] with y hy using indicator_of_mem hy _
        exact ((he.iteratedFDeriv ℝ 0).eq_of_nhds).trans (indicator_of_mem hx _).symm
      · ext a
        rw [iteratedFDeriv_zero_apply, indicator_of_notMem hx]
        change (0 : ℂ) = U.indicator (iteratedFDeriv ℝ 0 g) x a
        rw [indicator_of_notMem hx]
        rfl
    | succ n ih =>
      funext x
      by_cases hx : x ∈ U
      · have he : U.indicator g =ᶠ[𝓝 x] g := by
          filter_upwards [hU.mem_nhds hx] with y hy using indicator_of_mem hy _
        exact ((he.iteratedFDeriv ℝ (n + 1)).eq_of_nhds).trans (indicator_of_mem hx _).symm
      · rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, (hdiff n x hx).fderiv]
        change _ = U.indicator (iteratedFDeriv ℝ (n+1) g) x
        rw [indicator_of_notMem hx]
        exact LinearIsometryEquiv.map_zero _
  refine ⟨contDiff_of_differentiable_iteratedFDeriv fun n _ x ↦ ?_, hJ⟩
  rw [hJ]
  by_cases hx : x ∈ U
  · have h := hg.contDiffAt (hU.mem_nhds hx)
    have hh : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) x :=
      h.differentiableAt_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top n)
    exact hh.congr_of_eventuallyEq (hnear n hx)
  · exact (hdiff n x hx).differentiableAt

/-- The Leibniz estimate for multiplying a flat Schwartz test by a smooth
function whose jets have polynomial growth and finite-order singularities
along one coordinate hyperplane. -/
theorem flatSchwartz_mul_jet_bound (p : E →L[ℝ] D) (i : D →L[ℝ] E)
    (hpi : Function.LeftInverse p i) (hi : ∀ d, ‖i d‖ ≤ ‖d‖)
    (b : E → ℂ) (hb : ContDiffOn ℝ ∞ b {x | p x ≠ 0})
    (f : 𝓢(E, ℂ)) (hf : f ∈ schwartzFlatSubspace {x | p x = 0})
    (k n m M : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbnd : ∀ j ≤ n, ∀ x : E, p x ≠ 0 →
      ‖iteratedFDeriv ℝ j b x‖ ≤ B * max 1 ‖x‖ ^ M / min 1 ‖p x‖ ^ M) :
    ∃ C ≥ 0, ∀ x : E, p x ≠ 0 →
      max 1 ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ b y * f y) x‖ ≤
        C * min 1 ‖p x‖ ^ m := by
  let K := k + M
  let N := m + M
  let S (d : ℕ) := max (SchwartzMap.seminorm ℂ 0 d f) (SchwartzMap.seminorm ℂ K d f)
  let Ct (j : ℕ) : ℝ := (n.choose j : ℝ) * B * (3 ^ K * max (S (n-j)) (S (n-j+N)))
  have hCt (j : ℕ) : 0 ≤ Ct j := by
    dsimp [Ct, S]
    positivity
  refine ⟨∑ j ∈ Finset.range (n+1), Ct j, Finset.sum_nonneg (fun j _ ↦ hCt j), ?_⟩
  intro x hx
  let W := max 1 ‖x‖
  let d := min 1 ‖p x‖
  have hW : 0 ≤ W := le_max_of_le_left zero_le_one
  have hd : 0 < d := lt_min zero_lt_one (norm_pos_iff.mpr hx)
  have hU : IsOpen {x : E | p x ≠ 0} := isOpen_ne_fun p.continuous continuous_const
  have hprod := norm_iteratedFDerivWithin_mul_le hb f.smooth'.contDiffOn hU.uniqueDiffOn
    (x := x) hx (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx] at hprod
  change W ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ b y * f y) x‖ ≤ _ * d ^ m
  refine (mul_le_mul_of_nonneg_left hprod (pow_nonneg hW _)).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hf' : W ^ K * ‖iteratedFDeriv ℝ (n-j) f x‖ ≤
      (3 ^ K * max (S (n-j)) (S (n-j+N))) * d ^ N :=
    schwartzFlat_weighted_jet_le_of_coordinate p i hpi hi f hf x K (n-j) N
  have hratio : (W ^ K * ‖iteratedFDeriv ℝ (n-j) f x‖) / d ^ M ≤
      (3 ^ K * max (S (n-j)) (S (n-j+N))) * d ^ m := by
    apply (div_le_iff₀ (pow_pos hd _)).mpr
    simpa only [N, pow_add, mul_assoc] using hf'
  calc
    _ ≤ W ^ k * ((n.choose j : ℝ) * (B * W ^ M / d ^ M) * ‖iteratedFDeriv ℝ (n-j) f x‖) := by
      gcongr
      · exact hbnd j hjn x hx
      · exact le_rfl
    _ = (n.choose j : ℝ) * B * ((W ^ K * ‖iteratedFDeriv ℝ (n-j) f x‖) / d ^ M) := by
      dsimp [K]
      rw [pow_add]
      ring
    _ ≤ (n.choose j : ℝ) * B * ((3 ^ K * max (S (n-j)) (S (n-j+N))) * d ^ m) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = Ct j * d ^ m := (mul_assoc _ _ _).symm

/-- A multiplier with polynomial growth at infinity and finite-order
singularities on a coordinate hyperplane acts by zero extension on flat
Schwartz tests. It preserves flatness on any additional vanishing loci. -/
theorem exists_flatSchwartz_mul_of_jet_bounds (p : E →L[ℝ] D) (i : D →L[ℝ] E)
    (hpi : Function.LeftInverse p i) (hi : ∀ d, ‖i d‖ ≤ ‖d‖)
    (b : E → ℂ) (hb : ContDiffOn ℝ ∞ b {x | p x ≠ 0})
    (hbnd : ∀ n : ℕ, ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j ≤ n, ∀ x : E, p x ≠ 0 →
      ‖iteratedFDeriv ℝ j b x‖ ≤ B * max 1 ‖x‖ ^ M / min 1 ‖p x‖ ^ M)
    (A : Set E) (hA : {x | p x = 0} ⊆ A) (f : 𝓢(E, ℂ)) (hf : f ∈ schwartzFlatSubspace A) :
    ∃ g : 𝓢(E, ℂ), g ∈ schwartzFlatSubspace A ∧
      (g : E → ℂ) = {x | p x ≠ 0}.indicator (fun y ↦ b y * f y) := by
  let U := {x | p x ≠ 0}
  have hU : IsOpen {x : E | p x ≠ 0} := isOpen_ne_fun p.continuous continuous_const
  let g (y : E) := b y * f y
  have hg : ContDiffOn ℝ ∞ g U := hb.mul f.smooth'.contDiffOn
  have hf₀ : f ∈ schwartzFlatSubspace {x | p x = 0} :=
    (mem_schwartzFlatSubspace _ _).mpr fun x hx ↦ (mem_schwartzFlatSubspace _ _).mp hf x (hA hx)
  have hbound (k n m : ℕ) : ∃ C ≥ 0, ∀ x : E, p x ≠ 0 →
      max 1 ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ ≤ C * min 1 ‖p x‖ ^ m := by
    obtain ⟨M, B, hB, h⟩ := hbnd n
    exact flatSchwartz_mul_jet_bound p i hpi hi b hb f hf₀ k n m M B hB h
  have hsmall (n : ℕ) : ∃ C ≥ 0, ∀ x : E, p x ≠ 0 → ‖p x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n g x‖ ≤ C * ‖p x‖ ^ 2 := by
    obtain ⟨C, hC, he⟩ := hbound 0 n 2
    exact ⟨C, hC, fun x hx hle ↦ by simpa only [pow_zero, one_mul, min_eq_right hle] using he x hx⟩
  obtain ⟨hs, hJ⟩ := smooth_flat_zeroExtend_of_jet_bounds p g hg hsmall
  let w : 𝓢(E, ℂ) := ⟨U.indicator g, hs, by
    intro k n
    obtain ⟨C, hC, he⟩ := hbound k n 0
    refine ⟨C, fun x ↦ ?_⟩
    rw [hJ]
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 ‖x‖) _)
        (norm_nonneg _)).trans ?_
      simpa only [pow_zero, mul_one] using he x hx
    · rw [indicator_of_notMem hx, norm_zero, mul_zero]
      exact hC⟩
  refine ⟨w, (mem_schwartzFlatSubspace _ _).mpr fun x hx n ↦ ?_, rfl⟩
  change iteratedFDeriv ℝ n (U.indicator g) x = 0
  rw [hJ]
  by_cases hp : x ∈ U
  · rw [indicator_of_mem hp]
    apply norm_eq_zero.mp
    have hx' : p x ≠ 0 := hp
    have he := norm_iteratedFDerivWithin_mul_le hb f.smooth'.contDiffOn hU.uniqueDiffOn (x := x) hx'
      (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)
    simp_rw [iteratedFDerivWithin_of_isOpen _ hU hx'] at he
    apply le_antisymm ?_ (norm_nonneg _)
    refine he.trans_eq ?_
    apply Finset.sum_eq_zero
    intro j _
    have hz : iteratedFDeriv ℝ (n-j) f.toFun x = 0 :=
      (mem_schwartzFlatSubspace _ _).mp hf x hx (n-j)
    rw [hz, norm_zero, mul_zero]
  · exact indicator_of_notMem hp _

/-- The multiplier on the full flat Schwartz subspace is continuous in
the induced Schwartz topology. Its graph is closed by pointwise evaluation. -/
theorem exists_flatSchwartz_mulCLM_of_jet_bounds (p : E →L[ℝ] D) (i : D →L[ℝ] E)
    (hpi : Function.LeftInverse p i) (hi : ∀ d, ‖i d‖ ≤ ‖d‖)
    (b : E → ℂ) (hb : ContDiffOn ℝ ∞ b {x | p x ≠ 0})
    (hbnd : ∀ n : ℕ, ∃ (M : ℕ) (B : ℝ), 0 ≤ B ∧ ∀ j ≤ n, ∀ x : E, p x ≠ 0 →
      ‖iteratedFDeriv ℝ j b x‖ ≤ B * max 1 ‖x‖ ^ M / min 1 ‖p x‖ ^ M)
    (A : Set E) (hA : {x | p x = 0} ⊆ A) :
    ∃ M : schwartzFlatSubspace A →L[ℂ] schwartzFlatSubspace A,
      ∀ f : schwartzFlatSubspace A, ((M f).val : E → ℂ) =
        {x | p x ≠ 0}.indicator (fun y ↦ b y * f.val y) := by
  let P := schwartzFlatSubspace A
  let c := {x | p x ≠ 0}.indicator b
  have h (f : P) : ∃ g : P, ∀ x : E, g.val x = c x * f.val x := by
    obtain ⟨g, hg, he⟩ := exists_flatSchwartz_mul_of_jet_bounds p i hpi hi b hb hbnd A hA
      f.val f.property
    refine ⟨⟨g, hg⟩, fun x ↦ ?_⟩
    have hx := congrFun he x
    by_cases hpx : p x ≠ 0 <;> simpa [c, indicator_apply, hpx] using hx
  choose M hM using h
  let L : P →ₗ[ℂ] P := {
    toFun := M
    map_add' := fun f g ↦ Subtype.ext (SchwartzMap.ext fun x ↦ by
      change (M (f+g)).val x = (M f).val x + (M g).val x
      rw [hM, hM, hM]
      exact mul_add _ _ _)
    map_smul' := fun a f ↦ Subtype.ext (SchwartzMap.ext fun x ↦ by
      change (M (a • f)).val x = a * (M f).val x
      rw [hM, hM]
      exact mul_left_comm _ _ _) }
  letI : CompleteSpace 𝓢(E, ℂ) := completeSpace_schwartzMap
  letI : IsUniformAddGroup P := P.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace P := (schwartzFlatSubspace_isClosed A).completeSpace_coe
  letI : FirstCountableTopology P := IsInducing.subtypeVal.firstCountableTopology
  have hgraph : (L.graph : Set (P × P)) =
      ⋂ x : E, {z : P × P | z.2.val x = c x * z.1.val x} := by
    ext z
    change z.2 = M z.1 ↔ _
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro he x
      rw [he, hM]
    · intro he
      exact Subtype.ext (SchwartzMap.ext fun x ↦ (he x).trans (hM z.1 x).symm)
  have hc : Continuous L := by
    apply frechet_continuous_of_closed_graph L
    rw [hgraph]
    apply isClosed_iInter
    intro x
    have hEval : Continuous (fun f : P ↦ f.val x) :=
      ((BoundedContinuousFunction.evalCLM ℂ x).continuous.comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ).continuous).comp continuous_subtype_val
    exact isClosed_eq (hEval.comp continuous_snd) (continuous_const.mul (hEval.comp continuous_fst))
  refine ⟨⟨L, hc⟩, fun f ↦ funext fun x ↦ ?_⟩
  change (M f).val x = {y | p y ≠ 0}.indicator (fun y ↦ b y * f.val y) x
  rw [hM]
  by_cases hx : p x ≠ 0 <;> simp [c, hx]

end Masullo
