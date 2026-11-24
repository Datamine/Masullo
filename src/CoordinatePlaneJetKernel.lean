import CoordinatePlaneDistributionOrder
import SchwartzFlatJetBounds
import ElementarySchwartz
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open Filter Function Set TopologicalSpace Topology
open scoped ContDiff Distributions SchwartzMap

namespace Masullo

noncomputable section

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D]

private abbrev Tests (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  𝓓((⊤ : Opens X), ℂ)

private theorem normal_jet_bound (p : E →L[ℝ] D) (i : D →L[ℝ] E)
    (hpi : LeftInverse p i) (hi : ‖i‖ ≤ 1)
    (f : 𝓢(E, ℂ)) (N : ℕ)
    (hf : ∀ y, p y = 0 → ∀ k ≤ N, iteratedFDeriv ℝ k f y = 0)
    {r : ℝ} (hr : 0 ≤ r) (x : E) (hx : ‖p x‖ ≤ r) (k : ℕ) (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ SchwartzMap.seminorm ℂ 0 (N + 1) f * r ^ (N + 1 - k) := by
  let y := x - i (p x)
  have hy : p y = 0 := by simp only [y, map_sub, hpi _, sub_self]
  have hxy : x ∈ Metric.closedBall y r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖x - (x - i (p x))‖ ≤ r
    rw [sub_sub_cancel]
    calc
      ‖i (p x)‖ ≤ ‖i‖ * ‖p x‖ := i.le_opNorm _
      _ ≤ ‖p x‖ := mul_le_of_le_one_left (norm_nonneg _) hi
      _ ≤ r := hx
  refine schwartz_norm_jet_le_on_closedBall_of_vanishing_jets f y hr (N + 1 - k) k ?_ ?_ x hxy
  · intro j _ hj
    exact hf y hy j (by omega)
  · intro z _
    rw [show k + (N + 1 - k) = N + 1 by omega]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f _ z

private theorem scaled_cutoff_jet_bound (p : E →L[ℝ] D) (hp : ‖p‖ ≤ 1)
    (b : 𝓢(D, ℂ)) {r : ℝ} (hr : 0 < r) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y ↦ b (r⁻¹ • p y)) x‖ ≤
      SchwartzMap.seminorm ℂ 0 k b / r ^ k := by
  let L : E →L[ℝ] D := r⁻¹ • p
  change ‖iteratedFDeriv ℝ k (b.toFun ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right b.smooth' x
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  have hL : ‖L‖ ≤ r⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hr.le) hp
  calc
    _ ≤ ‖iteratedFDeriv ℝ k b (L x)‖ * ∏ _ : Fin k, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ SchwartzMap.seminorm ℂ 0 k b * (r⁻¹) ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ b _ _)
        (pow_le_pow_left₀ (norm_nonneg _) hL _) (by positivity) (apply_nonneg _ _)
    _ = _ := by rw [inv_pow, div_eq_mul_inv]

variable [FiniteDimensional ℝ D]

/-- An order-N distribution carried by a split coordinate plane kills a test
whose jets through order N vanish along the plane. The proof uses a cutoff
in the normal directions and a derivative bound linear in its radius. -/
theorem coordinatePlane_distribution_kills_vanishing_jets
    (p : E →L[ℝ] D) (i : D →L[ℝ] E) (hpi : LeftInverse p i)
    (hp : ‖p‖ ≤ 1) (hi : ‖i‖ ≤ 1) (T : Tests E →L[ℂ] ℂ) (N : ℕ)
    (hT : testDistributionOrderLE T N)
    (hvan : Distribution.IsVanishingOn (⇑T) {y | p y = 0}ᶜ)
    (f : Tests E) (hf : ∀ y, p y = 0 → ∀ k ≤ N, iteratedFDeriv ℝ k (f : E → ℂ) y = 0) :
    T f = 0 := by
  let fS := f.hasCompactSupport.toSchwartzMap f.contDiff
  let K : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
  obtain ⟨C, hC, hCbound⟩ := hT K
  let b₀ : ContDiffBump (0 : D) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hb₀ : tsupport (fun x ↦ (b₀ x : ℂ)) ⊆ Metric.closedBall 0 1 :=
    (tsupport_comp_subset Complex.ofReal_zero b₀).trans (by rw [b₀.tsupport_eq])
  let b : 𝓢(D, ℂ) := HasCompactSupport.toSchwartzMap
    ((isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport _) hb₀)
    (Complex.ofRealCLM.contDiff.comp b₀.contDiff)
  let A := SchwartzMap.seminorm ℂ 0 (N + 1) fS
  let B := ∑ j ∈ Finset.range (N + 1), SchwartzMap.seminorm ℂ 0 j b
  have hA : 0 ≤ A := apply_nonneg _ _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _
  have hsmall (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : ‖T f‖ ≤ C * (2 ^ N * (B * A) * r) := by
    let L : E →L[ℝ] D := r⁻¹ • p
    let χ : E → ℂ := b ∘ L
    have hχ : ContDiff ℝ ∞ χ := b.smooth'.comp L.contDiff
    let g₀ : E → ℂ := fun x ↦ χ x * f x
    have hgK : tsupport g₀ ⊆ (K : Set E) := tsupport_mul_subset_right
    let g : Tests E := ⟨g₀, hχ.mul f.contDiff,
      K.isCompact.of_isClosed_subset (isClosed_tsupport _) hgK, subset_univ _⟩
    have hTf : T f = T g := by
      have hs : tsupport (f - g) ⊆ {y | p y = 0}ᶜ := by
        intro x hx hxp
        have hxL : L x = 0 := by change r⁻¹ • p x = 0; rw [hxp, smul_zero]
        have hloc : ((f - g : Tests E) : E → ℂ) =ᶠ[𝓝 x] 0 := by
          have hball : L ⁻¹' Metric.ball 0 (1 / 2) ∈ 𝓝 x :=
            (Metric.isOpen_ball.preimage L.continuous).mem_nhds
              (by change L x ∈ Metric.ball 0 (1 / 2); rw [hxL]; simp)
          filter_upwards [hball] with y hy
          change f y - (b₀ (L y) : ℂ) * f y = 0
          rw [b₀.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), Complex.ofReal_one,
            one_mul, sub_self]
        exact (notMem_tsupport_iff_eventuallyEq.mpr hloc) hx
      exact sub_eq_zero.mp (by simpa only [map_sub] using hvan (f - g) hs)
    rw [hTf]
    refine hCbound g hgK _ (by positivity) (fun j hj x ↦ ?_)
    by_cases hx : ‖p x‖ ≤ r
    · change ‖iteratedFDeriv ℝ j g₀ x‖ ≤ _
      have hprod := norm_iteratedFDeriv_mul_le hχ f.contDiff x
        (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
      refine hprod.trans ?_
      calc
        (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
            ‖iteratedFDeriv ℝ k χ x‖ * ‖iteratedFDeriv ℝ (j - k) (f : E → ℂ) x‖) ≤
            ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * (B * A) * r := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ j := by simpa using hk
          have hb := scaled_cutoff_jet_bound p hp b hr x k
          have hb' : SchwartzMap.seminorm ℂ 0 k b ≤ B :=
            Finset.single_le_sum (fun n _ ↦ apply_nonneg
              (SchwartzMap.seminorm ℂ 0 n) b) (Finset.mem_range.mpr (by omega))
          have hb'' : ‖iteratedFDeriv ℝ k χ x‖ ≤ B / r ^ k :=
            hb.trans (div_le_div_of_nonneg_right hb' (by positivity))
          have ha : ‖iteratedFDeriv ℝ (j - k) (f : E → ℂ) x‖ ≤
              A * r ^ (N + 1 - (j - k)) :=
            normal_jet_bound p i hpi hi fS N hf hr.le x hx _ (by omega)
          have hpow : r ^ (N + 1 - j) ≤ r := by
            simpa using (pow_le_pow_of_le_one hr.le hr1 (show 1 ≤ N + 1 - j by omega))
          calc
            _ ≤ (j.choose k : ℝ) * ((B / r ^ k) * (A * r ^ (N + 1 - (j - k)))) := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left (mul_le_mul hb'' ha (norm_nonneg _)
                (by positivity)) (by positivity)
            _ = (j.choose k : ℝ) * (B * A) * r ^ (N + 1 - j) := by
              rw [show N + 1 - (j - k) = (N + 1 - j) + k by omega, pow_add]
              field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (2 : ℝ) ^ j * (B * A) * r := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
          norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (by positivity)) hr.le
    · have hloc : (g : E → ℂ) =ᶠ[𝓝 x] 0 := by
        filter_upwards [(isOpen_lt continuous_const (p.continuous.norm)).mem_nhds (lt_of_not_ge hx)]
          with y hy
        have hLy : L y ∉ Metric.closedBall 0 1 := by
          rw [Metric.mem_closedBall, dist_zero_right]
          change ¬ ‖r⁻¹ • p y‖ ≤ 1
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_eq_div]
          exact not_le.mpr ((one_lt_div hr).mpr hy)
        have hbzero : (b₀ (L y) : ℂ) = 0 :=
          notMem_support.mp (fun hm ↦ hLy (hb₀ (subset_closure hm)))
        change (b₀ (L y) : ℂ) * f y = 0
        rw [hbzero, zero_mul]
      rw [(hloc.iteratedFDeriv ℝ j).eq_of_nhds]
      change ‖iteratedFDeriv ℝ j (fun _ : E ↦ (0 : ℂ)) x‖ ≤ _
      simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      positivity
  by_contra h
  have ht : 0 < ‖T f‖ := norm_pos_iff.mpr h
  let M := C * (2 ^ N * (B * A))
  have hM : 0 ≤ M := by positivity
  let r := min 1 (‖T f‖ / (M + 1))
  have hr : 0 < r := lt_min zero_lt_one (div_pos ht (by positivity))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hbound := hsmall r hr hr1
  have hlt : M * r < ‖T f‖ := by
    calc
      M * r ≤ M * (‖T f‖ / (M + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM
      _ = (M / (M + 1)) * ‖T f‖ := by ring
      _ < ‖T f‖ := mul_lt_of_lt_one_left ht ((div_lt_one (by positivity)).mpr (lt_add_one _))
  exact hlt.not_ge (by simpa only [M, mul_assoc] using hbound)

omit [FiniteDimensional ℝ D] in
/-- At a split plane, vanishing of the pure normal jets at every point
implies vanishing of all mixed jets through the same order. A mixed jet
with a tangent direction differentiates a lower-order zero jet along the
plane. -/
theorem coordinatePlane_all_jets_zero_of_normal
    (p : E →L[ℝ] D) (i : D →L[ℝ] E) (hpi : LeftInverse p i)
    (f : E → ℂ) (hc : ContDiff ℝ ∞ f) (N : ℕ)
    (hf : ∀ y, p y = 0 → ∀ k ≤ N, ∀ m : Fin k → D,
      iteratedFDeriv ℝ k f y (i ∘ m) = 0) :
    ∀ y, p y = 0 → ∀ k ≤ N, iteratedFDeriv ℝ k f y = 0 := by
  classical
  suffices hh : ∀ k ≤ N, ∀ y, p y = 0 → iteratedFDeriv ℝ k f y = 0 by
    exact fun y hy k hk ↦ hh k hk y hy
  intro k
  induction k with
  | zero =>
    intro hk y hy
    ext m
    have hm : m = i ∘ (fun _ : Fin 0 ↦ (0 : D)) := funext fun j ↦ Fin.elim0 j
    rw [hm, hf y hy 0 hk]
    rfl
  | succ k ih =>
    intro hk y hy
    ext m
    let B := iteratedFDeriv ℝ (k + 1) f y
    have hker (u : Fin (k + 1) → E) (j : Fin (k + 1)) (hj : p (u j) = 0) : B u = 0 := by
      let σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 j
      have he : B (u ∘ σ) = B u := by
        have h := iteratedFDeriv_apply_list_perm hc id (σ.ofFn_comp_perm u) y
        have hlen (v : Fin (k + 1) → E) (a : ℕ) (ha : a = k + 1) :
            iteratedFDeriv ℝ a f y (fun j ↦ v (Fin.cast ha j)) = B v := by
          subst a
          rfl
        simpa only [id_eq, List.get_ofFn, hlen] using h
      rw [← he]
      have hzero : (u ∘ σ) 0 = u j := by simp [σ]
      rw [show B (u ∘ σ) = _ from iteratedFDeriv_succ_apply_left _, hzero]
      let J := iteratedFDeriv ℝ k f
      let l : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (u j)
      have hcurve (t : ℝ) : J (y + l t) = 0 := by
        apply ih (by omega)
        simp [l, hy, hj]
      have hd : DifferentiableAt ℝ J y :=
        hc.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k) y
      have hline : HasFDerivAt (fun t : ℝ ↦ y + l t) l 0 :=
        l.hasFDerivAt.const_add y
      have hdy : y + l (0 : ℝ) = y := by simp
      have hd' : HasFDerivAt J (fderiv ℝ J y) (y + l (0 : ℝ)) := hdy.symm ▸ hd.hasFDerivAt
      have h := (hd'.comp 0 hline).fderiv
      have hconst : J ∘ (fun t : ℝ ↦ y + l t) = 0 := funext hcurve
      rw [hconst, fderiv_zero] at h
      have hv := congrArg (fun L : ℝ →L[ℝ] _ ↦ L (1 : ℝ)) h
      have hz : fderiv ℝ J y (u j) = 0 := by simpa [l] using hv.symm
      change fderiv ℝ J y (u j) (Fin.tail (u ∘ σ)) = 0
      rw [hz]
      rfl
    let n : Fin (k + 1) → E := i ∘ p ∘ m
    have hn : B n = 0 := hf y hy (k + 1) hk (p ∘ m)
    have hs := B.toMultilinearMap.map_sub_map_piecewise m n Finset.univ
    change B m - B (Finset.univ.piecewise n m) = _ at hs
    have hsum : (∑ j ∈ Finset.univ, B.toMultilinearMap
        (fun l ↦ if l ∈ (Finset.univ : Finset (Fin (k+1))) → l < j then m l
          else if j = l then m l - n l else n l)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      apply hker _ j
      simp only [Finset.mem_univ, true_implies, lt_irrefl, ↓reduceIte, map_sub, n, comp_apply, hpi _,
        sub_self]
    rw [hsum] at hs
    simpa [Finset.piecewise, hn] using hs

/-- The distribution on a coordinate plane is determined by the pure
normal jets through its order. -/
theorem coordinatePlane_distribution_kills_vanishing_normal_jets
    (p : E →L[ℝ] D) (i : D →L[ℝ] E) (hpi : LeftInverse p i)
    (hp : ‖p‖ ≤ 1) (hi : ‖i‖ ≤ 1) (T : Tests E →L[ℂ] ℂ) (N : ℕ)
    (hT : testDistributionOrderLE T N)
    (hvan : Distribution.IsVanishingOn (⇑T) {y | p y = 0}ᶜ)
    (f : Tests E) (hf : ∀ y, p y = 0 → ∀ k ≤ N, ∀ m : Fin k → D,
      iteratedFDeriv ℝ k (f : E → ℂ) y (i ∘ m) = 0) :
    T f = 0 :=
  coordinatePlane_distribution_kills_vanishing_jets p i hpi hp hi T N hT hvan f
    (coordinatePlane_all_jets_zero_of_normal p i hpi f f.contDiff N hf)

/-- Matching normal jets give the same distribution value. -/
theorem coordinatePlane_distribution_eq_of_normal_jets
    (p : E →L[ℝ] D) (i : D →L[ℝ] E) (hpi : LeftInverse p i)
    (hp : ‖p‖ ≤ 1) (hi : ‖i‖ ≤ 1) (T : Tests E →L[ℂ] ℂ) (N : ℕ)
    (hT : testDistributionOrderLE T N)
    (hvan : Distribution.IsVanishingOn (⇑T) {y | p y = 0}ᶜ)
    (f g : Tests E) (h : ∀ y, p y = 0 → ∀ k ≤ N, ∀ m : Fin k → D,
      iteratedFDeriv ℝ k (f : E → ℂ) y (i ∘ m) =
        iteratedFDeriv ℝ k (g : E → ℂ) y (i ∘ m)) :
    T f = T g := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply coordinatePlane_distribution_kills_vanishing_normal_jets p i hpi hp hi T N hT hvan
  intro y hy k hk m
  change iteratedFDeriv ℝ k ((f : E → ℂ) - (g : E → ℂ)) y (i ∘ m) = 0
  have htop : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  rw [iteratedFDeriv_sub_apply (f.contDiff.of_le htop).contDiffAt
    (g.contDiff.of_le htop).contDiffAt]
  exact sub_eq_zero.mpr (h y hy k hk m)

/-- The coordinate-plane result on the product of normal and tangential
spaces, with the jet evaluated at `(0, y)`. -/
theorem productPlane_distribution_eq_of_normal_jets
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Tests (D × V) →L[ℂ] ℂ) (N : ℕ) (hT : testDistributionOrderLE T N)
    (hvan : Distribution.IsVanishingOn (⇑T) {x : D × V | x.1 = 0}ᶜ)
    (f g : Tests (D × V)) (h : ∀ (y : V) (k : ℕ), k ≤ N → ∀ m : Fin k → D,
      iteratedFDeriv ℝ k (f : D × V → ℂ) (0, y) (fun j ↦ (m j, 0)) =
        iteratedFDeriv ℝ k (g : D × V → ℂ) (0, y) (fun j ↦ (m j, 0))) :
    T f = T g := by
  let p := ContinuousLinearMap.fst ℝ D V
  let i := ContinuousLinearMap.inl ℝ D V
  have hpi : LeftInverse p i := fun _ ↦ rfl
  have hp : ‖p‖ ≤ 1 := p.opNorm_le_bound zero_le_one (fun x ↦ by
    change ‖x.1‖ ≤ 1 * ‖x‖
    rw [one_mul, Prod.norm_def]
    exact le_max_left _ _)
  have hi : ‖i‖ ≤ 1 := i.opNorm_le_bound zero_le_one (fun x ↦ by
    simp [i, Prod.norm_def])
  apply coordinatePlane_distribution_eq_of_normal_jets p i hpi hp hi T N hT hvan f g
  rintro ⟨x, y⟩ hx k hk m
  change x = 0 at hx
  subst x
  exact h y k hk m

end
end Masullo
