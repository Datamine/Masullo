import BergmanNormalizedJets

open Bornology Filter Function Set Topology
open scoped ENat

namespace Masullo

noncomputable section

private abbrev Bergman := SchwartzBergman (univ : Set ℝ)

private theorem entire_of_test (f : Bergman) : Differentiable ℂ f.val := by
  simpa only [preimage_univ, differentiableOn_univ] using f.property.2.1

private theorem test_of_entire_bounds {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hb : ∀ (a b : ℝ), a ≤ b → ∀ N : ℕ, ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖z ^ N * f z‖ ≤ C) :
    f ∈ schwartzBergmanSubmodule univ := by
  refine ⟨by simp, hf.differentiableOn, fun a b hab _ N ↦ ?_⟩
  obtain ⟨C, hC⟩ := hb a b hab N
  exact ⟨C, fun _ ⟨z, hz, he⟩ ↦ he ▸ hC z hz⟩

private theorem entireBergman_bound (f : Bergman) (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    ∃ C ≥ 0, ∀ z : ℂ, z.re ∈ Icc a b → ‖z ^ N * f.val z‖ ≤ C := by
  obtain ⟨C, hC⟩ := f.property.2.2 a b hab (subset_univ _) N
  exact ⟨max C 0, le_max_right _ _, fun z hz ↦ (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)⟩

private theorem order_centered (w z : ℂ) (n : ℕ) :
    analyticOrderAt (fun t : ℂ ↦ (t - w) ^ n) z = if z = w then (n : ℕ∞) else 0 := by
  by_cases h : z = w
  · rw [ite_eq_left h, h]
    exact analyticOrderAt_centeredMonomial
  · rw [ite_eq_right h]
    apply (show AnalyticAt ℂ (fun t : ℂ ↦ (t - w)^n) z by fun_prop).analyticOrderAt_eq_zero.mpr
    exact pow_ne_zero _ (sub_ne_zero.mpr h)

/-- Removing a finite zero from an entire Schwartz–Bergman test preserves
the full strip decay topology's membership conditions. -/
theorem exists_bergman_remove_zero (g : Bergman) (w : ℂ) (n : ℕ)
    (hn : analyticOrderAt g.val w = (n : ℕ∞)) :
    ∃ q : Bergman, q.val w ≠ 0 ∧ (∀ z, g.val z = (z - w) ^ n * q.val z) ∧
      ∀ z ≠ w, analyticOrderAt q.val z = analyticOrderAt g.val z := by
  have hp : Differentiable ℂ (fun z : ℂ ↦ (z - w) ^ n) := by fun_prop
  have hle (z : ℂ) :
      analyticOrderAt (fun t : ℂ ↦ (t - w) ^ n) z ≤ analyticOrderAt g.val z := by
    rw [order_centered]
    by_cases h : z = w
    · rw [ite_eq_left h, h, hn]
    · rw [ite_eq_right h]
      exact bot_le
  obtain ⟨k, hk, he⟩ := (entire_divisibility_iff_orders hp (entire_of_test g)).mpr hle
  have ho (z : ℂ) : analyticOrderAt g.val z =
      analyticOrderAt (fun t : ℂ ↦ (t - w) ^ n) z + analyticOrderAt k z := by
    rw [show g.val = (fun t : ℂ ↦ (t - w) ^ n) * k from funext he]
    exact analyticOrderAt_mul (hp.analyticAt z) (hk.analyticAt z)
  have hkw : k w ≠ 0 := by
    have h := ho w
    rw [hn, order_centered, ite_eq_left rfl] at h
    have hzero : analyticOrderAt k w = 0 := by
      apply (ENat.add_left_injective_of_ne_top (ENat.natCast_ne_top n))
      simpa [add_comm] using h.symm
    exact (hk.analyticAt w).analyticOrderAt_eq_zero.mp hzero
  have hmem := test_of_entire_bounds hk (by
    intro a b hab N
    obtain ⟨C, hC₀, hC⟩ := entireBergman_bound g a b hab N
    have hK : IsCompact (Metric.closedBall w 1) := isCompact_closedBall _ _
    obtain ⟨D, hD⟩ := (hK.image_of_continuousOn
      (((continuous_id.pow N).mul hk.continuous).norm.continuousOn)).bddAbove
    refine ⟨max C D, fun z hz ↦ ?_⟩
    by_cases hsmall : ‖z - w‖ ≤ 1
    · apply le_trans _ (le_max_right C D)
      exact hD ⟨z, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hsmall, rfl⟩
    · have hlarge : 1 ≤ ‖z - w‖ := le_of_lt (lt_of_not_ge hsmall)
      calc
        ‖z ^ N * k z‖ ≤ ‖(z - w) ^ n‖ * ‖z ^ N * k z‖ := by
          have hpow : 1 ≤ ‖(z - w) ^ n‖ := by rw [norm_pow]; exact one_le_pow₀ hlarge
          exact le_mul_of_one_le_left (norm_nonneg _) hpow
        _ = ‖z ^ N * g.val z‖ := by rw [← norm_mul, he z]; congr 1; ring
        _ ≤ max C D := (hC z hz).trans (le_max_left C D))
  refine ⟨⟨k, hmem⟩, hkw, he, fun z hz ↦ ?_⟩
  have h := ho z
  rw [order_centered, ite_eq_right hz, zero_add] at h
  exact h.symm

private def bergmanCenteredMultiply (w : ℂ) (k : ℕ) (q : Bergman) : Bergman := by
  refine ⟨fun z ↦ (z - w)^k * q.val z, test_of_entire_bounds (by
    have hq := entire_of_test q
    fun_prop) ?_⟩
  intro a b hab N
  obtain ⟨C, hC₀, hC⟩ := entireBergman_bound q a b hab N
  obtain ⟨D, hD₀, hD⟩ := entireBergman_bound q a b hab (N + k)
  refine ⟨(1 + ‖w‖)^k * max C D, fun z hz ↦ ?_⟩
  have hnorm := norm_sub_le z w
  by_cases h : ‖z‖ ≤ 1
  · have hp : ‖z - w‖ ^ k ≤ (1 + ‖w‖)^k := by
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans (add_le_add_left h _)) _
    rw [← mul_left_comm, norm_mul, norm_pow]
    exact mul_le_mul hp ((hC z hz).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  · have hz₁ : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge h)
    have hp : ‖z - w‖ ≤ (1 + ‖w‖) * ‖z‖ := by
      calc
        _ ≤ ‖z‖ + ‖w‖ := hnorm
        _ ≤ ‖z‖ + ‖w‖ * ‖z‖ :=
          add_le_add_right (le_mul_of_one_le_right (norm_nonneg _) hz₁) _
        _ = _ := by ring
    have hpk := pow_le_pow_left₀ (norm_nonneg _) hp k
    rw [← mul_left_comm, norm_mul, norm_pow]
    refine (mul_le_mul_of_nonneg_right hpk (norm_nonneg _)).trans ?_
    rw [mul_pow, mul_assoc, ← norm_pow, ← norm_mul, ← mul_assoc, ← pow_add]
    exact mul_le_mul_of_nonneg_left ((by simpa only [Nat.add_comm k N] using hD z hz : _ ≤ D).trans
      (le_max_right _ _)) (by positivity)

private theorem normalizedJet_zero_of_lt_order (f : Bergman) (z : ℂ) (j : ℕ)
    (h : (j : ℕ∞) < analyticOrderAt f.val z) : bergmanNormalizedJet z j f = 0 := by
  have h' : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f.val z := by
    rwa [Nat.cast_add, Nat.cast_one, ENat.add_one_le_iff (ENat.natCast_ne_top j)]
  rw [bergmanNormalizedJet_apply, (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((entire_of_test f).analyticAt z)).mp h' j (Nat.lt_succ_self j), mul_zero]

private theorem centeredMultiply_order (w z : ℂ) (j : ℕ) (f : Bergman) :
    analyticOrderAt (bergmanCenteredMultiply w j f).val z =
      (if z = w then (j : ℕ∞) else 0) + analyticOrderAt f.val z := by
  change analyticOrderAt ((fun t : ℂ ↦ (t - w)^j) * f.val) z = _
  rw [analyticOrderAt_mul (by fun_prop) ((entire_of_test f).analyticAt z), order_centered]

/-- A finite jet can be prescribed at one zero of an entire Schwartz–Bergman
divisor, while the test vanishes to the full divisor order at all other zeros. -/
theorem exists_bergman_divisor_local_interpolation (g : Bergman) (w : ℂ) (n : ℕ)
    (hn : analyticOrderAt g.val w = (n : ℕ∞)) (a : ℕ → ℂ) :
    ∃ f : Bergman,
      (∀ j < n, bergmanNormalizedJet w j f = a j) ∧
      (∀ z ≠ w, ∀ j : ℕ, (j : ℕ∞) < analyticOrderAt g.val z →
        bergmanNormalizedJet z j f = 0) := by
  obtain ⟨q, hqw, _, hq⟩ := exists_bergman_remove_zero g w n hn
  let P : Submodule ℂ Bergman :=
    ⨅ i : {i : ℂ × ℕ // i.1 ≠ w ∧ (i.2 : ℕ∞) < analyticOrderAt g.val i.1},
      (bergmanNormalizedJet i.val.1 i.val.2).ker
  let B (k : ℕ) := bergmanCenteredMultiply w k q
  have hord (k : ℕ) : analyticOrderAt (B k).val w = (k : ℕ∞) := by
    rw [centeredMultiply_order, ite_eq_left rfl,
      ((entire_of_test q).analyticAt w).analyticOrderAt_eq_zero.mpr hqw, add_zero]
  have hp (k : ℕ) : B k ∈ P := by
    apply (Submodule.mem_iInf _).mpr
    intro i
    apply normalizedJet_zero_of_lt_order
    rw [centeredMultiply_order, ite_eq_right i.property.1, zero_add, hq _ i.property.1]
    exact i.property.2
  have hd (k : ℕ) : bergmanNormalizedJet w k (B k) ≠ 0 := by
    rw [bergmanNormalizedJet_apply]
    apply mul_ne_zero (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero k))
    exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
      ((entire_of_test (B k)).analyticAt w)).mp (hord k)).2
  have hlow (j k : ℕ) (hj : j < k) : bergmanNormalizedJet w j (B k) = 0 :=
    normalizedJet_zero_of_lt_order _ _ _ (by rw [hord]; exact_mod_cast hj)
  have hsol (r : ℕ) : ∃ f ∈ P, ∀ j < r, bergmanNormalizedJet w j f = a j := by
    induction r with
    | zero => exact ⟨0, P.zero_mem, fun j hj ↦ (Nat.not_lt_zero j hj).elim⟩
    | succ r ih =>
      obtain ⟨f, hf, h⟩ := ih
      let c := (a r - bergmanNormalizedJet w r f) / bergmanNormalizedJet w r (B r)
      refine ⟨f + c • B r, P.add_mem hf (P.smul_mem c (hp r)), fun j hj ↦ ?_⟩
      rw [map_add, map_smul, smul_eq_mul]
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hj' | heq
      · rw [h j hj', hlow j r hj', mul_zero, add_zero]
      · subst j
        rw [show c * bergmanNormalizedJet w r (B r) =
          a r - bergmanNormalizedJet w r f from div_mul_cancel₀ _ (hd r)]
        abel
  obtain ⟨f, hf, h⟩ := hsol n
  exact ⟨f, h, fun z hz j hj ↦ ((Submodule.mem_iInf _).mp hf) ⟨(z, j), hz, hj⟩⟩

/-- Below a finite divisor order at one zero, the normalized jets admit
individual biorthogonal test vectors. -/
theorem bergmanDivisor_normalizedJet_biorthogonal (g : Bergman) (w : ℂ)
    (n k : ℕ) (hn : analyticOrderAt g.val w = (n : ℕ∞)) :
    ∃ f : Bergman, ∀ (z : ℂ) (j : ℕ), (j : ℕ∞) < analyticOrderAt g.val z →
      bergmanNormalizedJet z j f = if z = w ∧ j = k then 1 else 0 := by
  classical
  obtain ⟨f, hw, hother⟩ := exists_bergman_divisor_local_interpolation g w n hn
    (fun j ↦ if j = k then 1 else 0)
  refine ⟨f, fun z j hj ↦ ?_⟩
  by_cases hz : z = w
  · subst z
    rw [hn] at hj
    simpa using hw j (by exact_mod_cast hj)
  · simpa only [hz, false_and, ite_false] using hother z hz j hj

/-- A divisor with a Schwartz–Bergman representative of the same orders
has biorthogonal vectors for its continuous quotient jets on each closed strip. -/
theorem bergmanDivisor_quotientJets_biorthogonal (g : ℂ → ℂ) (q : Bergman)
    (hq : ∀ z, analyticOrderAt q.val z = analyticOrderAt g z)
    (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤) (a b : ℝ) (hab : a ≤ b) :
    let S : Set ({z : ℂ // z.re ∈ Icc a b} × ℕ) :=
      {i | (i.2 : ℕ∞) < analyticOrderAt g i.1}
    ∃ J : S → StrongDual ℂ (Bergman ⧸ bergmanDivisorSubmodule g),
      (∀ i f, J i ((bergmanDivisorSubmodule g).mkQ f) =
        bergmanNormalizedJet i.val.1 i.val.2 f) ∧
      Equicontinuous (fun i (f : Bergman ⧸ bergmanDivisorSubmodule g) ↦ J i f) ∧
      IsVonNBounded ℂ (range J) ∧
      ∀ i, ∃ x, ∀ j, J j x = if j = i then 1 else 0 := by
  classical
  intro S
  obtain ⟨J, hJ, hcont, hbounded⟩ := bergmanDivisor_normalizedJets g a b hab
  refine ⟨J, fun i f ↦ (hJ i f).trans (bergmanNormalizedJet_apply _ _ _).symm,
    hcont, hbounded, fun i ↦ ?_⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfinite i.val.1)
  obtain ⟨f, hf⟩ := bergmanDivisor_normalizedJet_biorthogonal q i.val.1 n i.val.2
    ((hq _).trans hn.symm)
  refine ⟨(bergmanDivisorSubmodule g).mkQ f, fun j ↦ ?_⟩
  rw [hJ, ← bergmanNormalizedJet_apply, hf _ _ (by rw [hq]; exact j.property)]
  have heq : ((j.val.1 : ℂ) = i.val.1 ∧ j.val.2 = i.val.2) ↔ j = i := by
    constructor
    · rintro ⟨hz, hj⟩
      exact Subtype.ext (Prod.ext (Subtype.ext hz) hj)
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp only [heq]

/-- For a finite divisor, the jet coordinates give a continuous linear
equivalence from the saturated divisor quotient onto the full space of its
Taylor data. In particular the inverse images of the coordinate vectors form
a finite basis carrying the quotient topology. -/
theorem exists_bergmanDivisor_finiteJetEquiv (g : Bergman)
    (hzeros : Set.Finite {z : ℂ | g.val z = 0}) :
    let I : Set (ℂ × ℕ) := {i | (i.2 : ℕ∞) < analyticOrderAt g.val i.1}
    let D := bergmanDivisorSubmodule g.val
    ∃ e : (Bergman ⧸ D) ≃L[ℂ] (I → ℂ),
      ∀ f i, e (D.mkQ f) i = bergmanNormalizedJet i.val.1 i.val.2 f := by
  classical
  intro I D
  have hg (z : ℂ) : AnalyticAt ℂ g.val z := (entire_of_test g).analyticAt z
  obtain ⟨w, hw⟩ : ∃ w : ℂ, g.val w ≠ 0 := by
    by_contra! hn
    have he : {z : ℂ | g.val z = 0} = univ := Set.eq_univ_of_forall hn
    exact Set.infinite_univ (he ▸ hzeros)
  have hfinite (z : ℂ) : analyticOrderAt g.val z ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (fun z _ ↦ hg z)
      isPreconnected_univ (mem_univ w) (mem_univ z) (by
        rw [(hg w).analyticOrderAt_eq_zero.mpr hw]
        exact ENat.zero_ne_top)
  let Z := {z : ℂ | g.val z = 0}
  letI : Fintype Z := hzeros.fintype
  choose n hn using fun z : Z ↦ ENat.ne_top_iff_exists.mp (hfinite z.val)
  have hz (i : I) : g.val i.val.1 = 0 :=
    ((hg i.val.1).analyticOrderAt_ne_zero.mp
      (ne_of_gt ((bot_le : (0 : ℕ∞) ≤ (i.val.2 : ℕ∞)).trans_lt i.property)))
  let k (i : I) : Z := ⟨i.val.1, hz i⟩
  have hk (i : I) : i.val.2 < n (k i) := by
    have hi := i.property
    change (i.val.2 : ℕ∞) < analyticOrderAt g.val (k i).val at hi
    rw [← hn (k i)] at hi
    exact_mod_cast hi
  let j (i : I) : (z : Z) × Fin (n z) := ⟨k i, ⟨i.val.2, hk i⟩⟩
  have hj : Injective j := by
    intro i i' he
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p : (z : Z) × Fin (n z) ↦ p.1.val) he)
      (congrArg (fun p : (z : Z) × Fin (n z) ↦ p.2.val) he)
  letI : Finite I := Finite.of_injective j hj
  letI : Fintype I := Fintype.ofFinite I
  have h (i : I) :
      ∃ f : Bergman, ∀ j : I, bergmanNormalizedJet j.val.1 j.val.2 f = if j = i then 1 else 0 := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfinite i.val.1)
    obtain ⟨f, hf⟩ := bergmanDivisor_normalizedJet_biorthogonal g i.val.1 n i.val.2 hn.symm
    refine ⟨f, fun j ↦ ?_⟩
    rw [hf _ _ j.property]
    have he : (j.val.1 = i.val.1 ∧ j.val.2 = i.val.2) ↔ j = i :=
      ⟨fun h ↦ Subtype.ext (Prod.ext h.1 h.2), fun h ↦ h ▸ ⟨rfl, rfl⟩⟩
    simp only [he]
  choose f hf using h
  let J₀ (i : I) : (Bergman ⧸ D) →L[ℂ] ℂ :=
    D.liftQL (bergmanNormalizedJet i.val.1 i.val.2)
      (iInf_le (fun j : I ↦ (bergmanNormalizedJet j.val.1 j.val.2).ker) i)
  let J := ContinuousLinearMap.pi J₀
  have hJ (u : Bergman) (i : I) :
      J (D.mkQ u) i = bergmanNormalizedJet i.val.1 i.val.2 u := rfl
  have hJinj : Injective J := by
    apply (injective_iff_map_eq_zero J).mpr
    intro u hu
    obtain ⟨f, rfl⟩ := D.mkQ_surjective u
    apply (Submodule.Quotient.mk_eq_zero D).mpr
    change f ∈ bergmanDivisorSubmodule g.val
    simp only [bergmanDivisorSubmodule, Submodule.mem_iInf]
    intro i
    change bergmanNormalizedJet i.val.1 i.val.2 f = 0
    exact (hJ f i).symm.trans (congrFun hu i)
  obtain ⟨ha, hp, _, _⟩ := schwartzBergman_frechet univ isOpen_univ ordConnected_univ univ_nonempty
  letI : IsTopologicalAddGroup Bergman := ha
  letI : PolynormableSpace ℂ Bergman := hp
  letI : ContinuousSMul ℂ Bergman := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
  let L : (I → ℂ) →L[ℂ] Bergman :=
    ∑ i : I, (ContinuousLinearMap.proj i).smulRight (f i)
  let U := D.mkQL.comp L
  have hJU (c : I → ℂ) : J (U c) = c := by
    funext i
    change J (D.mkQ (L c)) i = c i
    rw [hJ]
    simp [L, hf]
  exact ⟨ContinuousLinearEquiv.equivOfInverse J U
    (fun u ↦ hJinj (hJU (J u))) hJU, hJ⟩

end

end Masullo
