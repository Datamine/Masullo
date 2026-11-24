import SUnitCounting
import SLocalBruhatProjections
import SLocalCharacterRestriction
import Mathlib.Analysis.SpecialFunctions.Exp

open Bornology Filter Function IsDedekindDomain NumberField Set Topology
open scoped Classical NumberField NNReal SchwartzMap

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev U := Additive (sIntegerRing F S)ˣ
private abbrev degree := Fintype.card (SLogIndex F S) - 1

/-- A support cutoff linear in the shell number and exponential decay within
each shell give an absolutely summable orbit bound of degree `|S| - 1`. -/
private theorem sUnitShell_bound (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Idele F), g ∈ sIdeleBlock F S →
      ∀ (k : U F S → ℕ) (term : U F S → ℝ) (A : ℝ), 0 ≤ A →
      (∀ u, 0 ≤ term u) →
      (∀ u, term u ≤ A * Real.exp (-(k u : ℝ))) →
      (∀ u, term u ≠ 0 → u ∈ sUnitLogBox F S g (H + 2 * ((k u : ℝ) + 1))) →
      Summable term ∧ ∑' u, term u ≤ C * A * (1 + |Real.log (ideleNorm F g)|) ^ degree F S := by
  obtain ⟨D, hD, hcount⟩ := sUnitLogBox_count F S
  let n : ℝ := Fintype.card (SLogIndex F S)
  let d := degree F S
  let K := 1 + (n + 1) * (H + 2)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let m (j : ℕ) := ((j : ℝ) + 1) ^ d * Real.exp (-(j : ℝ))
  have hm₀ (j : ℕ) : 0 ≤ m j := by dsimp [m]; positivity
  have hm : Summable m := by
    let a (j : ℕ) := (j : ℝ) ^ d * Real.exp (-(j : ℝ))
    have ha : Summable a := by
      simpa [a] using Real.summable_pow_mul_exp_neg_nat_mul d (r := 1) one_pos
    have hs := ((summable_nat_add_iff (f := a) 1).mpr ha).mul_left (Real.exp 1)
    have he (j : ℕ) : Real.exp 1 * a (j + 1) = m j := by
      dsimp [a, m]
      rw [Nat.cast_add, Nat.cast_one, mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    simpa only [he] using hs
  refine ⟨D * K ^ d * ∑' j, m j,
    mul_nonneg (by positivity) (tsum_nonneg hm₀), ?_⟩
  intro g hg k term A hA hterm₀ hterm hsupp
  let L := 1 + |Real.log (ideleNorm F g)|
  have hL : 1 ≤ L := le_add_of_nonneg_right (abs_nonneg _)
  let r (j : ℕ) := H + 2 * ((j : ℝ) + 1)
  have hr (j : ℕ) : 0 ≤ r j := by dsimp [r]; positivity
  let P (j : ℕ) := sUnitLogBox F S g (r j)
  have hP (j : ℕ) : (P j).Finite ∧ ((P j).ncard : ℝ) ≤ D * (L + (n + 1) * r j) ^ d :=
    hcount g hg (r j) (hr j)
  let M := D * K ^ d * A * L ^ d
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hweight (j : ℕ) :
      ((P j).ncard : ℝ) * (A * Real.exp (-(j : ℝ))) ≤ M * m j := by
    have hj : 1 ≤ (j : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg j)
    have hbase : L + (n + 1) * r j ≤ L * (K * ((j : ℝ) + 1)) := calc
      _ ≤ L * (1 + (n + 1) * r j) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hL) (mul_nonneg (by positivity : 0 ≤ n + 1) (hr j))]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hL)
        have hh : r j ≤ (H + 2) * ((j : ℝ) + 1) := by
          dsimp [r]
          nlinarith [mul_nonneg hH (Nat.cast_nonneg (α := ℝ) j)]
        dsimp only [K]
        calc
          _ ≤ ((j : ℝ) + 1) + (n + 1) * ((H + 2) * ((j : ℝ) + 1)) :=
            add_le_add hj (mul_le_mul_of_nonneg_left hh (by positivity))
          _ = _ := by ring
    calc
      _ ≤ D * (L + (n + 1) * r j) ^ d * (A * Real.exp (-(j : ℝ))) :=
        mul_le_mul_of_nonneg_right (hP j).2 (by positivity)
      _ ≤ D * (L * (K * ((j : ℝ) + 1))) ^ d * (A * Real.exp (-(j : ℝ))) := by
        gcongr
      _ = _ := by dsimp [M, m]; rw [mul_pow, mul_pow]; ring
  have hfinite (t : Finset (U F S)) : ∑ u ∈ t, term u ≤ ∑' j, M * m j := by
    let s := t.filter (fun u => term u ≠ 0)
    have hsum : ∑ u ∈ s, term u = ∑ u ∈ t, term u :=
      Finset.sum_subset (Finset.filter_subset _ _) (fun u hu hn =>
        not_ne_iff.mp (fun h => hn (Finset.mem_filter.mpr ⟨hu, h⟩)))
    refine hsum.ge.trans ((Finset.sum_fiberwise_of_maps_to (g := k) (s := s) (t := s.image k)
      (fun u hu => Finset.mem_image_of_mem k hu) term).ge.trans ?_)
    refine (Finset.sum_le_sum (fun j _ => ?_)).trans
      ((hm.mul_left M).sum_le_tsum (s.image k) (fun j _ => mul_nonneg hM (hm₀ j)))
    have hsub : s.filter (fun u => k u = j) ⊆ (hP j).1.toFinset := by
      intro u hu
      obtain ⟨hu, hk⟩ := Finset.mem_filter.mp hu
      exact (hP j).1.mem_toFinset.mpr (hk ▸ hsupp u (Finset.mem_filter.mp hu).2)
    calc
      _ ≤ ∑ u ∈ s with k u = j, A * Real.exp (-(j : ℝ)) :=
        Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2 ▸ hterm u
      _ ≤ ((P j).ncard : ℝ) * (A * Real.exp (-(j : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ (hP j).1]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
      _ ≤ _ := hweight j
  have hs := summable_of_sum_le hterm₀ hfinite
  refine ⟨hs, (hs.tsum_le_of_sum_le hfinite).trans_eq ?_⟩
  rw [tsum_mul_left]
  dsimp [M]
  ring

/-- The positive Archimedean weight controlling all coordinates of the orbit. -/
def sThetaArchWeight (x : InfiniteAdeleRing F) : ℝ :=
  max 1 (∑ v : InfinitePlace F, ‖x v‖)

/-- On bounded finite coordinates the modulus is controlled by a power of the
Archimedean weight, with the usual multiplicities at the infinite places. -/
theorem sLocalIdeleNorm_le_archWeight (g : (SAdeles F S)ˣ) (H : ℝ)
    (hfinite : ∀ v : S, ‖g.val.2 v‖ ≤ H) :
    sLocalIdeleNorm F S g ≤ (1 + H) ^ S.card *
      sThetaArchWeight F g.val.1 ^ (∑ v : InfinitePlace F, v.mult) := by
  let a := (sLocalEmbed F S g).val
  have hs : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => ‖a.val.2 v‖) ⊆ (S : Set _) := by
    intro v hv
    by_contra h
    apply hv
    have ho := (sIdeleBlock_mem_iff F S a).mp (sLocalEmbed F S g).property v h
    change ‖a.val.2 v‖ = 1
    rw [FinitePlace.norm_def, (ideleOrder_eq_zero_iff F a v).mp ho]
    simp
  let y := sThetaArchWeight F g.val.1
  have hy : 0 ≤ y := zero_le_one.trans (le_max_left _ _)
  have ha (v : InfinitePlace F) : ‖a.val.1 v‖ ≤ y := by
    rw [sLocalEmbed_arch F S g]
    exact (Finset.single_le_sum (fun w _ => norm_nonneg (g.val.1 w))
      (Finset.mem_univ v)).trans (le_max_right _ _)
  have hb : (∏ v ∈ S, ‖a.val.2 v‖) ≤ (1 + H) ^ S.card := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    intro v hv
    rw [sLocalEmbed_finite F S g ⟨v, hv⟩]
    exact (hfinite ⟨v, hv⟩).trans (le_add_of_nonneg_left zero_le_one)
  have hprod : (∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) ≤ y ^ (∑ v : InfinitePlace F, v.mult) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun _ _ => by positivity) (fun v _ =>
      pow_le_pow_left₀ (norm_nonneg _) (ha v) _)
  change (∏ v : InfinitePlace F, ‖a.val.1 v‖ ^ v.mult) * (∏ᶠ v, ‖a.val.2 v‖) ≤ _
  rw [finprod_eq_prod_of_mulSupport_subset _ hs, mul_comm ((1 + H) ^ S.card)]
  exact mul_le_mul hprod hb (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (pow_nonneg hy _)

/-- The actual S-unit orbit series before descent to the S-idele quotient. -/
def sLocalThetaOnIdeles (f : SAdeles F S → ℂ) (g : (SAdeles F S)ˣ) : ℂ :=
  ∑' u : U F S, f (sIntegerDiagonal F S u.toMul.val * g.val)

/-- The all-number-field orbit estimate for tests with a common bound on
the finite support and a common first weighted Archimedean supremum. -/
private theorem sLocalTheta_abs_log_envelope (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SAdeles F S → ℂ) (A : ℝ), 0 ≤ A →
      (∀ x, f x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H) →
      (∀ x, ‖f x‖ * sThetaArchWeight F x.1 ≤ A) →
      ∀ g : (SAdeles F S)ˣ,
        Summable (fun u : U F S => ‖f (sIntegerDiagonal F S u.toMul.val * g.val)‖) ∧
        (∑' u : U F S, ‖f (sIntegerDiagonal F S u.toMul.val * g.val)‖) ≤
          C * A * (1 + |Real.log (sLocalIdeleNorm F S g)|) ^ degree F S := by
  obtain ⟨C, hC, hshell⟩ := sUnitShell_bound F S H hH
  refine ⟨C, hC, fun f A hA hsupp hbound g => ?_⟩
  let a := (sLocalEmbed F S g).val
  let z (u : U F S) := principalIdele F (sUnitToField F S u.toMul) * a
  let x (u : U F S) := sIntegerDiagonal F S u.toMul.val * g.val
  have hx (u : U F S) : sAdelesProjection F S (z u).val = x u := by
    change sAdelesProjection F S ((principalIdele F (sUnitToField F S u.toMul)).val * a.val) = _
    rw [map_mul, show sAdelesProjection F S a.val = g.val from sLocalEmbed_project F S g]
    rfl
  let y (u : U F S) := sThetaArchWeight F (x u).1
  have hy (u : U F S) : 1 ≤ y u := le_max_left _ _
  have hypos (u : U F S) : 0 < y u := zero_lt_one.trans_le (hy u)
  let k (u : U F S) := ⌊Real.log (y u)⌋₊
  let term (u : U F S) := ‖f (x u)‖
  have ht (u : U F S) : term u ≤ A * Real.exp (-(k u : ℝ)) := by
    have hk : (k u : ℝ) ≤ Real.log (y u) := Nat.floor_le (Real.log_nonneg (hy u))
    calc
      _ ≤ A / y u := (le_div_iff₀ (hypos u)).mpr (hbound (x u))
      _ = A * Real.exp (-Real.log (y u)) := by
        rw [Real.exp_neg, Real.exp_log (hypos u), div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hk)) hA
  have hs (u : U F S) (hu : term u ≠ 0) :
      u ∈ sUnitLogBox F S a (H + 2 * ((k u : ℝ) + 1)) := by
    have hf : f (x u) ≠ 0 := fun h => hu (norm_eq_zero.mpr h)
    intro v
    cases v with
    | inl v =>
      change (v.mult : ℝ) * Real.log ‖(z u).val.1 v‖ ≤ _
      have hv : (z u).val.1 v = (x u).1 v :=
        congrArg (fun p : SAdeles F S => p.1 v) (hx u)
      rw [hv]
      have hy' : ‖(x u).1 v‖ ≤ y u :=
        (Finset.single_le_sum (fun w _ => norm_nonneg ((x u).1 w))
          (Finset.mem_univ v)).trans (le_max_right _ _)
      have hlog : Real.log ‖(x u).1 v‖ ≤ Real.log (y u) := by
        by_cases h : (x u).1 v = 0
        · simpa [h] using Real.log_nonneg (hy u)
        · exact Real.log_le_log (norm_pos_iff.mpr h) hy'
      have hmult : (v.mult : ℝ) ≤ 2 := by
        by_cases h : v.IsReal
        · simp [h.mult_eq_one]
        · simp [(InfinitePlace.not_isReal_iff_isComplex.mp h).mult_eq_two]
      have hk : Real.log (y u) ≤ (k u : ℝ) + 1 := (Nat.lt_floor_add_one _).le
      have hmul := mul_le_mul (hlog.trans hk) hmult
        (Nat.cast_nonneg (α := ℝ) v.mult) (by positivity : 0 ≤ (k u : ℝ) + 1)
      linarith
    | inr v =>
      change Real.log ‖(z u).val.2 v.val‖ ≤ _
      have hv : (z u).val.2 v.val = (x u).2 v :=
        congrArg (fun p : SAdeles F S => p.2 v) (hx u)
      rw [hv]
      exact ((Real.log_le_self (norm_nonneg _)).trans (hsupp (x u) hf v)).trans
        (le_add_of_nonneg_right (by positivity))
  obtain ⟨habs, hsum⟩ := hshell a (sLocalEmbed F S g).property k term A hA
    (fun _ => norm_nonneg _) ht hs
  exact ⟨habs, hsum⟩

/-- The all-number-field orbit estimate for tests with a common bound on
the finite support and a common first weighted Archimedean supremum. -/
theorem sLocalTheta_log_bound (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SAdeles F S → ℂ) (A : ℝ), 0 ≤ A →
      (∀ x, f x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H) →
      (∀ x, ‖f x‖ * sThetaArchWeight F x.1 ≤ A) →
      ∀ g : (SAdeles F S)ˣ,
        Summable (fun u : U F S => ‖f (sIntegerDiagonal F S u.toMul.val * g.val)‖) ∧
        ‖sLocalThetaOnIdeles F S f g‖ ≤
          C * A * (1 + |Real.log (sLocalIdeleNorm F S g)|) ^ degree F S := by
  obtain ⟨C, hC, h⟩ := sLocalTheta_abs_log_envelope F S H hH
  refine ⟨C, hC, fun f A hA hs ht g => ?_⟩
  obtain ⟨habs, hb⟩ := h f A hA hs ht g
  exact ⟨habs, (norm_tsum_le_tsum_norm habs).trans hb⟩

private theorem sThetaArchWeight_le (x : InfiniteAdeleRing F) :
    sThetaArchWeight F x ≤
      1 + (Fintype.card (InfinitePlace F) : ℝ) * ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  let arch := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have hc (v : InfinitePlace F) : ‖x v‖ ≤ ‖arch x‖ := by
    rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
    apply Finset.le_sup'_of_le _ (Finset.mem_univ v)
    by_cases hv : v.IsReal
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hv, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
        (map_zero _) _).symm.le
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      exact ((InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
        (map_zero _) _).symm.le
  apply max_le
  · exact le_add_of_nonneg_right (by positivity)
  · have hh : ∑ v : InfinitePlace F, ‖x v‖ ≤ ∑ _ : InfinitePlace F, ‖arch x‖ :=
      Finset.sum_le_sum fun v _ => hc v
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    exact hh.trans (le_add_of_nonneg_left zero_le_one)

private abbrev Arch := mixedEmbedding.mixedSpace F

private def thetaSchwartzSeminorm (k : ℕ) : Seminorm ℂ (𝓢(Arch F, ℂ)) :=
  let c : NNReal := 1 + (Fintype.card (InfinitePlace F) : NNReal)
  c ^ k • (SchwartzMap.seminorm ℂ 0 0 + SchwartzMap.seminorm ℂ k 0)

private theorem thetaSchwartzSeminorm_continuous (k : ℕ) :
    Continuous (thetaSchwartzSeminorm F k) :=
  continuous_const.mul (((schwartz_withSeminorms ℂ (Arch F) ℂ).continuous_seminorm (0, 0)).add
    ((schwartz_withSeminorms ℂ (Arch F) ℂ).continuous_seminorm (k, 0)))

private theorem thetaSchwartzSeminorm_bound (k : ℕ) (φ : 𝓢(Arch F, ℂ))
    (x : InfiniteAdeleRing F) :
    ‖φ (InfiniteAdeleRing.ringEquiv_mixedSpace F x)‖ * sThetaArchWeight F x ^ k ≤
      thetaSchwartzSeminorm F k φ := by
  let w := InfiniteAdeleRing.ringEquiv_mixedSpace F x
  let c : ℝ := 1 + Fintype.card (InfinitePlace F)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hw : sThetaArchWeight F x ≤ c * max 1 ‖w‖ := calc
    _ ≤ 1 + (Fintype.card (InfinitePlace F) : ℝ) * ‖w‖ := sThetaArchWeight_le F x
    _ ≤ max 1 ‖w‖ + (Fintype.card (InfinitePlace F) : ℝ) * max 1 ‖w‖ :=
      add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _))
    _ = _ := by dsimp [c]; ring
  have hnonneg : 0 ≤ sThetaArchWeight F x := zero_le_one.trans (le_max_left _ _)
  calc
    _ ≤ ‖φ w‖ * (c * max 1 ‖w‖) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hw _) (norm_nonneg _)
    _ = c ^ k * (max 1 ‖w‖ ^ k * ‖φ w‖) := by rw [mul_pow]; ring
    _ ≤ _ := by
      change _ ≤ c ^ k * (SchwartzMap.seminorm ℂ 0 0 φ + SchwartzMap.seminorm ℂ k 0 φ)
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc _)
      by_cases h : ‖w‖ ≤ 1
      · rw [max_eq_left h, one_pow, one_mul]
        exact (SchwartzMap.norm_le_seminorm ℂ φ w).trans (le_add_of_nonneg_right (apply_nonneg _ _))
      · rw [max_eq_right (le_of_not_ge h)]
        exact (SchwartzMap.norm_pow_mul_le_seminorm ℂ φ k w).trans
          (le_add_of_nonneg_left (apply_nonneg _ _))

private theorem sLocalTheta_pure_envelope (k : ℕ) (ψ : FiniteBruhat F) :
    ∃ H B : ℝ, 0 ≤ H ∧ 0 ≤ B ∧
      ∀ φ : 𝓢(Arch F, ℂ),
        let f := sLocalBruhatRestriction F S (GlobalBruhat.pure F ψ φ)
        (∀ x, f x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H) ∧
          ∀ x, ‖f x‖ * sThetaArchWeight F x.1 ^ k ≤ B * thetaSchwartzSeminorm F k φ := by
  let p := restrictFiniteBruhat F S ψ
  have hcont := p.property.1.continuous
  have hK := p.property.2
  have hcoord (v : S) : ∃ R : ℝ, ∀ y ∈ tsupport p.val, ‖y v‖ ≤ R :=
    hK.exists_bound_of_continuousOn (continuous_apply v).continuousOn
  let R (v : S) := (hcoord v).choose
  let H := ∑ v : S, max 0 (R v)
  have hH : 0 ≤ H := Finset.sum_nonneg fun _ _ => le_max_left _ _
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hψ (y : (v : S) → v.val.adicCompletion F) : ‖p.val y‖ ≤ B := by
    by_cases hy : y ∈ tsupport p.val
    · exact (hB₀ y hy).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact hB
  refine ⟨H, B, hH, hB, fun φ => ?_⟩
  simp only [sLocalBruhatRestriction_pure]
  refine ⟨fun x hx v => ?_, fun x => ?_⟩
  · have hy : x.2 ∈ tsupport p.val := subset_tsupport p.val
      (fun h => hx (by change φ _ * p.val x.2 = 0; rw [h, mul_zero]))
    have hv : ‖x.2 v‖ ≤ R v := (hcoord v).choose_spec _ hy
    exact (hv.trans (le_max_right (0 : ℝ) _)).trans
      (Finset.single_le_sum (f := fun w => max 0 (R w)) (fun _ _ => le_max_left _ _) (Finset.mem_univ v))
  · let w := InfiniteAdeleRing.ringEquiv_mixedSpace F x.1
    have hw := thetaSchwartzSeminorm_bound F k φ x.1
    change ‖φ w * p.val x.2‖ * sThetaArchWeight F x.1 ^ k ≤ _
    rw [norm_mul, mul_comm ‖φ w‖, mul_assoc]
    exact mul_le_mul (hψ x.2) hw (mul_nonneg (norm_nonneg _)
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) hB

private theorem sLocalTheta_envelope (k : ℕ) (g : GlobalBruhat F) :
    ∃ H A : ℝ, 0 ≤ H ∧ 0 ≤ A ∧
      let f := sLocalBruhatRestriction F S g
      (∀ x, f x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H) ∧
        ∀ x, ‖f x‖ * sThetaArchWeight F x.1 ^ k ≤ A := by
  let P (g : GlobalBruhat F) :=
    ∃ H A : ℝ, 0 ≤ H ∧ 0 ≤ A ∧
      (∀ x, sLocalBruhatRestriction F S g x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H) ∧
        ∀ x, ‖sLocalBruhatRestriction F S g x‖ * sThetaArchWeight F x.1 ^ k ≤ A
  change P g
  let e := GlobalBruhat.algebraicEquiv F
  have h : ∀ f (hf : f ∈ bruhatSubmodule F), P (e.symm ⟨f, hf⟩) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, ψ, rfl⟩ := hf
      obtain ⟨H, B, hH, hB, hp⟩ := sLocalTheta_pure_envelope F S k ψ
      exact ⟨H, B * thetaSchwartzSeminorm F k φ, hH, mul_nonneg hB (apply_nonneg _ _), hp φ⟩
    | zero =>
      change P (e.symm 0)
      rw [map_zero]
      exact ⟨0, 0, le_rfl, le_rfl, by simp, by simp⟩
    | add f₁ f₂ hf₁ hf₂ h₁ h₂ =>
      change P (e.symm (⟨f₁, hf₁⟩ + ⟨f₂, hf₂⟩))
      rw [map_add]
      obtain ⟨H₁, A₁, hH₁, hA₁, hs₁, hb₁⟩ := h₁
      obtain ⟨H₂, A₂, _, hA₂, hs₂, hb₂⟩ := h₂
      refine ⟨max H₁ H₂, A₁ + A₂, hH₁.trans (le_max_left _ _), add_nonneg hA₁ hA₂, ?_, ?_⟩
      · intro x hx v
        simp only [map_add, Pi.add_apply] at hx
        by_cases h : sLocalBruhatRestriction F S (e.symm ⟨f₁, hf₁⟩) x = 0
        · rw [h, zero_add] at hx
          exact (hs₂ x hx v).trans (le_max_right _ _)
        · exact (hs₁ x h v).trans (le_max_left _ _)
      · intro x
        simp only [map_add, Pi.add_apply]
        refine (mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)).trans ?_
        rw [add_mul]
        exact add_le_add (hb₁ x) (hb₂ x)
    | smul c f hf h =>
      change P (e.symm (c • ⟨f, hf⟩))
      rw [map_smul]
      obtain ⟨H, A, hH, hA, hs, hb⟩ := h
      refine ⟨H, ‖c‖ * A, hH, mul_nonneg (norm_nonneg _) hA, ?_, ?_⟩
      · intro x hx
        exact hs x (fun h₀ => hx (by simp [h₀]))
      · intro x
        simp only [map_smul, Pi.smul_apply, norm_smul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
  have hfinal := h (e g).val (e g).property
  change P (e.symm (e g)) at hfinal
  rwa [LinearEquiv.symm_apply_apply] at hfinal

/-- Absolute convergence of the S-local theta series on the actual test space. -/
theorem sLocalTheta_restriction_summable (f : GlobalBruhat F) (g : (SAdeles F S)ˣ) :
    Summable (fun u : U F S => ‖sLocalBruhatRestriction F S f
      (sIntegerDiagonal F S u.toMul.val * g.val)‖) := by
  obtain ⟨H, A, hH, hA, hs, hb⟩ := sLocalTheta_envelope F S 1 f
  obtain ⟨_, _, h⟩ := sLocalTheta_log_bound F S H hH
  exact (h _ A hA hs (by simpa only [pow_one] using hb) g).1

/-- Evaluation of the S-local theta series as a linear functional of the test. -/
def sLocalThetaEval (g : (SAdeles F S)ˣ) : GlobalBruhat F →ₗ[ℂ] ℂ where
  toFun f := sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f) g
  map_add' f h := by
    unfold sLocalThetaOnIdeles
    simp only [map_add, Pi.add_apply]
    exact ((sLocalTheta_restriction_summable F S f g).of_norm).tsum_add
      ((sLocalTheta_restriction_summable F S h g).of_norm)
  map_smul' c f := by
    unfold sLocalThetaOnIdeles
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul, tsum_mul_left]

private abbrev thetaLogWeight (g : (SAdeles F S)ˣ) : ℝ :=
  (1 + |Real.log (sLocalIdeleNorm F S g)|) ^ degree F S

private theorem sLocalTheta_weight_seminorm (k : ℕ) (w : (SAdeles F S)ˣ → NNReal)
    (hestimate : ∀ H : ℝ, 0 ≤ H → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : SAdeles F S → ℂ) (A : ℝ), 0 ≤ A →
      (∀ x, f x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H) →
      (∀ x, ‖f x‖ * sThetaArchWeight F x.1 ^ k ≤ A) →
      ∀ g, (w g : ℝ) * ‖sLocalThetaOnIdeles F S f g‖ ≤ C * A)
    : ∃ p : Seminorm ℂ (sLocalBruhatImage F S), Continuous p ∧ ∀ f g,
      (w g : ℝ) * ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖ ≤ p f := by
  let p (g : (SAdeles F S)ˣ) : Seminorm ℂ (GlobalBruhat F) :=
    w g • (normSeminorm ℂ ℂ).comp (sLocalThetaEval F S g)
  have hp : BddAbove (range p) := Seminorm.bddAbove_range_iff.mpr fun f => by
    obtain ⟨H, A, hH, hA, hs, hb⟩ := sLocalTheta_envelope F S k f
    obtain ⟨C, _, h⟩ := hestimate H hH
    exact ⟨C * A, Set.forall_mem_range.mpr (h _ A hA hs hb)⟩
  let q : Seminorm ℂ (GlobalBruhat F) := ⨆ g, p g
  have hq : Continuous q := by
    apply GlobalBruhat.continuous_seminorm_of_pure F
    intro ψ
    obtain ⟨H, B₀, hH, hB₀, hs⟩ := sLocalTheta_pure_envelope F S k ψ
    obtain ⟨C, hC, hb⟩ := hestimate H hH
    let c : NNReal := ⟨C * B₀, mul_nonneg hC hB₀⟩
    let q' : Seminorm ℂ (𝓢(Arch F, ℂ)) := c • thetaSchwartzSeminorm F k
    have hc : Continuous q' := continuous_const.mul (thetaSchwartzSeminorm_continuous F k)
    apply Seminorm.continuous_of_le (p := q.comp (GlobalBruhat.pure F ψ)) hc
    intro φ
    change q (GlobalBruhat.pure F ψ φ) ≤ (C * B₀) * thetaSchwartzSeminorm F k φ
    refine (Seminorm.iSup_apply hp).trans_le (ciSup_le fun g => ?_)
    rw [mul_assoc C B₀]
    exact hb _ _ (mul_nonneg hB₀ (apply_nonneg _ _)) (hs φ).1 (hs φ).2 g
  exact ⟨q.comp (sLocalBruhatImage F S).subtype, hq.comp continuous_subtype_val,
    fun f g => (le_ciSup hp g) f.val⟩

/-- The logarithmic orbit estimate with a continuous seminorm on the tests. -/
theorem sLocalTheta_log_seminorm :
    ∃ p : Seminorm ℂ (sLocalBruhatImage F S), Continuous p ∧ ∀ f g,
      ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖ ≤
        p f * thetaLogWeight F S g := by
  let w (g : (SAdeles F S)ˣ) : NNReal :=
    ⟨(thetaLogWeight F S g)⁻¹, inv_nonneg.mpr (by positivity)⟩
  obtain ⟨p, hp, hb⟩ := sLocalTheta_weight_seminorm F S 1 w (by
    intro H hH
    obtain ⟨C, hC, h⟩ := sLocalTheta_log_bound F S H hH
    refine ⟨C, hC, fun f A hA hs hbound g => ?_⟩
    change (thetaLogWeight F S g)⁻¹ * ‖sLocalThetaOnIdeles F S f g‖ ≤ C * A
    rw [inv_mul_le_iff₀ (by positivity)]
    simpa only [mul_comm (thetaLogWeight F S g)] using
      (h f A hA hs (by simpa only [pow_one] using hbound) g).2)
  refine ⟨p, hp, fun f g => ?_⟩
  have h := hb f g
  change (thetaLogWeight F S g)⁻¹ * ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖ ≤ p f at h
  rwa [inv_mul_le_iff₀ (by positivity), mul_comm (thetaLogWeight F S g)] at h

/-- Theorem 2.4.2.1. The logarithmic theta estimate is uniform on bounded
families of S-local Schwartz–Bruhat tests in their actual locally convex topology. -/
theorem sLocalTheta_log_bounded (B : Set (sLocalBruhatImage F S)) (hB : IsVonNBounded ℂ B) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g : (SAdeles F S)ˣ,
      sLocalIdeleNorm F S g < 1 →
      ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖ ≤
        C₁ * |Real.log (sLocalIdeleNorm F S g)| ^
          (Fintype.card (InfinitePlace F) + S.card - 1) + C₂ := by
  obtain ⟨p, hp, hb⟩ := sLocalTheta_log_seminorm F S
  have hW := PolynormableSpace.withSeminorms ℂ (sLocalBruhatImage F S)
  obtain ⟨M, hM, hMb⟩ := hW.isVonNBounded_iff_seminorm_bounded.mp hB ⟨p, hp⟩
  let d := degree F S
  refine ⟨M * 2 ^ (d - 1), M * 2 ^ (d - 1), by positivity, by positivity, ?_⟩
  intro f hf g _
  have hpg := (hb f g).trans (mul_le_mul_of_nonneg_right (hMb f hf).le (by positivity))
  have hd : d = Fintype.card (InfinitePlace F) + S.card - 1 := by
    change Fintype.card (InfinitePlace F ⊕ (↑S : Type _)) - 1 = _
    rw [Fintype.card_sum, Fintype.card_coe]
  rw [← hd]
  let t := |Real.log (sLocalIdeleNorm F S g)|
  calc
    _ ≤ M * (1 + t) ^ d := hpg
    _ ≤ M * (2 ^ (d - 1) * (1 ^ d + t ^ d)) :=
      mul_le_mul_of_nonneg_left (add_pow_le zero_le_one (abs_nonneg _) _) hM.le
    _ = _ := by rw [one_pow]; ring

private def thetaUnit : (sIntegerRing F S)ˣ →* (SAdeles F S)ˣ :=
  (MonoidHom.fst _ _).comp ((sBlockUnitProduct F S).toMonoidHom.comp (sPrincipal F S))

private theorem thetaUnit_val (u : (sIntegerRing F S)ˣ) :
    (thetaUnit F S u).val = sIntegerDiagonal F S u.val := rfl

/-- Enumeration of the actual S-unit subgroup by the units of the S-integers. -/
def sUnitOrbitEquiv : U F S ≃ sUnitImage F S :=
  Equiv.ofBijective (fun u : U F S => ⟨thetaUnit F S u.toMul, ⟨u.toMul, rfl⟩⟩) (by
    constructor
    · intro u v h
      apply Additive.toMul.injective
      apply Units.ext
      have he := congrArg (fun a : sUnitImage F S => a.val.val) h
      change (thetaUnit F S u.toMul).val = (thetaUnit F S v.toMul).val at he
      rw [thetaUnit_val, thetaUnit_val] at he
      exact Subtype.val_injective ((sAdelesDiagonal_injective F S) he)
    · rintro ⟨_, u, rfl⟩
      exact ⟨Additive.ofMul u, rfl⟩)

theorem sUnitOrbitEquiv_val (u : U F S) :
    (sUnitOrbitEquiv F S u).val.val = sIntegerDiagonal F S u.toMul.val := thetaUnit_val F S u.toMul

/-- The subgroup acting in the S-local theta sum is discrete in the idele topology. -/
theorem sThetaUnitImage_discrete : DiscreteTopology (sUnitImage F S) := by
  letI := principalSAdeles_discrete F S
  have hv (a : sUnitImage F S) : a.val.val ∈ principalSAdeles F S := by
    obtain ⟨u, hu⟩ := a.property
    change thetaUnit F S u = a.val at hu
    exact ⟨u.val, (thetaUnit_val F S u).symm.trans (congrArg Units.val hu)⟩
  let e (a : sUnitImage F S) : principalSAdeles F S := ⟨a.val.val, hv a⟩
  have he : Continuous e := (Units.continuous_val.comp continuous_subtype_val).subtype_mk hv
  exact DiscreteTopology.of_continuous_injective he
    (fun a b hab => Subtype.ext (Units.ext (congrArg Subtype.val hab)))

private theorem thetaUnit_norm (u : (sIntegerRing F S)ˣ) :
    sLocalIdeleNorm F S (thetaUnit F S u) = 1 :=
  (sPrincipalLocalNormOne F S u).property

private abbrev thetaArchDegree := ∑ v : InfinitePlace F, v.mult

private theorem sLocalTheta_abs_large_envelope (N : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SAdeles F S → ℂ) (A : ℝ), 0 ≤ A →
      (∀ x, f x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H) →
      (∀ x, ‖f x‖ * sThetaArchWeight F x.1 ^
        (thetaArchDegree F * (N + degree F S) + 1) ≤ A) →
      ∀ g : (SAdeles F S)ˣ, 1 ≤ sLocalIdeleNorm F S g →
        sLocalIdeleNorm F S g ^ N * (∑' u : U F S, ‖f (sIntegerDiagonal F S u.toMul.val * g.val)‖) ≤ C * A := by
  obtain ⟨C₀, hC₀, h⟩ := sLocalTheta_abs_log_envelope F S H hH
  let J := N + degree F S
  let K := (1 + H) ^ S.card
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨C₀ * K ^ J * 2 ^ degree F S, by positivity, fun f A hA hsupp hbound g hg => ?_⟩
  let r := sLocalIdeleNorm F S g
  have hr : 0 < r := zero_lt_one.trans_le hg
  let x (u : U F S) := (thetaUnit F S u.toMul * g).val
  let scaled (z : SAdeles F S) : ℂ :=
    if z ∈ range x then (↑(r ^ J) : ℂ) * f z else 0
  have hsupport (z : SAdeles F S) (hz : scaled z ≠ 0) :
      ∀ v : S, ‖z.2 v‖ ≤ H := by
    apply hsupp z
    intro hf
    apply hz
    simp [scaled, hf]
  have hscaled (z : SAdeles F S) :
      ‖scaled z‖ * sThetaArchWeight F z.1 ≤ K ^ J * A := by
    by_cases hz : scaled z = 0
    · rw [hz, norm_zero, zero_mul]
      positivity
    · have hx : z ∈ range x := by
        by_contra hx
        exact hz (ite_eq_right hx)
      obtain ⟨u, rfl⟩ := hx
      let y := sThetaArchWeight F (x u).1
      have hy : 0 ≤ y := zero_le_one.trans (le_max_left _ _)
      have hn : sLocalIdeleNorm F S (thetaUnit F S u.toMul * g) = r := by
        rw [map_mul, thetaUnit_norm, one_mul]
      have hnorm : r ≤ K * y ^ thetaArchDegree F := by
        rw [← hn]
        exact sLocalIdeleNorm_le_archWeight F S _ H (hsupport _ hz)
      have he : scaled (x u) = (↑(r ^ J) : ℂ) * f (x u) :=
        ite_eq_left (mem_range_self u)
      rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hr.le _)]
      change r ^ J * ‖f (x u)‖ * y ≤ _
      calc
        _ ≤ (K * y ^ thetaArchDegree F) ^ J * ‖f (x u)‖ * y :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hnorm _) (norm_nonneg _)) hy
        _ = K ^ J * (‖f (x u)‖ * y ^ (thetaArchDegree F * J + 1)) := by
          rw [mul_pow, ← pow_mul, pow_succ]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hK _)
  let T := ∑' u : U F S, ‖f (x u)‖
  have hseries : (∑' u : U F S, ‖scaled (x u)‖) = r ^ J * T := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro u
    have he : scaled (x u) = (↑(r ^ J) : ℂ) * f (x u) := ite_eq_left (mem_range_self u)
    rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hr.le _)]
  have hraw := (h scaled (K ^ J * A) (by positivity) hsupport hscaled g).2
  change (∑' u : U F S, ‖scaled (x u)‖) ≤ _ at hraw
  rw [hseries] at hraw
  have hlog : 1 + |Real.log r| ≤ 2 * r := by
    rw [abs_of_nonneg (Real.log_nonneg hg)]
    linarith [Real.log_le_self hr.le]
  have hp : (1 + |Real.log r|) ^ degree F S ≤ 2 ^ degree F S * r ^ degree F S := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlog _
  have hfinal : (r ^ N * T) * r ^ degree F S ≤
      (C₀ * K ^ J * 2 ^ degree F S * A) * r ^ degree F S := calc
    _ = r ^ J * T := by dsimp [J]; rw [pow_add]; ring
    _ ≤ C₀ * (K ^ J * A) * (1 + |Real.log r|) ^ degree F S := hraw
    _ ≤ C₀ * (K ^ J * A) * (2 ^ degree F S * r ^ degree F S) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring
  exact le_of_mul_le_mul_right hfinal (pow_pos hr _)

private theorem sLocalTheta_large_bound (N : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SAdeles F S → ℂ) (A : ℝ), 0 ≤ A →
      (∀ x, f x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H) →
      (∀ x, ‖f x‖ * sThetaArchWeight F x.1 ^
        (thetaArchDegree F * (N + degree F S) + 1) ≤ A) →
      ∀ g : (SAdeles F S)ˣ, 1 ≤ sLocalIdeleNorm F S g →
        sLocalIdeleNorm F S g ^ N * ‖sLocalThetaOnIdeles F S f g‖ ≤ C * A := by
  obtain ⟨C, hC, h⟩ := sLocalTheta_abs_large_envelope F S N H hH
  refine ⟨C, hC, fun f A hA hs ht g hg => ?_⟩
  have hsum := (sLocalTheta_log_bound F S H hH).choose_spec.2
  have hθ (x : SAdeles F S) : ‖f x‖ * sThetaArchWeight F x.1 ≤ A := by
    have h1 : 1 ≤ sThetaArchWeight F x.1 := le_max_left _ _
    have hp : sThetaArchWeight F x.1 ≤
        sThetaArchWeight F x.1 ^ (thetaArchDegree F * (N + degree F S) + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ h1 (Nat.le_add_left 1 _)
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (ht x)
  have ha := (hsum f A hA hs hθ g).1
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ha)
    (pow_nonneg (zero_le_one.trans hg) _)).trans (h f A hA hs ht g hg)

/-- The large-modulus orbit bound with a continuous seminorm on the tests. -/
theorem sLocalTheta_largeNorm_seminorm (N : ℕ) :
    ∃ p : Seminorm ℂ (sLocalBruhatImage F S), Continuous p ∧ ∀ f g, 1 ≤ sLocalIdeleNorm F S g →
      sLocalIdeleNorm F S g ^ N * ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖ ≤ p f := by
  let w (g : (SAdeles F S)ˣ) : NNReal :=
    if 1 ≤ sLocalIdeleNorm F S g then (sLocalIdeleNorm F S g ^ N).toNNReal else 0
  have hw (g : (SAdeles F S)ˣ) (hg : 1 ≤ sLocalIdeleNorm F S g) :
      (w g : ℝ) = sLocalIdeleNorm F S g ^ N := by
    simp only [w, ite_eq_left hg, Real.coe_toNNReal _ (pow_nonneg (zero_le_one.trans hg) _)]
  have hw₀ (g : (SAdeles F S)ˣ) (hg : ¬ 1 ≤ sLocalIdeleNorm F S g) :
      (w g : ℝ) = 0 := by
    simp only [w, ite_eq_right hg, NNReal.coe_zero]
  obtain ⟨p, hp, hb⟩ := sLocalTheta_weight_seminorm F S
    (thetaArchDegree F * (N + degree F S) + 1) w (by
      intro H hH
      obtain ⟨C, hC, h⟩ := sLocalTheta_large_bound F S N H hH
      refine ⟨C, hC, fun f A hA hs hbound g => ?_⟩
      by_cases hg : 1 ≤ sLocalIdeleNorm F S g
      · rw [hw g hg]
        exact h f A hA hs hbound g hg
      · rw [hw₀ g hg, zero_mul]
        exact mul_nonneg hC hA)
  exact ⟨p, hp, fun f g hg => by simpa only [hw g hg] using hb f g⟩

/-- Rapid decay at large modulus, uniformly on bounded families of S-local tests.
The estimate is valid at every modulus at least one, including for exponent zero. -/
theorem sLocalTheta_largeNorm_bounded (B : Set (sLocalBruhatImage F S))
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f ∈ B, ∀ g : (SAdeles F S)ˣ, 1 ≤ sLocalIdeleNorm F S g →
      sLocalIdeleNorm F S g ^ N * ‖sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f.val) g‖ ≤ M := by
  obtain ⟨p, hp, hb⟩ := sLocalTheta_largeNorm_seminorm F S N
  have hW := PolynormableSpace.withSeminorms ℂ (sLocalBruhatImage F S)
  obtain ⟨M, hM, hMb⟩ := hW.isVonNBounded_iff_seminorm_bounded.mp hB ⟨p, hp⟩
  exact ⟨M, hM, fun f hf g hg => (hb f g hg).trans (hMb f hf).le⟩

/-- The pointwise logarithmic estimate also bounds the sum of absolute
values, as needed for unfolding the Mellin integral. -/
theorem sLocalTheta_absolute_log_bound (f : GlobalBruhat F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : (SAdeles F S)ˣ,
      (∑' u : U F S, ‖sLocalBruhatRestriction F S f
        (sIntegerDiagonal F S u.toMul.val * g.val)‖) ≤ C * thetaLogWeight F S g := by
  obtain ⟨H, A, hH, hA, hs, ht⟩ := sLocalTheta_envelope F S 1 f
  obtain ⟨C, hC, h⟩ := sLocalTheta_abs_log_envelope F S H hH
  exact ⟨C * A, mul_nonneg hC hA, fun g => (h _ A hA hs
    (by simpa only [pow_one] using ht) g).2⟩

/-- The absolute sum has arbitrary-power decay at large modulus. -/
theorem sLocalTheta_absolute_large_bound (f : GlobalBruhat F) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : (SAdeles F S)ˣ, 1 ≤ sLocalIdeleNorm F S g →
      sLocalIdeleNorm F S g ^ N * (∑' u : U F S, ‖sLocalBruhatRestriction F S f
        (sIntegerDiagonal F S u.toMul.val * g.val)‖) ≤ C := by
  obtain ⟨H, A, hH, hA, hs, ht⟩ := sLocalTheta_envelope F S
    (thetaArchDegree F * (N + degree F S) + 1) f
  obtain ⟨C, hC, h⟩ := sLocalTheta_abs_large_envelope F S N H hH
  exact ⟨C * A, mul_nonneg hC hA, h _ A hA hs ht⟩

private theorem sLocalTheta_reindex (f : SAdeles F S → ℂ) (g : (SAdeles F S)ˣ) (u : (sIntegerRing F S)ˣ) :
    sLocalThetaOnIdeles F S f (thetaUnit F S u * g) = sLocalThetaOnIdeles F S f g := by
  unfold sLocalThetaOnIdeles
  simp_rw [← thetaUnit_val, ← Units.val_mul, ← mul_assoc, ← map_mul]
  exact (Equiv.addRight (Additive.ofMul u)).tsum_eq
    (fun z : U F S => f (thetaUnit F S z.toMul * g).val)

theorem sLocalThetaOnIdeles_invariant (f : SAdeles F S → ℂ) (g u : (SAdeles F S)ˣ)
    (hu : u ∈ sUnitImage F S) : sLocalThetaOnIdeles F S f (u * g) = sLocalThetaOnIdeles F S f g := by
  obtain ⟨z, hz⟩ := hu
  change thetaUnit F S z = u at hz
  rw [← hz, sLocalTheta_reindex]

/-- The theta series on the quotient by the diagonally embedded S-units. -/
def sLocalTheta (f : SAdeles F S → ℂ) : SIdeleQuotient F S → ℂ :=
  Quotient.lift (sLocalThetaOnIdeles F S f) (fun g k h => by
    have hx : k / g ∈ sUnitImage F S :=
      (QuotientGroup.eq_one_iff (k / g)).mp (by
        change QuotientGroup.mk' (sUnitImage F S) (k / g) = 1
        rw [map_div]
        exact div_eq_one.mpr (Quotient.sound h).symm)
    obtain ⟨u, hu⟩ := hx
    have he : thetaUnit F S u * g = k := by
      change thetaUnit F S u = k / g at hu
      rw [hu, div_mul_cancel]
    rw [← he, sLocalTheta_reindex])

@[simp] theorem sLocalTheta_mk (f : SAdeles F S → ℂ) (g : (SAdeles F S)ˣ) :
    sLocalTheta F S f (QuotientGroup.mk g) = sLocalThetaOnIdeles F S f g := rfl

private theorem sLocalTheta_localMajorant (f : SAdeles F S → ℂ)
    (H A : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hsupp : ∀ x, f x ≠ 0 → ∀ v : S, ‖x.2 v‖ ≤ H)
    (hbound : ∀ x, ‖f x‖ * sThetaArchWeight F x.1 ≤ A)
    (g : (SAdeles F S)ˣ) :
    ∃ V ∈ 𝓝 g, ∃ m : U F S → ℝ, Summable m ∧
      ∀ u b, b ∈ V → ‖f (thetaUnit F S u.toMul * b).val‖ ≤ m u := by
  let V := {b : (SAdeles F S)ˣ |
    (∀ v : InfinitePlace F, ‖g.val.1 v‖ ≤ 2 * ‖b.val.1 v‖) ∧
    ∀ v : S, ‖g.val.2 v‖ ≤ 2 * ‖b.val.2 v‖}
  have hV : V ∈ 𝓝 g := by
    have hp : ∀ᶠ b : (SAdeles F S)ˣ in 𝓝 g, ∀ v : InfinitePlace F,
        ‖g.val.1 v‖ ≤ 2 * ‖b.val.1 v‖ := by
      apply Filter.eventually_all.mpr
      intro v
      have hinv := congrArg (fun y : SAdeles F S => y.1 v) g.val_inv
      have hp : 0 < ‖g.val.1 v‖ := norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one hinv)
      have hc : Continuous (fun b : (SAdeles F S)ˣ => 2 * ‖b.val.1 v‖) := by fun_prop
      have ht : Tendsto (fun b : (SAdeles F S)ˣ => 2 * ‖b.val.1 v‖) (𝓝 g)
          (𝓝 (2 * ‖g.val.1 v‖)) := hc.continuousAt
      exact (ht.eventually (Ioi_mem_nhds (show ‖g.val.1 v‖ < 2 * ‖g.val.1 v‖ by linarith))).mono
        fun _ h => h.le
    have hq : ∀ᶠ b : (SAdeles F S)ˣ in 𝓝 g, ∀ v : S,
        ‖g.val.2 v‖ ≤ 2 * ‖b.val.2 v‖ := by
      apply Filter.eventually_all.mpr
      intro v
      have hinv := congrArg (fun y : SAdeles F S => y.2 v) g.val_inv
      have hp : 0 < ‖g.val.2 v‖ := norm_pos_iff.mpr (left_ne_zero_of_mul_eq_one hinv)
      have hc : Continuous (fun b : (SAdeles F S)ˣ => 2 * ‖b.val.2 v‖) := by fun_prop
      have ht : Tendsto (fun b : (SAdeles F S)ˣ => 2 * ‖b.val.2 v‖) (𝓝 g)
          (𝓝 (2 * ‖g.val.2 v‖)) := hc.continuousAt
      exact (ht.eventually (Ioi_mem_nhds (show ‖g.val.2 v‖ < 2 * ‖g.val.2 v‖ by linarith))).mono
        fun _ h => h.le
    exact hp.and hq
  let major (x : SAdeles F S) : ℂ :=
    if ∀ v : S, ‖x.2 v‖ ≤ 2 * H then (2 * A / sThetaArchWeight F x.1 : ℝ) else 0
  have hy (x : InfiniteAdeleRing F) : 0 < sThetaArchWeight F x :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hmajor (x : SAdeles F S) : ‖major x‖ * sThetaArchWeight F x.1 ≤ 2 * A := by
    by_cases h : ∀ v : S, ‖x.2 v‖ ≤ 2 * H
    · simp only [major, ite_eq_left h, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (by positivity : 0 ≤ 2 * A) (hy _).le)]
      exact ((div_mul_cancel₀ _ (hy _).ne')).le
    · simp only [major, ite_eq_right h, norm_zero, zero_mul]
      positivity
  obtain ⟨_, _, hb⟩ := sLocalTheta_log_bound F S (2 * H) (by positivity)
  have hmajorant := (hb major (2 * A) (by positivity)
    (fun x h => by
      by_contra hn
      exact h (ite_eq_right hn)) hmajor g).1
  let m (u : U F S) := ‖major (thetaUnit F S u.toMul * g).val‖
  refine ⟨V, hV, m, ?_, fun u b hb => ?_⟩
  · simpa only [m, Units.val_mul, thetaUnit_val] using hmajorant
  let x := (thetaUnit F S u.toMul * g).val
  let y := (thetaUnit F S u.toMul * b).val
  have ha (v : InfinitePlace F) : ‖x.1 v‖ ≤ 2 * ‖y.1 v‖ := by
    change ‖(thetaUnit F S u.toMul).val.1 v * g.val.1 v‖ ≤
      2 * ‖(thetaUnit F S u.toMul).val.1 v * b.val.1 v‖
    rw [norm_mul, norm_mul, ← mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hb.1 v) (norm_nonneg _)
  have hf (v : S) : ‖x.2 v‖ ≤ 2 * ‖y.2 v‖ := by
    change ‖(thetaUnit F S u.toMul).val.2 v * g.val.2 v‖ ≤
      2 * ‖(thetaUnit F S u.toMul).val.2 v * b.val.2 v‖
    rw [norm_mul, norm_mul, ← mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hb.2 v) (norm_nonneg _)
  have hw : sThetaArchWeight F x.1 ≤ 2 * sThetaArchWeight F y.1 := by
    apply max_le
    · exact (by norm_num : (1 : ℝ) ≤ 2 * 1).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
    · rw [sThetaArchWeight]
      refine (Finset.sum_le_sum fun v _ => ha v).trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
  change ‖f y‖ ≤ ‖major x‖
  by_cases hfy : f y = 0
  · simp [hfy]
  · have hcut (v : S) : ‖x.2 v‖ ≤ 2 * H := (hf v).trans
      (mul_le_mul_of_nonneg_left (hsupp y hfy v) (by norm_num))
    simp only [major, ite_eq_left hcut, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by positivity : 0 ≤ 2 * A) (hy _).le)]
    apply (le_div_iff₀ (hy _)).mpr
    calc
      _ ≤ ‖f y‖ * (2 * sThetaArchWeight F y.1) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = 2 * (‖f y‖ * sThetaArchWeight F y.1) := by ring
      _ ≤ 2 * A := mul_le_mul_of_nonneg_left (hbound y) (by norm_num)

/-- The theta orbit sum converges locally uniformly in the idele. -/
theorem sLocalTheta_hasSumLocallyUniformly (f : GlobalBruhat F) :
    HasSumLocallyUniformly (fun (u : U F S) (g : (SAdeles F S)ˣ) =>
      sLocalBruhatRestriction F S f (sIntegerDiagonal F S u.toMul.val * g.val))
      (sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f)) := by
  let φ := sLocalBruhatRestriction F S f
  obtain ⟨H, A, hH, hA, hsupp, hbound⟩ := sLocalTheta_envelope F S 1 f
  apply hasSumLocallyUniformly_of_of_forall_exists_nhds
  intro g
  obtain ⟨V, hV, m, hm, hmajor⟩ := sLocalTheta_localMajorant F S φ H A hH hA hsupp (by simpa only [pow_one] using hbound) g
  refine ⟨V, hV, HasSumUniformlyOn.of_norm_le_summable hm ?_⟩
  simpa only [Units.val_mul, thetaUnit_val] using hmajor

/-- The orbit series converges uniformly on every compact subset of the S-ideles. -/
theorem sLocalTheta_hasSumUniformlyOn (f : GlobalBruhat F) (K : Set (SAdeles F S)ˣ)
    (hK : IsCompact K) :
    HasSumUniformlyOn (fun (u : U F S) (g : (SAdeles F S)ˣ) =>
      sLocalBruhatRestriction F S f (sIntegerDiagonal F S u.toMul.val * g.val))
      (sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f)) K := by
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    ← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK,
    ← hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]
  exact (sLocalTheta_hasSumLocallyUniformly F S f).hasSumLocallyUniformlyOn

/-- The absolute orbit sums converge uniformly on every compact subset of the S-ideles. -/
theorem sLocalTheta_norm_hasSumUniformlyOn (f : GlobalBruhat F) (K : Set (SAdeles F S)ˣ)
    (hK : IsCompact K) :
    HasSumUniformlyOn (fun (u : U F S) (g : (SAdeles F S)ˣ) =>
      ‖sLocalBruhatRestriction F S f (sIntegerDiagonal F S u.toMul.val * g.val)‖)
      (fun g => ∑' u : U F S, ‖sLocalBruhatRestriction F S f
        (sIntegerDiagonal F S u.toMul.val * g.val)‖) K := by
  let φ := sLocalBruhatRestriction F S f
  obtain ⟨H, A, hH, hA, hsupp, hbound⟩ := sLocalTheta_envelope F S 1 f
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    ← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK,
    ← hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  intro g _
  obtain ⟨V, hV, m, hm, hmajor⟩ := sLocalTheta_localMajorant F S φ H A hH hA hsupp (by simpa only [pow_one] using hbound) g
  refine ⟨V, nhdsWithin_le_nhds hV, HasSumUniformlyOn.of_norm_le_summable hm ?_⟩
  simpa only [Real.norm_of_nonneg (norm_nonneg _), Units.val_mul, thetaUnit_val] using hmajor

/-- The theta sum is continuous on the actual quotient of the S-ideles. -/
theorem sLocalTheta_continuous (f : GlobalBruhat F) :
    Continuous (sLocalTheta F S (sLocalBruhatRestriction F S f)) := by
  apply (QuotientGroup.isQuotientMap_mk (sUnitImage F S)).continuous_iff.mpr
  change Continuous (sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f))
  apply (hasSumLocallyUniformly_iff_tendstoLocallyUniformly.mp
    (sLocalTheta_hasSumLocallyUniformly F S f)).continuous
  exact Frequently.of_forall fun s => continuous_finsetSum _ fun u _ =>
    (sLocalBruhatRestriction_continuous F S f).comp (by fun_prop)

theorem sLocalThetaOnIdeles_continuous (f : GlobalBruhat F) :
    Continuous (sLocalThetaOnIdeles F S (sLocalBruhatRestriction F S f)) :=
  (sLocalTheta_continuous F S f).comp QuotientGroup.continuous_mk

end

end Masullo
