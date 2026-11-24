import BruhatCompactSupport
import BruhatSchwartzStrict
import BruhatDirectionalDerivatives
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Function Set Topology
open scoped ContDiff ENNReal NNReal BigOperators

namespace Masullo

noncomputable section

private theorem iteratedDeriv_unitPhase (k : ℕ) (c : ℂ) :
    iteratedDeriv k (fun t : ℝ ↦ c * Complex.exp ((t : ℂ) * Complex.I)) =
      fun t : ℝ ↦ (c * Complex.I ^ k) * Complex.exp ((t : ℂ) * Complex.I) := by
  let g (t : ℝ) := Complex.exp ((t : ℂ) * Complex.I)
  have hD (t : ℝ) : HasDerivAt g (Complex.I * g t) t := by
    have ht : HasDerivAt (fun x : ℝ ↦ (x : ℂ)) 1 t := by
      change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) t
      exact Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    convert (ht.mul_const Complex.I).cexp using 1
    simp only [g, one_mul]
    rw [mul_comm]
  change iteratedDeriv k (fun t ↦ c * g t) = _
  induction k with
  | zero => simp [g]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    change deriv (fun x : ℝ ↦ (c * Complex.I ^ k) * g x) t = _
    rw [((hD t).const_mul _).deriv, pow_succ]
    ring

private theorem norm_iteratedFDeriv_unitPhase_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (c : Circle) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y ↦ (c : ℂ) * Complex.exp ((L y : ℂ) * Complex.I)) x‖
      ≤ ‖L‖ ^ k := by
  let g (t : ℝ) := (c : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
  have hg : ContDiff ℝ ∞ g :=
    contDiff_const.mul ((Complex.ofRealCLM.contDiff.mul contDiff_const).cexp)
  change ‖iteratedFDeriv ℝ k (g ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hg x (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g (L x)) (fun _ ↦ L)).trans_eq ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv k (fun t : ℝ ↦ (c : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) (L x)‖ *
    (∏ _i : Fin k, ‖L‖) = _
  simp only [iteratedDeriv_unitPhase, norm_mul, Circle.norm_coe, norm_pow, Complex.norm_I,
    one_pow, Complex.norm_exp_ofReal_mul_I, mul_one, one_mul, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- A continuous seminorm on a space defined by seminorms inherits the
polynomial bound of an integer-indexed family in each defining seminorm. -/
private theorem polynomial_bound_of_withSeminorms {E I : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (p : I → Seminorm ℂ E) (hp : WithSeminorms p) (q : Seminorm ℂ E)
    (hq : Continuous q) (f : ℤ → E)
    (hf : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ z : ℤ,
      p i (f z) ≤ C * (1 + |(z : ℝ)|) ^ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ z : ℤ,
      q (f z) ≤ C * (1 + |(z : ℝ)|) ^ d := by
  classical
  obtain ⟨⟨S, ε⟩, hε, hS⟩ := hp.hasBasis_zero_ball.mem_iff.mp
    ((isOpen_lt hq continuous_const).mem_nhds (show q 0 < (1 : ℝ) by simp))
  choose C hC d hd using hf
  let A : ℝ := ∑ i ∈ S, C i
  let N := S.sup d
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ hC i
  refine ⟨(2 / ε) * (1 + A), by positivity, N, fun z ↦ ?_⟩
  let b : ℝ := 1 + |(z : ℝ)|
  have hb : 1 ≤ b := le_add_of_nonneg_right (abs_nonneg _)
  have hBN : 1 ≤ b ^ N := one_le_pow₀ hb
  have hSN : (S.sup p) (f z) ≤ A * b ^ N := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hA (by positivity)) fun i hi ↦ ?_
    exact (hd i z).trans (mul_le_mul
      (Finset.single_le_sum (fun j _ ↦ hC j) hi)
      (pow_le_pow_right₀ hb (Finset.le_sup hi)) (by positivity) hA)
  let t := ε / (2 * (1 + A * b ^ N))
  have ht : 0 < t := by positivity
  have hball : (t : ℂ) • f z ∈ (S.sup p).ball 0 ε := by
    rw [Seminorm.mem_ball_zero]
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    apply (mul_le_mul_of_nonneg_left hSN ht.le).trans_lt
    dsimp only [t]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_nonneg hA (show 0 ≤ b ^ N by positivity),
      mul_nonneg hε.le (mul_nonneg hA (show 0 ≤ b ^ N by positivity))]
  have hlt : t * q (f z) < 1 := by
    have := hS hball
    change q ((t : ℂ) • f z) < 1 at this
    rwa [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at this
  calc
    q (f z) ≤ (2 / ε) * (1 + A * b ^ N) := by
      have h : q (f z) < 1 / t := (lt_div_iff₀ ht).2 (by rwa [mul_comm])
      calc
        q (f z) ≤ 1 / t := h.le
        _ = _ := by dsimp only [t]; rw [one_div_div]; ring
    _ ≤ _ := by
      dsimp only [b] at hBN ⊢
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)

section Elementary

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "E" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

omit [DiscreteTopology F] [Finite F] in
/-- On a compact elementary group, the defining Schwartz bounds of a
character grow polynomially in the operator norm of its linear phase. -/
theorem elementaryCharacter_bound_of_phase [CompactSpace A]
    (i : ElementarySchwartzIndex m n r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ (χ : PontryaginDual (Multiplicative A)) (L : E →L[ℝ] ℝ),
      (∀ x : E, χ (Multiplicative.ofAdd (elementaryCoverHom x)) = Circle.exp (L x)) →
      elementarySchwartzBound (fun x ↦ (χ (Multiplicative.ofAdd x) : ℂ)) i ≤
        ENNReal.ofReal (C * ‖L‖ ^ d) := by
  let dirs : List E :=
    (List.ofFn (fun j : Fin m ↦ List.replicate (i.2.1 j) (EuclideanSpace.single j 1, 0))).flatten ++
    (List.ofFn (fun j : Fin n ↦ List.replicate (i.2.2.1 j) (0, EuclideanSpace.single j 1))).flatten
  let d := dirs.length
  let D := ∏ j : Fin d, ‖dirs.get j‖
  let W (x : A) : ℂ := (∏ j, (x.1 j : ℂ) ^ i.1 j) *
    (∏ j, (x.2.2.1 j : ℂ) ^ i.2.2.2 j)
  have hW : Continuous W := by
    apply Continuous.mul
    · exact continuous_finsetProd _ fun j _ ↦
        (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp continuous_fst)).pow _
    · exact continuous_finsetProd _ fun j _ ↦
        ((continuous_of_discreteTopology : Continuous (fun a : ℤ ↦ (a : ℂ))).comp
          ((continuous_apply j).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))).pow _
  obtain ⟨R, hR⟩ := (isCompact_univ : IsCompact (univ : Set A)).exists_bound_of_continuousOn
    hW.continuousOn
  refine ⟨max R 0 * D, by positivity, d, fun χ L hL ↦ ?_⟩
  unfold elementarySchwartzBound
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  let c : Circle := χ (Multiplicative.ofAdd (elementaryCover (0 : E) a b))
  let f := fun x : A ↦ (χ (Multiplicative.ofAdd x) : ℂ)
  have he (x : E) : f (elementaryCover x a b) =
      (c : ℂ) * Complex.exp ((L x : ℂ) * Complex.I) := by
    have h := elementaryCover_add (0 : E) x a b
    rw [zero_add] at h
    dsimp only [f, c]
    rw [h, show Multiplicative.ofAdd (elementaryCover (0 : E) a b + elementaryCoverHom x) =
      Multiplicative.ofAdd (elementaryCover (0 : E) a b) *
        Multiplicative.ofAdd (elementaryCoverHom x) from rfl, map_mul, Circle.coe_mul, hL, Circle.coe_exp]
  have hD := norm_iteratedFDeriv_unitPhase_comp L c d x
  have hpartial : ‖elementaryPartial f i.2.1 i.2.2.1 x a b‖ ≤ ‖L‖ ^ d * D := by
    unfold elementaryPartial
    change ‖(iteratedFDeriv ℝ d (fun y ↦ f (elementaryCover y a b)) x) dirs.get‖ ≤ _
    rw [show (fun y ↦ f (elementaryCover y a b)) =
      (fun y ↦ (c : ℂ) * Complex.exp ((L y : ℂ) * Complex.I)) from funext he]
    exact (ContinuousMultilinearMap.le_opNorm _ dirs.get).trans
      (mul_le_mul_of_nonneg_right hD (by positivity))
  have hweight : ‖W (elementaryCover x a b)‖ ≤ max R 0 :=
    (hR _ (mem_univ _)).trans (le_max_left _ _)
  change (↑‖W (elementaryCover x a b) * elementaryPartial f i.2.1 i.2.2.1 x a b‖₊ : ℝ≥0∞) ≤ _
  apply (ENNReal.le_ofReal_iff_toReal_le ENNReal.coe_ne_top (by positivity)).2
  change ‖W (elementaryCover x a b) * elementaryPartial f i.2.1 i.2.2.1 x a b‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ max R 0 * (‖L‖ ^ d * D) :=
      mul_le_mul hweight hpartial (norm_nonneg _) (le_max_right _ _)
    _ = _ := by ring

/-- Along a fixed line of characters, each defining Schwartz seminorm on a
compact elementary group grows at most polynomially in the integer parameter. -/
theorem elementaryCharacter_line_bound [CompactSpace A]
    (χ ψ : PontryaginDual (Multiplicative A)) (i : ElementarySchwartzIndex m n r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ z : ℤ,
      elementarySchwartzBound (fun x ↦ ((χ * ψ ^ z) (Multiplicative.ofAdd x) : ℂ)) i ≤
      ENNReal.ofReal (C * (1 + |(z : ℝ)|) ^ d) := by
  obtain ⟨L, hL⟩ := elementaryCharacter_phase χ
  obtain ⟨M, hM⟩ := elementaryCharacter_phase ψ
  obtain ⟨C, hC, d, hbound⟩ := elementaryCharacter_bound_of_phase (F := F) i
  let s (z : ℤ) : E →L[ℝ] ℝ := L + (z : ℝ) • M
  let B := ‖L‖ + ‖M‖
  refine ⟨C * B ^ d, by positivity, d, fun z ↦ ?_⟩
  have hnorm : ‖s z‖ ≤ B * (1 + |(z : ℝ)|) := by
    calc
      ‖s z‖ ≤ ‖L‖ + |(z : ℝ)| * ‖M‖ := by
        simpa [s, norm_smul, Real.norm_eq_abs] using norm_add_le L ((z : ℝ) • M)
      _ ≤ _ := by dsimp [B]; nlinarith [norm_nonneg L, norm_nonneg M,
        abs_nonneg (z : ℝ), mul_nonneg (norm_nonneg L) (abs_nonneg (z : ℝ))]
  have hphase (x : E) :
      (χ * ψ ^ z) (Multiplicative.ofAdd (elementaryCoverHom x)) = Circle.exp (s z x) := by
    let ev : PontryaginDual (Multiplicative A) →* Circle :=
      { toFun := fun k ↦ k (Multiplicative.ofAdd (elementaryCoverHom x))
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    change ev (χ * ψ ^ z) = _
    rw [map_mul ev, map_zpow ev]
    change χ (Multiplicative.ofAdd (elementaryCoverHom x)) *
      ψ (Multiplicative.ofAdd (elementaryCoverHom x)) ^ z = _
    rw [hL, hM, ← Circle.exp_zsmul, ← Circle.exp_add]
    simp only [s, add_apply, smul_apply, smul_eq_mul, zsmul_eq_mul]
  refine (hbound (χ * ψ ^ z) (s z) hphase).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm _) hC

end Elementary

section Compact

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [CompactSpace G]

set_option maxHeartbeats 1200000 in
/-- For any continuous seminorm on the full Schwartz–Bruhat space of a
compact group, a line of characters has polynomial growth. The entire
line lies in one compact elementary stage. -/
theorem compactBruhatCharacter_line_polynomial
    (χ ψ : PontryaginDual G) (q : Seminorm ℂ (BruhatSchwartz G)) (hq : Continuous q)
    (f : ℤ → BruhatSchwartz G)
    (hf : ∀ z x, (f z).val x = ((χ * ψ ^ z) x : ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ z : ℤ, q (f z) ≤ C * (1 + |(z : ℝ)|) ^ d := by
  obtain ⟨J, hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains (isCompact_univ (X := G))
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains
    (isCompact_singleton (x := ψ) |>.insert χ)
  let P := LCAStructuralPair.ofDual J H (fun x _ ↦ hJ (mem_univ x))
  letI : CompactSpace J.val := isCompact_iff_compactSpace.mp
    ((J.val.isClosed_of_isOpen J.property.1).isCompact)
  obtain ⟨p⟩ := P.quotient_elementary
  let S : BruhatSchwartzStage G := ⟨P, p⟩
  let A := ElementaryLCAModel p.realDim p.torusDim p.latticeRank p.finiteFactor
  letI : CompactSpace P.StageQuotient := inferInstanceAs
    (CompactSpace (J.val ⧸ P.kernel.comap J.val.subtype))
  letI : CompactSpace (Multiplicative A) := p.equiv.toHomeomorph.compactSpace
  letI : CompactSpace A := ⟨by
    simpa only [image_univ, Multiplicative.toAdd.surjective.range_eq] using
      (isCompact_univ : IsCompact (univ : Set (Multiplicative A))).image continuous_toAdd⟩
  let R (θ : PontryaginDual G) : J.val →* Circle := θ.toMonoidHom.comp J.val.subtype
  have hk (θ : PontryaginDual G) (hθ : θ ∈ H.val) :
      P.kernel.comap J.val.subtype ≤ (R θ).ker := by
    intro x hx
    change θ x.val = 1
    exact (mem_lcaDualAnnihilator_iff H.val x.val).mp hx ⟨θ, hθ⟩
  let D (θ : PontryaginDual G) (hθ : θ ∈ H.val) :
      PontryaginDual (Multiplicative A) := by
    let v : P.StageQuotient →ₜ* Circle :=
      ⟨QuotientGroup.lift _ (R θ) (hk θ hθ), (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (θ.continuous.comp continuous_subtype_val)⟩
    exact v.comp ⟨p.equiv.symm.toMulEquiv.toMonoidHom, p.equiv.symm.continuous⟩
  have hχH : χ ∈ H.val := hH (by simp)
  have hψH : ψ ∈ H.val := hH (by simp)
  let χ' := D χ hχH
  let ψ' := D ψ hψH
  have hD (θ : PontryaginDual G) (hθ : θ ∈ H.val) (x : P.upper.val) :
      D θ hθ (P.stageCoordinates p x) = θ x.val := by
    change (QuotientGroup.lift _ (R θ) (hk θ hθ) : P.StageQuotient →* Circle)
      (p.equiv.symm (p.equiv (QuotientGroup.mk x))) = _
    rw [p.equiv.symm_apply_apply]
    rfl
  let g (z : ℤ) (x : A) : ℂ := ((χ' * ψ' ^ z) (Multiplicative.ofAdd x) : ℂ)
  have hg (z : ℤ) (x : P.upper.val) :
      g z (P.stageCoordinates p x).toAdd = (f z).val x.val := by
    rw [hf]
    let e : PontryaginDual G →* Circle :=
      { toFun := fun θ ↦ θ x.val, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    let e' : PontryaginDual (Multiplicative A) →* Circle :=
      { toFun := fun θ ↦ θ (P.stageCoordinates p x)
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    change (e' (χ' * ψ' ^ z) : ℂ) = (e (χ * ψ ^ z) : ℂ)
    rw [map_mul e', map_zpow e', map_mul e, map_zpow e]
    change ((D χ hχH (P.stageCoordinates p x) * D ψ hψH (P.stageCoordinates p x) ^ z : Circle) : ℂ) =
      ((χ x.val * ψ x.val ^ z : Circle) : ℂ)
    rw [hD χ hχH x, hD ψ hψH x]
  have hS (z : ℤ) : g z ∈ elementarySchwartzSubmodule p.realDim p.torusDim p.latticeRank p.finiteFactor :=
    elementarySchwartz_mem_of_compactSupport _ (HasCompactSupport.of_compactSpace _)
      (elementaryCharacter_smooth (χ' * ψ' ^ z))
  let u (z : ℤ) : S.Space := ⟨g z, hS z⟩
  have he (z : ℤ) : S.inclusionCLM (u z) = f z := by
    apply Subtype.ext
    funext x
    let y : P.upper.val := ⟨x, hJ (mem_univ x)⟩
    exact (P.realizeSchwartz_apply_of_mem p (u z) y).trans (hg z y)
  let q' := q.comp S.inclusion
  have hq' : Continuous q' := hq.comp S.inclusionCLM.continuous
  obtain ⟨C, hC, d, hd⟩ := polynomial_bound_of_withSeminorms _
    elementarySchwartz_withSeminorms q' hq' u fun i ↦ by
      obtain ⟨C, hC, d, hd⟩ := elementaryCharacter_line_bound χ' ψ' i
      refine ⟨C, hC, d, fun z ↦ ?_⟩
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hd z)
      rwa [ENNReal.toReal_ofReal (by positivity)] at h
  refine ⟨C, hC, d, fun z ↦ ?_⟩
  rw [← he z]
  exact hd z

end Compact

end

end Masullo
