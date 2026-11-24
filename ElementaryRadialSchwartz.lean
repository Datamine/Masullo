import BruhatDirectionalDerivatives
import ElementarySchwartzRefinement
import ElementarySchwartzCutoffs
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Real.Cardinality

open Function Set Topology
open scoped ContDiff ENNReal SchwartzMap

namespace Masullo

noncomputable section

private abbrev RealStage : Type := ElementaryLCAModel 1 0 0 PUnit

private def realStageInclusion : ℝ →+ RealStage where
  toFun x := (WithLp.toLp 2 (fun _ => x), 0, 0, 0)
  map_zero' := rfl
  map_add' x y := by
    change (WithLp.toLp 2 (fun _ : Fin 1 => x + y), (0 : (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit)) =
      (WithLp.toLp 2 (fun _ : Fin 1 => x) + WithLp.toLp 2 (fun _ : Fin 1 => y), 0 + 0)
    rw [zero_add]
    rfl

private theorem realStageInclusion_isProperMap : IsProperMap realStageInclusion := by
  let p (x : RealStage) := x.1 0
  have hp : Continuous p := (PiLp.continuous_apply 2 _ 0).comp continuous_fst
  have hi : Continuous realStageInclusion := by
    change Continuous (fun x : ℝ => (WithLp.toLp 2 (fun _ : Fin 1 => x), (0, 0, 0)) : ℝ → RealStage)
    exact (PiLp.continuous_toLp 2 _ |>.comp (continuous_pi fun _ => continuous_id)).prodMk continuous_const
  exact isProperMap_of_comp_of_t2 hi hp (show IsProperMap (p ∘ realStageInclusion) from isProperMap_id)

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "V" => Fin m ⊕ Fin r → ℝ

/-- A proper real coordinate controls the real and lattice growth of an
elementary quotient. -/
theorem exists_elementaryGrowth_le_properLog (l : A →+ ℝ) (hl : IsProperMap l) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖elementaryGrowth x‖ ≤ C * |l x| := by
  let j := realStageInclusion.comp l
  have hj : IsProperMap j := realStageInclusion_isProperMap.comp hl
  obtain ⟨L, hL⟩ := elementaryGrowth_hom j hj.continuous
  have hi := elementaryGrowth_linear_injective_of_proper j hj L hL
  obtain ⟨C, hC, hCL⟩ := L.toLinearMap.injective_iff_antilipschitz.mp hi
  refine ⟨C, by positivity, fun x => ?_⟩
  have hbound := hCL.le_mul_dist (elementaryGrowth x) 0
  change dist (elementaryGrowth x) 0 ≤ (C : ℝ) * dist (L (elementaryGrowth x)) (L 0) at hbound
  rw [map_zero, ← hL, dist_zero_right, dist_zero_right] at hbound
  apply hbound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
  intro k
  cases k with
  | inl i => change ‖l x‖ ≤ |l x|; rw [Real.norm_eq_abs]
  | inr i => exact Fin.elim0 i

/-- A proper surjective additive logarithm has exactly one unbounded
real direction and no lattice direction on an elementary group. -/
theorem elementary_dimensions_of_proper_surjective_log (l : A →+ ℝ)
    (hl : IsProperMap l) (hs : Surjective l) : m = 1 ∧ r = 0 := by
  let j := realStageInclusion.comp l
  have hj : IsProperMap j := realStageInclusion_isProperMap.comp hl
  obtain ⟨L, hL⟩ := elementaryGrowth_hom j hj.continuous
  have hi := elementaryGrowth_linear_injective_of_proper j hj L hL
  have hdim := LinearMap.finrank_le_finrank_of_injective (f := L.toLinearMap) hi
  have hmr : m + r ≤ 1 := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, add_zero] using hdim
  have hm : m ≠ 0 := by
    intro hm
    subst m
    obtain ⟨c, d, he⟩ := elementary_real_addHom_coordinates l hl.continuous
    have ht : Surjective (fun a : Fin r → ℤ => ∑ i, d i * (a i : ℝ)) := by
      intro y
      obtain ⟨g, hg⟩ := hs y
      exact ⟨g.2.2.1, by simpa using (he g).symm.trans hg⟩
    exact Cardinal.not_countable_real (ht.range_eq ▸ Set.countable_range _)
  omega

private theorem norm_iteratedFDeriv_elementaryCharacter
    (χ : PontryaginDual (Multiplicative A)) (k : ℕ) (a : Fin r → ℤ) (b : F) (x : X) :
    ‖iteratedFDeriv ℝ k (fun z => (χ (Multiplicative.ofAdd (elementaryCover z a b)) : ℂ)) x‖ =
    ‖iteratedFDeriv ℝ k (fun z => (χ (Multiplicative.ofAdd (elementaryCoverHom z)) : ℂ)) (0 : X)‖ := by
  let f (z : X) := (χ (Multiplicative.ofAdd (elementaryCover z a b)) : ℂ)
  let q (z : X) := (χ (Multiplicative.ofAdd (elementaryCoverHom z)) : ℂ)
  have hq : ContDiff ℝ ∞ q := elementaryCharacter_smooth χ 0 0
  have hf : (fun z => f (x + z)) = fun z => f x • q z := by
    funext z
    dsimp only [f, q]
    rw [elementaryCover_add, show Multiplicative.ofAdd (elementaryCover x a b + elementaryCoverHom z) =
      Multiplicative.ofAdd (elementaryCover x a b) * Multiplicative.ofAdd
        (elementaryCoverHom z : A) from rfl, map_mul, Circle.coe_mul, smul_eq_mul]
  have he := (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) k x (0 : X))
  rw [hf, add_zero] at he
  change ‖iteratedFDeriv ℝ k f x‖ = ‖iteratedFDeriv ℝ k q (0 : X)‖
  have hfx : ‖f x‖ = 1 := Circle.norm_coe _
  rw [← he, iteratedFDeriv_const_smul_apply' (a := f x) (hq.contDiffAt.of_le (by
    exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))), norm_smul, hfx, one_mul]

private theorem elementaryFibreBasis_norm (i : Fin m ⊕ Fin n) :
    ‖elementaryFibreBasis m n i‖ = 1 := by
  cases i <;> simp [elementaryFibreBasis, Module.Basis.prod_apply, Prod.norm_def,
    EuclideanSpace.basisFun_apply, OrthonormalBasis.coe_toBasis, PiLp.norm_single]

private theorem norm_iteratedFDeriv_schwartz_comp_affine
    (p : 𝓢(ℝ, ℂ)) (L : X →L[ℝ] ℝ) (c : ℝ) (k : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ k (fun z => p (L z + c)) x‖ ≤
      ‖iteratedFDeriv ℝ k p (L x + c)‖ * ‖L‖ ^ k := by
  let f (t : ℝ) := p (t + c)
  have hf : ContDiff ℝ ∞ f := (p.smooth ⊤).comp (contDiff_id.add contDiff_const)
  change ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k f (L x)) (fun _ => L)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, f, iteratedFDeriv_comp_add_right] using h

private theorem elementarySchwartz_monomial_le_properLog
    (l : A →+ ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖elementaryGrowth x‖ ≤ C * |l x|)
    (α : Fin m → ℕ) (δ : Fin r → ℕ) (x : X) (a : Fin r → ℤ) (b : F) :
    ‖(∏ k, (x.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)‖ ≤
      (C * |l (elementaryCover x a b)|) ^ ((∑ k, α k) + ∑ k, δ k) := by
  let y := elementaryCover x a b
  let R := C * |l y|
  have hreal (i : Fin m) : |x.1 i| ≤ R := by
    calc
      |x.1 i| = ‖elementaryGrowth y (Sum.inl i)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖elementaryGrowth y‖ := norm_le_pi_norm _ _
      _ ≤ R := hC y
  have hint (i : Fin r) : |(a i : ℝ)| ≤ R := by
    calc
      |(a i : ℝ)| = ‖elementaryGrowth y (Sum.inr i)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖elementaryGrowth y‖ := norm_le_pi_norm _ _
      _ ≤ R := hC y
  simp only [norm_mul, norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast]
  change _ ≤ R ^ _
  rw [pow_add, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  have hR : 0 ≤ R := mul_nonneg hC0 (abs_nonneg _)
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ =>
      pow_le_pow_left₀ (abs_nonneg _) (hreal i) _)
  · exact Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ =>
      pow_le_pow_left₀ (abs_nonneg _) (hint i) _)
  · positivity
  · positivity

/-- On a proper logarithmic chart, rapid decay of all covering derivatives
implies membership in the elementary Schwartz space. -/
theorem elementarySchwartz_mem_of_log_derivative_bounds (l : A →+ ℝ) (hl : IsProperMap l)
    (f : A → ℂ) (hsm : ∀ (a : Fin r → ℤ) (b : F),
      ContDiff ℝ ∞ (fun x : X ↦ f (elementaryCover x a b)))
    (hb : ∀ N k : ℕ, ∃ B : ℝ, ∀ (x : X) (a : Fin r → ℤ) (b : F),
      (1 + |l (elementaryCover x a b)|) ^ N *
        ‖iteratedFDeriv ℝ k (fun y ↦ f (elementaryCover y a b)) x‖ ≤ B) :
    f ∈ elementarySchwartzSubmodule m n r F := by
  refine ⟨hsm, ?_⟩
  obtain ⟨C, hC, hlog⟩ := exists_elementaryGrowth_le_properLog l hl
  rintro ⟨α, β, γ, δ⟩
  let N := (∑ i, α i) + ∑ j, δ j
  let k := (elementaryDirectionList β γ).length
  obtain ⟨B, hB⟩ := hb N k
  apply lt_of_le_of_lt ?_ (show ENNReal.ofReal (C ^ N * B) < ⊤ from ENNReal.ofReal_lt_top)
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  let t := l (elementaryCover x a b)
  let W : ℂ := (∏ i, (x.1 i : ℂ) ^ α i) * (∏ j, (a j : ℂ) ^ δ j)
  let D := iteratedFDeriv ℝ k (fun y ↦ f (elementaryCover y a b)) x
  change ‖W * elementaryPartial f β γ x a b‖ₑ ≤ ENNReal.ofReal (C ^ N * B)
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hpart : ‖elementaryPartial f β γ x a b‖ ≤ ‖D‖ := by
    rw [elementaryPartial_eq_basis f a b β γ x]
    apply ContinuousMultilinearMap.unit_le_opNorm
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact (elementaryFibreBasis_norm _).le
  have hw : ‖W‖ ≤ (C * |t|) ^ N := elementarySchwartz_monomial_le_properLog l C hC hlog α δ x a b
  rw [norm_mul]
  calc
    _ ≤ ((C * |t|) ^ N) * ‖D‖ := mul_le_mul hw hpart (norm_nonneg _) (by positivity)
    _ ≤ ((C * (1 + |t|)) ^ N) * ‖D‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (by linarith) hC) _) (norm_nonneg _)
    _ = C ^ N * ((1 + |t|) ^ N * ‖D‖) := by rw [mul_pow, mul_assoc]
    _ ≤ C ^ N * B := mul_le_mul_of_nonneg_left (hB x a b) (by positivity)

private theorem norm_iteratedFDeriv_affine {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Y → ℂ) (hf : ContDiff ℝ ∞ f) (L : X →L[ℝ] Y) (c : Y) (k : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ k (fun y => f (L y + c)) x‖ ≤
      ‖iteratedFDeriv ℝ k f (L x + c)‖ * ‖L‖ ^ k := by
  let g (t : Y) := f (t+c)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  change ‖iteratedFDeriv ℝ k (g ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hg x (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))]
  have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g (L x)) (fun _ => L)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, g, iteratedFDeriv_comp_add_right] using h

set_option maxHeartbeats 1100000 in
/-- Radial–angular multiplication on elementary quotients. A proper log
coordinate provides the rapid decay and the pulled-back angular Schwartz
factor has bounded derivatives. -/
theorem elementarySchwartz_splitProduct_mem {d e s : ℕ} {H : Type*}
    [AddCommGroup H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    (l : A →+ ℝ) (hl : IsProperMap l)
    (φ : A →+ ElementaryLCAModel d e s H) (hφ : Continuous φ)
    (p : 𝓢(ℝ, ℂ)) (h : ElementarySchwartz d e s H) :
    (fun x => h (φ x) * p (l x)) ∈ elementarySchwartzSubmodule m n r F := by
  obtain ⟨M,hM⟩ := elementaryCover_hom_affine φ hφ
  let L₀ := l.comp (elementaryCoverHom : X →+ A)
  have hL₀ : Continuous L₀ := hl.continuous.comp elementaryCoverHom_continuous
  let L : X →L[ℝ] ℝ := ⟨L₀.toRealLinearMap hL₀,(L₀.toRealLinearMap hL₀).continuous_of_finiteDimensional⟩
  have hL (x : X) (a : Fin r → ℤ) (b : F) :
      l (elementaryCover x a b) = L x + l (elementaryCover (0 : X) a b) := by
    have he := elementaryCover_add (0 : X) x a b
    rw [zero_add] at he
    rw [he,map_add,add_comm]
    rfl
  let R (a : Fin r → ℤ) (b : F) (x : X) := p (l (elementaryCover x a b))
  let Q (a : Fin r → ℤ) (b : F) (x : X) := h (φ (elementaryCover x a b))
  have hR (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (R a b) := by
    have he : R a b = fun z => p (L z + l (elementaryCover (0 : X) a b)) :=
      funext fun z => congrArg p (hL z a b)
    rw [he]
    exact (p.smooth ⊤).comp (L.contDiff.add contDiff_const)
  have hQ (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (Q a b) :=
    elementaryContDiff_hom φ hφ h.val h.property.1 a b
  apply elementarySchwartz_mem_of_log_derivative_bounds l hl _
    (fun a b => (hQ a b).mul (hR a b))
  intro N k
  let rBound (j : ℕ) : ℝ :=
    2^N * (Finset.Iic (N,j)).sup (fun i => SchwartzMap.seminorm ℂ i.1 i.2) p * ‖L‖^j
  have hrb (j : ℕ) (x : X) (a : Fin r → ℤ) (b : F) :
      (1 + |l (elementaryCover x a b)|)^N * ‖iteratedFDeriv ℝ j (R a b) x‖ ≤ rBound j := by
    have he : R a b = fun z => p (L z + l (elementaryCover (0 : X) a b)) :=
      funext fun z => congrArg p (hL z a b)
    have hd := norm_iteratedFDeriv_affine p (p.smooth ⊤) L (l (elementaryCover (0 : X) a b)) j x
    rw [← he,← hL] at hd
    refine (mul_le_mul_of_nonneg_left hd (by positivity)).trans ?_
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa only [Real.norm_eq_abs] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N,j)) le_rfl le_rfl p
        (l (elementaryCover x a b)))
  choose q _ hq using fun j => exists_elementary_weighted_iterated_seminorm
    (n := e) (F := H) (1 : MvPolynomial (Fin d ⊕ Fin s) ℂ) j
  let aBound (j : ℕ) : ℝ := q j h * ‖M‖ ^ j
  have hab (j : ℕ) (x : X) (a : Fin r → ℤ) (b : F) :
      ‖iteratedFDeriv ℝ j (Q a b) x‖ ≤ aBound j := by
    obtain ⟨y,a',b',hy⟩ := hM a b
    have he : Q a b = fun z => h (elementaryCover (M z + y) a' b') :=
      funext fun z => congrArg h (hy z)
    rw [he]
    have hD : ‖iteratedFDeriv ℝ j (fun z => h (elementaryCover z a' b')) (M x + y)‖ ≤ q j h := by
      simpa only [map_one,norm_one,one_mul] using hq j h (M x + y) a' b'
    exact (norm_iteratedFDeriv_affine _ (h.property.1 a' b') M y j x).trans
      (mul_le_mul_of_nonneg_right hD (by positivity))
  let C := ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ) * aBound j * rBound (k-j)
  refine ⟨C,fun x a b => ?_⟩
  have hD := norm_iteratedFDeriv_mul_le (hQ a b) (hR a b) x (n := k)
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  let w := (1 + |l (elementaryCover x a b)|)^N
  change w * ‖iteratedFDeriv ℝ k (fun z => Q a b z * R a b z) x‖ ≤ C
  apply (mul_le_mul_of_nonneg_left hD (by unfold w; positivity)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ = (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (Q a b) x‖ *
        (w * ‖iteratedFDeriv ℝ (k-j) (R a b) x‖) := by ring
    _ ≤ _ := by
      have hn : 0 ≤ aBound j := (norm_nonneg _).trans (hab j x a b)
      gcongr
      · exact hab j x a b
      · exact hrb (k-j) x a b

/-- A unitary character preserves elementary Schwartz functions.
Its fibre derivatives are uniformly bounded, so the product rule preserves rapid decay. -/
theorem elementarySchwartz_unitaryMul_mem (χ : PontryaginDual (Multiplicative A))
    (f : ElementarySchwartz m n r F) :
    (fun z => (χ (Multiplicative.ofAdd z) : ℂ) * f z) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  let u (a : Fin r → ℤ) (b : F) (x : X) := f (elementaryCover x a b)
  let v (a : Fin r → ℤ) (b : F) (x : X) := (χ (Multiplicative.ofAdd (elementaryCover x a b)) : ℂ)
  have hu (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (u a b) := f.property.1 a b
  have hv (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (v a b) := elementaryCharacter_smooth χ a b
  refine ⟨fun a b => (hv a b).mul (hu a b), ?_⟩
  rintro ⟨α, β, γ, δ⟩
  let k := (elementaryDirectionList β γ).length
  let c (j : ℕ) := ‖iteratedFDeriv ℝ j
    (fun z => (χ (Multiplicative.ofAdd (elementaryCoverHom z)) : ℂ)) (0 : X)‖
  let W (x : X) (a : Fin r → ℤ) : ℂ :=
    (∏ i, (x.1 i : ℂ)^α i) * ∏ i, (a i : ℂ)^δ i
  let d : (Fin m ⊕ Fin r) →₀ ℕ := Finsupp.equivFunOnFinite.symm (Sum.elim α δ)
  let P := MvPolynomial.monomial d (1 : ℂ)
  have hP (x : X) (a : Fin r → ℤ) (b : F) :
      MvPolynomial.eval (elementaryGrowthVariables (elementaryCover x a b)) P = W x a := by
    rw [MvPolynomial.eval_monomial, d.prod_fintype _ (fun _ => pow_zero _),
      Fintype.prod_sum_type, one_mul]
    rfl
  have hb (j : ℕ) : ∃ C : ℝ, ∀ x a b,
      ‖W x a‖ * ‖iteratedFDeriv ℝ j (u a b) x‖ ≤ C := by
    obtain ⟨q, _, hq⟩ := exists_elementary_weighted_iterated_seminorm (n := n) (F := F) P j
    refine ⟨q f, fun x a b => ?_⟩
    simpa only [hP] using hq f x a b
  choose C hC using hb
  let M := ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * c j * C (k - j)
  apply lt_of_le_of_lt ?_ (show ENNReal.ofReal M < ⊤ from ENNReal.ofReal_lt_top)
  refine iSup_le fun x => iSup_le fun a => iSup_le fun b => ?_
  let g (z : A) := (χ (Multiplicative.ofAdd z) : ℂ) * f z
  change ‖W x a * elementaryPartial g β γ x a b‖ₑ ≤ ENNReal.ofReal M
  rw [← ofReal_norm, norm_mul]
  apply ENNReal.ofReal_le_ofReal
  have hp : ‖elementaryPartial g β γ x a b‖ ≤
      ‖iteratedFDeriv ℝ k (fun z => v a b z * u a b z) x‖ := by
    rw [elementaryPartial_eq_basis g a b β γ x]
    apply ContinuousMultilinearMap.unit_le_opNorm
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact (elementaryFibreBasis_norm _).le
  have hd := norm_iteratedFDeriv_mul_le (hv a b) (hu a b) x (n := k)
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  refine (mul_le_mul_of_nonneg_left (hp.trans hd) (norm_nonneg _)).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [show ‖iteratedFDeriv ℝ j (v a b) x‖ = c j from
    norm_iteratedFDeriv_elementaryCharacter χ j a b x]
  calc
    _ = (k.choose j : ℝ) * c j * (‖W x a‖ * ‖iteratedFDeriv ℝ (k-j) (u a b) x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hC (k-j) x a b) (by unfold c; positivity)

/-- A real Schwartz profile along a proper logarithmic homomorphism,
multiplied by any unitary character, is Schwartz on the elementary group. -/
theorem elementarySchwartz_radialCharacter_mem (l : A →+ ℝ) (hl : IsProperMap l)
    (χ : PontryaginDual (Multiplicative A)) (p : 𝓢(ℝ, ℂ)) :
    (fun x => p (l x) * (χ (Multiplicative.ofAdd x) : ℂ)) ∈ elementarySchwartzSubmodule m n r F := by
  let f (x : A) := p (l x) * (χ (Multiplicative.ofAdd x) : ℂ)
  let H := l.comp (elementaryCoverHom : X →+ A)
  have hH : Continuous H := hl.continuous.comp elementaryCoverHom_continuous
  let L₀ := H.toRealLinearMap hH
  let L : X →L[ℝ] ℝ := ⟨L₀, L₀.continuous_of_finiteDimensional⟩
  have hL (x : X) (a : Fin r → ℤ) (b : F) :
      l (elementaryCover x a b) = L x + l (elementaryCover (0 : X) a b) := by
    have he := elementaryCover_add (0 : X) x a b
    rw [zero_add] at he
    rw [he, map_add, add_comm]
    rfl
  let u (a : Fin r → ℤ) (b : F) (x : X) := p (L x + l (elementaryCover (0 : X) a b))
  let v (a : Fin r → ℤ) (b : F) (x : X) := (χ (Multiplicative.ofAdd (elementaryCover x a b)) : ℂ)
  have hu (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (u a b) :=
    (p.smooth ⊤).comp (L.contDiff.add contDiff_const)
  have hv (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (v a b) := elementaryCharacter_smooth χ a b
  have hc (a : Fin r → ℤ) (b : F) : (fun z => f (elementaryCover z a b)) =
      fun z => u a b z * v a b z := funext fun z => by
    change p (l (elementaryCover z a b)) * v a b z = _
    rw [hL]
  change (∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun z => f (elementaryCover z a b))) ∧
    ∀ i, elementarySchwartzBound f i < ⊤
  refine ⟨fun a b => by rw [hc]; exact (hu a b).mul (hv a b), ?_⟩
  obtain ⟨C, hC, hCg⟩ := exists_elementaryGrowth_le_properLog l hl
  rintro ⟨α, β, γ, δ⟩
  let k := (elementaryDirectionList β γ).length
  let d := (∑ i, α i) + ∑ j, δ j
  let bnd (j : ℕ) := ‖iteratedFDeriv ℝ j
    (fun z => (χ (Multiplicative.ofAdd (elementaryCoverHom z)) : ℂ)) (0 : X)‖
  let M := ∑ j ∈ Finset.range (k + 1),
    (k.choose j : ℝ) * (C ^ d * (SchwartzMap.seminorm ℂ d j p * ‖L‖ ^ j)) * bnd (k - j)
  apply lt_of_le_of_lt ?_ (show ENNReal.ofReal M < ⊤ from ENNReal.ofReal_lt_top)
  apply iSup_le
  intro x
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  let y := elementaryCover x a b
  let W : ℂ := (∏ i, (x.1 i : ℂ) ^ α i) * (∏ j, (a j : ℂ) ^ δ j)
  change ‖W * elementaryPartial f β γ x a b‖ₑ ≤ ENNReal.ofReal M
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  have hpart : ‖elementaryPartial f β γ x a b‖ ≤ ‖iteratedFDeriv ℝ k (fun z => u a b z * v a b z) x‖ := by
    rw [elementaryPartial_eq_basis f a b β γ x, hc]
    apply ContinuousMultilinearMap.unit_le_opNorm
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact (elementaryFibreBasis_norm _).le
  have hw : ‖W‖ ≤ (C * |l y|) ^ d := elementarySchwartz_monomial_le_properLog l C hC hCg α δ x a b
  have hder := norm_iteratedFDeriv_mul_le (hu a b) (hv a b) x (n := k)
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  change ‖W * elementaryPartial f β γ x a b‖ ≤ M
  rw [norm_mul]
  calc
    _ ≤ (C * |l y|) ^ d * (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (u a b) x‖ * ‖iteratedFDeriv ℝ (k - j) (v a b) x‖) :=
      mul_le_mul hw (hpart.trans hder) (norm_nonneg _) (by positivity)
    _ ≤ M := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have hj := norm_iteratedFDeriv_schwartz_comp_affine p L (l (elementaryCover (0 : X) a b)) j x
      change ‖iteratedFDeriv ℝ j (u a b) x‖ ≤ _ at hj
      rw [← hL] at hj
      have hj' := SchwartzMap.le_seminorm ℂ d j p (l y)
      rw [Real.norm_eq_abs] at hj'
      have hV : ‖iteratedFDeriv ℝ (k - j) (v a b) x‖ = bnd (k - j) :=
        norm_iteratedFDeriv_elementaryCharacter χ (k - j) a b x
      rw [hV, mul_pow]
      calc
        _ ≤ C ^ d * |l y| ^ d * ((k.choose j : ℝ) * (‖iteratedFDeriv ℝ j p (l y)‖ * ‖L‖ ^ j) * bnd (k - j)) := by
          gcongr
        _ = (k.choose j : ℝ) * (C ^ d * ((|l y| ^ d * ‖iteratedFDeriv ℝ j p (l y)‖) * ‖L‖ ^ j)) * bnd (k - j) := by ring
        _ ≤ _ := by gcongr

/-- A polynomial in a continuous real coordinate gives a continuous
weighted supremum seminorm on the elementary Schwartz space. -/
theorem exists_elementarySchwartz_logWeight_seminorm (l : A →+ ℝ) (hl : Continuous l) (N : ℕ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧
      ∀ f x, (1 + (l x) ^ 2) ^ N * ‖f x‖ ≤ q f := by
  obtain ⟨a, b, hab⟩ := elementary_real_addHom_coordinates l hl
  let Q : MvPolynomial (Fin m ⊕ Fin r) ℂ :=
    (∑ i, MvPolynomial.C (a i : ℂ) * MvPolynomial.X (Sum.inl i)) +
    ∑ j, MvPolynomial.C (b j : ℂ) * MvPolynomial.X (Sum.inr j)
  let P := (1 + Q ^ 2) ^ N
  obtain ⟨S, hS, hval⟩ := elementarySchwartz_withSeminorms_P2 (m := m) (n := n) (r := r) (F := F)
  let i : (Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ := (0, 0, P)
  refine ⟨S i, hS.continuous_seminorm i, fun f x => ?_⟩
  obtain ⟨z, hz⟩ := elementaryCover_surjective x.2.2.1 x.2.2.2 x.1 x.2.1
  let v := (x.1, z)
  have he : elementaryCover v x.2.2.1 x.2.2.2 = x := hz
  have hQ : MvPolynomial.eval (Sum.elim (fun k => (v.1 k : ℂ)) (fun k => (x.2.2.1 k : ℂ))) Q = (l x : ℂ) := by
    simp only [Q, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Sum.elim_inl, Sum.elim_inr, hab x, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_intCast]
    rfl
  have hP : MvPolynomial.eval (Sum.elim (fun k => (v.1 k : ℂ)) (fun k => (x.2.2.1 k : ℂ))) P =
      (((1 + (l x) ^ 2) ^ N : ℝ) : ℂ) := by
    simp [P, hQ]
  have h : ENNReal.ofReal (‖MvPolynomial.eval (Sum.elim (fun k => (v.1 k : ℂ)) (fun k => (x.2.2.1 k : ℂ))) P‖ *
      ‖elementaryPartial f 0 0 v x.2.2.1 x.2.2.2‖) ≤ ENNReal.ofReal (S i f) := by
    rw [hval]
    exact le_iSup_of_le v (le_iSup_of_le x.2.2.1 (le_iSup_of_le x.2.2.2 le_rfl))
  rw [hP, Complex.norm_real, Real.norm_of_nonneg (by positivity), elementaryPartial_zero, he] at h
  exact (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp h

end

end Masullo
