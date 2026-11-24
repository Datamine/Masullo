import ElementarySchwartzSymbols
import ElementarySchwartzComplete
import Mathlib.Algebra.Order.Floor.Ring

open Filter Function Set Topology
open scoped BigOperators ContDiff ENNReal NNReal

namespace Masullo

noncomputable section

variable {m n r m' n' r' : ℕ} {F F' : Type*}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']

local notation "A" => ElementaryLCAModel m n r F
local notation "B" => ElementaryLCAModel m' n' r' F'
local notation "V" => Fin m ⊕ Fin r → ℝ
local notation "W" => Fin m' ⊕ Fin r' → ℝ

/-- Real and lattice coordinates, with the lattice embedded in its real span. -/
def elementaryGrowth (g : A) : V :=
  fun j ↦ elementaryGrowthCoordinate (n := n) (F := F) j g

theorem elementaryGrowth_continuous : Continuous (elementaryGrowth (m := m) (n := n) (r := r) (F := F)) :=
  continuous_pi fun j ↦ elementaryGrowthCoordinate_continuous j

private theorem elementaryGrowth_compact_closedBall (R : ℝ) :
    IsCompact ((elementaryGrowth (m := m) (n := n) (r := r) (F := F)) ⁻¹'
      Metric.closedBall (0 : V) R) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin m ↦ ℝ)
  let U := e.symm '' Metric.closedBall (0 : Fin m → ℝ) R
  let V₀ := Metric.closedBall (0 : Fin r → ℤ) R
  have hU : IsCompact U := (isCompact_closedBall _ _).image e.symm.continuous
  have hV : IsCompact V₀ := isCompact_closedBall _ _
  apply (hU.prod (isCompact_univ.prod (hV.prod isCompact_univ))).of_isClosed_subset
    (Metric.isClosed_closedBall.preimage elementaryGrowth_continuous)
  intro g hg
  change elementaryGrowth g ∈ Metric.closedBall _ R at hg
  have hnorm : ‖elementaryGrowth g‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hg
  have hR : 0 ≤ R := (norm_nonneg _).trans hnorm
  refine ⟨⟨e g.1, ?_, e.symm_apply_apply _⟩, mem_univ _, ?_, mem_univ _⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    exact (norm_le_pi_norm (elementaryGrowth g) (Sum.inl j)).trans hnorm
  · change g.2.2.1 ∈ Metric.closedBall _ R
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    exact (norm_le_pi_norm (elementaryGrowth g) (Sum.inr j)).trans hnorm

/-- A continuous homomorphism acts linearly on the real spans of the growth
coordinates. Its compact torus and finite coordinates have zero real image. -/
theorem elementaryGrowth_hom (φ : A →+ B) (hφ : Continuous φ) :
    ∃ L : V →L[ℝ] W, ∀ g, elementaryGrowth (φ g) = L (elementaryGrowth g) := by
  classical
  let q (j : Fin m' ⊕ Fin r') : A →+ ℝ := (elementaryGrowthCoordinate j).comp φ
  have hq (j) : Continuous (q j) := (elementaryGrowthCoordinate_continuous j).comp hφ
  choose a b h using fun j ↦ elementary_real_addHom_coordinates (q j) (hq j)
  let L₀ (j : Fin m' ⊕ Fin r') : V →ₗ[ℝ] ℝ :=
    (∑ i, a j i • LinearMap.proj (Sum.inl i)) + ∑ i, b j i • LinearMap.proj (Sum.inr i)
  let L : V →ₗ[ℝ] W := LinearMap.pi L₀
  refine ⟨⟨L, L.continuous_of_finiteDimensional⟩, fun g ↦ ?_⟩
  funext j
  change q j g = L₀ j (elementaryGrowth g)
  rw [h j g]
  simp [L₀, elementaryGrowth, elementaryGrowthCoordinate, LinearMap.sum_apply, smul_eq_mul] <;> rfl

/-- Rounding the lattice coordinates approximates every vector in its real
span within one unit in the sup norm. -/
private theorem elementaryGrowth_round (v : V) :
    ∃ g : A, ‖elementaryGrowth g - v‖ ≤ 1 := by
  let g : A := (WithLp.toLp 2 (fun i ↦ v (.inl i)), 0, fun i ↦ ⌊v (.inr i)⌋, 0)
  refine ⟨g, (pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_⟩
  intro j
  cases j with
  | inl i =>
    change ‖v (.inl i) - v (.inl i)‖ ≤ 1
    simp
  | inr i =>
    change ‖(⌊v (.inr i)⌋ : ℝ) - v (.inr i)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [Int.lt_floor_add_one (v (.inr i))],
      by linarith [Int.floor_le (v (.inr i))]⟩

/-- Properness on the elementary groups forces injectivity on the real growth
spans. A ray in the linear kernel could otherwise be rounded to an unbounded
sequence with image in one compact set. -/
theorem elementaryGrowth_linear_injective_of_proper (φ : A →+ B) (hp : IsProperMap φ)
    (L : V →L[ℝ] W) (hL : ∀ g, elementaryGrowth (φ g) = L (elementaryGrowth g)) :
    Injective L := by
  apply (LinearMap.ker_eq_bot.mp ?_)
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv₀ : L v = 0 := hv
  by_contra hn
  let K : Set B := elementaryGrowth ⁻¹' Metric.closedBall (0 : W) ‖L‖
  have hK : IsCompact K := elementaryGrowth_compact_closedBall _
  have hC := hp.isCompact_preimage hK
  obtain ⟨R, hR⟩ := ((hC.image elementaryGrowth_continuous).image continuous_norm).bddAbove
  have hBound (k : ℕ) : (k : ℝ) * ‖v‖ ≤ R + 1 := by
    obtain ⟨g, hg⟩ := elementaryGrowth_round (n := n) (F := F) ((k : ℝ) • v)
    have hImg : φ g ∈ K := by
      change dist (elementaryGrowth (φ g)) 0 ≤ ‖L‖
      rw [dist_zero_right, hL]
      have he : L (elementaryGrowth g - (k : ℝ) • v) = L (elementaryGrowth g) := by
        rw [map_sub, map_smul, hv₀, smul_zero, sub_zero]
      rw [← he]
      exact (L.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_left hg (norm_nonneg L))
    have hgR : ‖elementaryGrowth g‖ ≤ R :=
      hR ⟨elementaryGrowth g, ⟨g, hImg, rfl⟩, rfl⟩
    have h := norm_add_le (elementaryGrowth g) ((k : ℝ) • v - elementaryGrowth g)
    rw [add_sub_cancel, norm_sub_rev, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)] at h
    exact h.trans (add_le_add hgR hg)
  have hPos := norm_pos_iff.mpr hn
  obtain ⟨k, hk⟩ := exists_nat_gt ((R + 1) / ‖v‖)
  exact (not_lt_of_ge (hBound k)) ((div_lt_iff₀ hPos).mp hk)

local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')

private theorem elementaryCoverHom_isOpenMap :
    IsOpenMap (elementaryCoverHom (m := m) (n := n) (r := r) (F := F)) := by
  let q : X × ((Fin r → ℤ) × F) → A := fun p ↦ elementaryCover p.1 p.2.1 p.2.2
  intro U hU
  have h := (elementaryCover_openQuotientMap (m := m) (n := n) (r := r) (F := F)).isOpenMap
    (U ×ˢ {(0 : (Fin r → ℤ) × F)}) (hU.prod (isOpen_discrete _))
  convert h using 1
  ext g
  change g ∈ elementaryCoverHom '' U ↔ g ∈ q '' (U ×ˢ {(0 : (Fin r → ℤ) × F)})
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x, 0), ⟨hx, mem_singleton 0⟩, rfl⟩
  · rintro ⟨⟨x, d⟩, ⟨hx, hd⟩, rfl⟩
    rcases mem_singleton_iff.mp hd with rfl
    exact ⟨x, hx, rfl⟩

private theorem elementaryCoverHom_locallyInjective_at_zero :
    ∃ U : Set X, IsOpen U ∧ 0 ∈ U ∧
      InjOn (elementaryCoverHom (m := m) (n := n) (r := r) (F := F)) U := by
  obtain ⟨R, hW, hz, hinj⟩ := (AddCircle.isLocalHomeomorph_coe (p := (1 : ℝ))).isLocallyInjective 0
  let U := ⋂ i : Fin n, (fun x : X ↦ x.2 i) ⁻¹' R
  refine ⟨U, isOpen_iInter_of_finite (fun i ↦
    hW.preimage ((PiLp.continuous_apply 2 _ i).comp continuous_snd)),
    mem_iInter.mpr (fun _ ↦ hz), fun x hx y hy he ↦ ?_⟩
  apply Prod.ext
  · exact congrArg (fun g : A ↦ g.1) he
  · apply (EuclideanSpace.equiv (Fin n) ℝ).injective
    funext i
    exact hinj (mem_iInter.mp hx i) (mem_iInter.mp hy i) (congrArg (fun g : A ↦ g.2.1 i) he)

/-- A continuous homomorphism between elementary groups lifts to a linear
map on their covering vector spaces. When the homomorphism is open, the
lift is surjective. -/
theorem elementaryCoverHom_lift_of_open (φ : A →+ B) (hφ : Continuous φ) (hopen : IsOpenMap φ) :
    ∃ L : X →L[ℝ] Y, Surjective L ∧
      ∀ x, φ (elementaryCoverHom x) = elementaryCoverHom (L x) := by
  obtain ⟨L, hL⟩ := elementaryCover_hom_affine φ hφ
  obtain ⟨y, a, b, he⟩ := hL 0 0
  have hz : elementaryCover y a b = (0 : B) := by
    have h₀ := he 0
    change φ (elementaryCoverHom 0) = elementaryCover (L 0 + y) a b at h₀
    simpa only [map_zero, zero_add] using h₀.symm
  have hf (x : X) : φ (elementaryCoverHom x) = elementaryCoverHom (L x) := by
    change φ (elementaryCover x 0 0) = _
    rw [he, add_comm (L x), elementaryCover_add, hz, zero_add]
  refine ⟨L, ?_, hf⟩
  obtain ⟨U, hU, hZero, hinj⟩ := elementaryCoverHom_locallyInjective_at_zero
    (m := m') (n := n') (r := r') (F := F')
  let T : Set X := L ⁻¹' U
  have hT : IsOpen T := hU.preimage L.continuous
  have hq : IsOpenMap (elementaryCoverHom (m := m) (n := n) (r := r) (F := F)) :=
    elementaryCoverHom_isOpenMap
  let q : Y → B := elementaryCoverHom
  have hOpen : IsOpen (q '' (L '' T)) := by
    have h := (hopen.comp hq) T hT
    rw [← image_comp]
    exact (show φ ∘ (elementaryCoverHom : X → A) = q ∘ L from funext hf) ▸ h
  have hEq : L '' T = U ∩ q ⁻¹' (q '' (L '' T)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, mem_image_of_mem q (mem_image_of_mem L hx)⟩
    · rintro ⟨hzU, v, ⟨x, hx, rfl⟩, hv⟩
      exact ⟨x, hx, hinj hx hzU hv⟩
  have hImage : IsOpen (L '' T) :=
    hEq.symm ▸ hU.inter (hOpen.preimage elementaryCoverHom_continuous)
  have hzero : (0 : Y) ∈ L '' T := ⟨0, by simpa [T] using hZero, map_zero _⟩
  let H := L.toLinearMap.range.toAddSubgroup
  have hH : IsOpen (H : Set Y) := H.isOpen_of_mem_nhds
    (mem_of_superset (hImage.mem_nhds hzero) (image_subset_range _ _))
  have hWhole := (show IsClopen (H : Set Y) from ⟨H.isClosed_of_isOpen hH, hH⟩).eq_univ
    ⟨0, H.zero_mem⟩
  intro z
  have hz : z ∈ (H : Set Y) := hWhole.symm ▸ mem_univ z
  exact hz

/-- The one-parameter subgroup obtained by composing with an elementary homomorphism. -/
def elementaryMapDirection (φ : A →+ B) (hφ : Continuous φ) (c : Multiplicative ℝ →ₜ* Multiplicative A) :
    Multiplicative ℝ →ₜ* Multiplicative B :=
  (⟨φ.toMultiplicative, hφ⟩ : Multiplicative A →ₜ* Multiplicative B).comp c

theorem elementaryMapDirection_surjective (φ : A →+ B) (hφ : Continuous φ)
    (hopen : IsOpenMap φ) : Surjective (elementaryMapDirection φ hφ) := by
  obtain ⟨L, hs, hL⟩ := elementaryCoverHom_lift_of_open φ hφ hopen
  intro c
  obtain ⟨v, hv⟩ := elementaryOneParameter_lift c
  obtain ⟨w, hw⟩ := hs v
  refine ⟨elementaryOneParameter w, ?_⟩
  apply ContinuousMonoidHom.ext
  intro t
  apply Multiplicative.toAdd.injective
  change φ (elementaryCoverHom (t.toAdd • w)) = (c t).toAdd
  rw [hL, map_smul, hw]
  exact (hv t.toAdd).symm

private theorem elementaryOrbitWord_pullback (φ : A →+ B) (hφ : Continuous φ)
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative A)) (f : B → ℂ) :
    elementaryOrbitWord cs (f ∘ φ) =
      elementaryOrbitWord (cs.map (elementaryMapDirection φ hφ)) f ∘ φ := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, elementaryOrbitWord, ih]
    funext x
    unfold elementaryOrbitDeriv
    congr 1
    funext t
    change elementaryOrbitWord (cs.map (elementaryMapDirection φ hφ)) f
      (φ (x + (c (Multiplicative.ofAdd t)).toAdd)) =
      elementaryOrbitWord (cs.map (elementaryMapDirection φ hφ)) f
        (φ x + φ (c (Multiplicative.ofAdd t)).toAdd)
    rw [map_add]


theorem elementaryGrowthVariables_eq (g : A) :
    elementaryGrowthVariables g = fun j ↦ (elementaryGrowth g j : ℂ) := by
  funext j
  cases j <;> rfl

/-- Substitute a real linear map in a monomial. -/
theorem linear_growth_monomial {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (d : κ → ℕ) :
    ∃ P : MvPolynomial ι ℂ, ∀ x : ι → ℝ,
      MvPolynomial.eval (fun j ↦ (x j : ℂ)) P = ∏ j, (L x j : ℂ) ^ d j := by
  classical
  let P (j : κ) : MvPolynomial ι ℂ :=
    ∑ i, MvPolynomial.C (L (Pi.single (M := fun _ : ι ↦ ℝ) i 1) j : ℂ) * MvPolynomial.X i
  refine ⟨∏ j, P j ^ d j, fun x ↦ ?_⟩
  simp only [map_prod, map_pow]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  have h : L x j = ∑ i, x i * L (Pi.single (M := fun _ : ι ↦ ℝ) i 1) j := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, h,
    Complex.ofReal_sum, Complex.ofReal_mul, mul_comm]

private theorem elementarySchwartz_properPullback_bound (φ : A →+ B) (hp : IsProperMap φ)
    (i : ElementarySchwartzIndex m n r) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m' n' r' F'), Continuous q ∧
      ∀ f : ElementarySchwartz m' n' r' F',
        elementarySchwartzBound (f ∘ φ) i ≤ ENNReal.ofReal (q f) := by
  obtain ⟨L, hL⟩ := elementaryGrowth_hom φ hp.continuous
  have hi := elementaryGrowth_linear_injective_of_proper φ hp L hL
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  have hBack (g : A) : R (elementaryGrowth (φ g)) = elementaryGrowth g := by
    rw [hL]
    exact DFunLike.congr_fun hR (elementaryGrowth g)
  obtain ⟨p, hp'⟩ := linear_growth_monomial R (Sum.elim i.1 i.2.2.2)
  obtain ⟨cs, hcs⟩ := elementaryOrbitWord_partial (r := r) (F := F) i.2.1 i.2.2.1
  obtain ⟨q, hq, hBound⟩ := elementary_polynomialWord_bound
    (cs.map (elementaryMapDirection φ hp.continuous)) p
  refine ⟨q, hq, fun f ↦ ?_⟩
  have hs := elementaryContDiff_hom φ hp.continuous f f.property.1
  unfold elementarySchwartzBound
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  let g := elementaryCover x a b
  have hw : MvPolynomial.eval (elementaryGrowthVariables (φ g)) p =
      (∏ k, (x.1 k : ℂ) ^ i.1 k) * (∏ k, (a k : ℂ) ^ i.2.2.2 k) := by
    rw [elementaryGrowthVariables_eq, hp', hBack, Fintype.prod_sum_type]
    rfl
  have hd : elementaryOrbitWord (cs.map (elementaryMapDirection φ hp.continuous)) f (φ g) =
      elementaryPartial (f ∘ φ) i.2.1 i.2.2.1 x a b :=
    (congrFun (elementaryOrbitWord_pullback φ hp.continuous cs f) g).symm.trans
      (hcs (f ∘ φ) hs x a b)
  have hb := hBound f (φ g)
  rw [hw, hd] at hb
  exact hb

/-- Proper pullback is a continuous linear map on the elementary Schwartz spaces. -/
def elementarySchwartz_properPullback (φ : A →+ B) (hp : IsProperMap φ) :
    ElementarySchwartz m' n' r' F' →L[ℂ] ElementarySchwartz m n r F := by
  let L : ElementarySchwartz m' n' r' F' →ₗ[ℂ] ElementarySchwartz m n r F :=
    { toFun := fun f ↦ ⟨f ∘ φ, elementaryContDiff_hom φ hp.continuous f f.property.1, fun i ↦ by
        obtain ⟨q, _, hq⟩ := elementarySchwartz_properPullback_bound φ hp i
        exact (hq f).trans_lt ENNReal.ofReal_lt_top⟩
      map_add' _ _ := Subtype.ext rfl
      map_smul' _ _ := Subtype.ext rfl }
  refine ⟨L, ?_⟩
  apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp
  intro i
  obtain ⟨q, hq, hBound⟩ := elementarySchwartz_properPullback_bound φ hp i
  refine Seminorm.continuous_of_le hq fun f ↦ ?_
  change (elementarySchwartzBound (f ∘ φ) i).toReal ≤ q f
  simpa only [ENNReal.toReal_ofReal (apply_nonneg q f)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hBound f)

@[simp] theorem elementarySchwartz_properPullback_apply
    (φ : A →+ B) (hp : IsProperMap φ) (f : ElementarySchwartz m' n' r' F') (x : A) :
    elementarySchwartz_properPullback φ hp f x = f (φ x) := rfl


private theorem elementaryOrbitWord_zero_off_range
    (φ : A →+ B) (hφ : Continuous φ) (ho : IsOpenMap φ)
    (cs : List (Multiplicative ℝ →ₜ* Multiplicative B)) (f : B → ℂ)
    (hf : ∀ y ∉ range φ, f y = 0) :
    ∀ y ∉ range φ, elementaryOrbitWord cs f y = 0 := by
  induction cs with
  | nil => exact hf
  | cons c cs ih =>
    obtain ⟨d, hd⟩ := elementaryMapDirection_surjective φ hφ ho c
    intro y hy
    have he : (fun t : ℝ ↦ elementaryOrbitWord cs f (y + (c (Multiplicative.ofAdd t)).toAdd)) =
        fun _ ↦ 0 := by
      funext t
      apply ih
      rintro ⟨x, hx⟩
      apply hy
      let z := (d (Multiplicative.ofAdd t)).toAdd
      have hr : (c (Multiplicative.ofAdd t)).toAdd = φ z := by
        rw [← hd]
        rfl
      rw [hr] at hx
      refine ⟨x - z, ?_⟩
      rw [map_sub, hx, add_sub_cancel_right]
    simp [elementaryOrbitWord, elementaryOrbitDeriv, he]

/-- Fibre regularity descends through an open homomorphism and extends by zero
off its open image. -/
theorem elementaryContDiff_of_open {s : WithTop ℕ∞} (φ : A →+ B) (hφ : Continuous φ) (ho : IsOpenMap φ)
    (f : A → ℂ) (h : B → ℂ)
    (hf : ∀ a b, ContDiff ℝ s (fun u ↦ f (elementaryCover u a b)))
    (he : h ∘ φ = f) (hz : ∀ y ∉ range φ, h y = 0) :
    ∀ a b, ContDiff ℝ s (fun u ↦ h (elementaryCover u a b)) := by
  obtain ⟨L, hL, hComm⟩ := elementaryCoverHom_lift_of_open φ hφ ho
  obtain ⟨R, hR⟩ := L.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  have hLift (u : Y) : φ (elementaryCoverHom (R u)) = elementaryCoverHom u := by
    rw [hComm]
    exact congrArg elementaryCoverHom (DFunLike.congr_fun hR u)
  intro a b
  let y := elementaryCover (0 : Y) a b
  have hTranslate (u : Y) : elementaryCover u a b = y + elementaryCoverHom u := by
    simpa only [zero_add] using elementaryCover_add (0 : Y) u a b
  by_cases hy : y ∈ range φ
  · obtain ⟨x, hx⟩ := hy
    obtain ⟨w, hw⟩ := elementaryCover_surjective x.2.2.1 x.2.2.2 x.1 x.2.1
    change elementaryCover (x.1, w) x.2.2.1 x.2.2.2 = x at hw
    have hEq : (fun u ↦ h (elementaryCover u a b)) =
        fun u ↦ f (elementaryCover ((x.1, w) + R u) x.2.2.1 x.2.2.2) := by
      funext u
      rw [hTranslate, ← hx, ← hLift, ← map_add]
      change (h ∘ φ) _ = _
      rw [he, elementaryCover_add, hw]
    rw [hEq]
    exact (hf _ _).comp (contDiff_const.add R.contDiff)
  · have hZero : (fun u ↦ h (elementaryCover u a b)) = fun _ ↦ 0 := by
      funext u
      apply hz
      rintro ⟨x, hx⟩
      apply hy
      rw [hTranslate, ← hLift] at hx
      exact ⟨x - elementaryCoverHom (R u), by rw [map_sub, hx, add_sub_cancel_right]⟩
    rw [hZero]
    exact contDiff_const

private theorem elementarySchwartz_openDescent_bound (φ : A →+ B)
    (hφ : Continuous φ) (ho : IsOpenMap φ) (i : ElementarySchwartzIndex m' n' r') :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧
      ∀ (f : ElementarySchwartz m n r F) (h : B → ℂ),
        h ∘ φ = f → (∀ y ∉ range φ, h y = 0) →
          elementarySchwartzBound h i ≤ ENNReal.ofReal (q f) := by
  obtain ⟨L, hL⟩ := elementaryGrowth_hom φ hφ
  obtain ⟨p, hp⟩ := linear_growth_monomial L.toLinearMap (Sum.elim i.1 i.2.2.2)
  obtain ⟨cs, hcs⟩ := elementaryOrbitWord_partial (r := r') (F := F') i.2.1 i.2.2.1
  obtain ⟨ds, hds⟩ := (List.map_surjective_iff.mpr (elementaryMapDirection_surjective φ hφ ho)) cs
  obtain ⟨q, hq, hBound⟩ := elementary_polynomialWord_bound ds p
  refine ⟨q, hq, fun f h he hz ↦ ?_⟩
  have hs := elementaryContDiff_of_open φ hφ ho f h f.property.1 he hz
  unfold elementarySchwartzBound
  refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  let y := elementaryCover x a b
  by_cases hy : y ∈ range φ
  · obtain ⟨z, hz'⟩ := hy
    have hw : MvPolynomial.eval (elementaryGrowthVariables z) p =
        (∏ k, (x.1 k : ℂ) ^ i.1 k) * (∏ k, (a k : ℂ) ^ i.2.2.2 k) := by
      rw [elementaryGrowthVariables_eq, hp, ← (show elementaryGrowth (φ z) = L.toLinearMap (elementaryGrowth z) from hL z), hz', Fintype.prod_sum_type]
      rfl
    have hd : elementaryOrbitWord ds f z = elementaryPartial h i.2.1 i.2.2.1 x a b := by
      rw [← he, elementaryOrbitWord_pullback φ hφ ds h, hds]
      change elementaryOrbitWord cs h (φ z) = _
      rw [hz']
      exact hcs h hs x a b
    have hb := hBound f z
    rw [hw, hd] at hb
    exact hb
  · have hzero := elementaryOrbitWord_zero_off_range φ hφ ho cs h hz y hy
    rw [hcs h hs x a b] at hzero
    rw [hzero, mul_zero, nnnorm_zero, NNReal.coe_zero]
    exact apply_nonneg q f

/-- A Schwartz function that descends through an open surjection is
Schwartz on the target elementary group. -/
theorem elementarySchwartz_mem_of_openPullback (φ : A →+ B) (hφ : Continuous φ)
    (ho : IsOpenMap φ) (hs : Surjective φ)
    (f : ElementarySchwartz m n r F) (g : B → ℂ) (he : g ∘ φ = f) :
    g ∈ elementarySchwartzSubmodule m' n' r' F' := by
  have hz (y : B) (hy : y ∉ range φ) : g y = 0 := (hy (hs y)).elim
  refine ⟨elementaryContDiff_of_open φ hφ ho f g f.property.1 he hz, fun i => ?_⟩
  obtain ⟨q, _, hq⟩ := elementarySchwartz_openDescent_bound φ hφ ho i
  exact (hq f g he hz).trans_lt ENNReal.ofReal_lt_top

/-- Pullback along a proper, open surjection embeds the elementary Schwartz space. -/
theorem elementarySchwartz_properPullback_isClosedEmbedding (φ : A →+ B) (hp : IsProperMap φ)
    (ho : IsOpenMap φ) (hs : Surjective φ) :
    IsClosedEmbedding (elementarySchwartz_properPullback φ hp) := by
  let T := elementarySchwartz_properPullback φ hp
  have hInjective : Injective T := by
    intro f g h
    apply Subtype.ext
    funext y
    obtain ⟨x, rfl⟩ := hs y
    exact congrArg (fun u : ElementarySchwartz m n r F ↦ u x) h
  let e := LinearEquiv.ofInjective T.toLinearMap hInjective
  have hBack : Continuous e.symm := by
    apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp
    intro i
    obtain ⟨q, hq, hBound⟩ := elementarySchwartz_openDescent_bound φ hp.continuous ho i
    have hc : Continuous (q.comp T.toLinearMap.range.subtype) := hq.comp continuous_subtype_val
    refine Seminorm.continuous_of_le hc fun f ↦ ?_
    have hEq : (e.symm f : B → ℂ) ∘ φ = f.val := by
      have he := congrArg Subtype.val (e.apply_symm_apply f)
      exact congrArg Subtype.val he
    have hle := hBound f.val (e.symm f) hEq (fun y hy ↦ (hy (hs y)).elim)
    change (elementarySchwartzBound (e.symm f).val i).toReal ≤ q f.val
    simpa only [ENNReal.toReal_ofReal (apply_nonneg q f.val)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  let E : _ ≃L[ℂ] _ :=
    { toLinearEquiv := e
      continuous_toFun := T.continuous.subtype_mk _
      continuous_invFun := hBack }
  have hemb : IsEmbedding T := IsEmbedding.subtypeVal.comp E.toHomeomorph.isEmbedding
  letI : CompleteSpace (ElementarySchwartz m' n' r' F') := completeSpace_elementarySchwartz
  letI : T2Space (ElementarySchwartz m n r F) := elementarySchwartz_t2
  exact (AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := T) hemb).isClosedEmbedding

private def elementaryOpenExtension (φ : A →+ B) (f : A → ℂ) (y : B) : ℂ := by
  classical
  exact if h : y ∈ range φ then f (Classical.choose h) else 0

private theorem elementaryOpenExtension_comp (φ : A →+ B) (hi : Injective φ) (f : A → ℂ) :
    elementaryOpenExtension φ f ∘ φ = f := by
  funext x
  classical
  unfold Function.comp elementaryOpenExtension
  have hx : φ x ∈ range φ := mem_range_self x
  rw [dite_eq_left hx, hi (Classical.choose_spec hx)]

private theorem elementaryOpenExtension_off_range (φ : A →+ B) (f : A → ℂ) :
    ∀ y ∉ range φ, elementaryOpenExtension φ f y = 0 := by
  intro y hy
  simp [elementaryOpenExtension, hy]

/-- Extension by zero through an open embedding is continuous and linear. -/
def elementarySchwartz_extendOpen (φ : A →+ B) (hφ : Continuous φ)
    (ho : IsOpenMap φ) (hi : Injective φ) :
    ElementarySchwartz m n r F →L[ℂ] ElementarySchwartz m' n' r' F' := by
  let L : ElementarySchwartz m n r F →ₗ[ℂ] ElementarySchwartz m' n' r' F' :=
    { toFun := fun f ↦ ⟨elementaryOpenExtension φ f,
        elementaryContDiff_of_open φ hφ ho f _ f.property.1
          (elementaryOpenExtension_comp φ hi f) (elementaryOpenExtension_off_range φ f),
        fun i ↦ by
          obtain ⟨q, _, hq⟩ := elementarySchwartz_openDescent_bound φ hφ ho i
          exact (hq f _ (elementaryOpenExtension_comp φ hi f)
            (elementaryOpenExtension_off_range φ f)).trans_lt ENNReal.ofReal_lt_top⟩
      map_add' f g := by
        apply Subtype.ext
        funext y
        change elementaryOpenExtension φ (f.val + g.val) y =
          elementaryOpenExtension φ f.val y + elementaryOpenExtension φ g.val y
        classical
        by_cases hy : y ∈ range φ <;> simp [elementaryOpenExtension, hy]
      map_smul' c f := by
        apply Subtype.ext
        funext y
        change elementaryOpenExtension φ (c • f.val) y = c • elementaryOpenExtension φ f.val y
        classical
        by_cases hy : y ∈ range φ <;> simp [elementaryOpenExtension, hy] }
  refine ⟨L, ?_⟩
  apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp
  intro i
  obtain ⟨q, hq, hBound⟩ := elementarySchwartz_openDescent_bound φ hφ ho i
  refine Seminorm.continuous_of_le hq fun f ↦ ?_
  change (elementarySchwartzBound (elementaryOpenExtension φ f) i).toReal ≤ q f
  simpa only [ENNReal.toReal_ofReal (apply_nonneg q f)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hBound f _ (elementaryOpenExtension_comp φ hi f) (elementaryOpenExtension_off_range φ f))

theorem elementarySchwartz_extendOpen_comp (φ : A →+ B) (hφ : Continuous φ)
    (ho : IsOpenMap φ) (hi : Injective φ) (f : ElementarySchwartz m n r F) :
    (elementarySchwartz_extendOpen φ hφ ho hi f : B → ℂ) ∘ φ = f :=
  elementaryOpenExtension_comp φ hi f

theorem elementarySchwartz_extendOpen_off_range (φ : A →+ B) (hφ : Continuous φ)
    (ho : IsOpenMap φ) (hi : Injective φ) (f : ElementarySchwartz m n r F) :
    ∀ y ∉ range φ, elementarySchwartz_extendOpen φ hφ ho hi f y = 0 :=
  elementaryOpenExtension_off_range φ f

/-- Extension by zero is also a closed topological embedding. -/
theorem elementarySchwartz_extendOpen_isClosedEmbedding (φ : A →+ B) (hφ : Continuous φ)
    (ho : IsOpenMap φ) (hi : Injective φ) :
    IsClosedEmbedding (elementarySchwartz_extendOpen φ hφ ho hi) := by
  let T := elementarySchwartz_extendOpen φ hφ ho hi
  have hopen : IsOpen (φ.range : Set B) := by
    rw [AddMonoidHom.coe_range, ← image_univ]
    exact ho _ isOpen_univ
  have hphi : IsClosedEmbedding φ :=
    ⟨(IsOpenEmbedding.of_continuous_injective_isOpenMap hφ hi ho).isEmbedding,
      φ.range.isClosed_of_isOpen hopen⟩
  let R := elementarySchwartz_properPullback φ hphi.isProperMap
  have hLeft : LeftInverse R T := fun f ↦ Subtype.ext (elementarySchwartz_extendOpen_comp φ hφ ho hi f)
  have hemb := hLeft.isEmbedding R.continuous T.continuous
  letI : CompleteSpace (ElementarySchwartz m n r F) := completeSpace_elementarySchwartz
  letI : T2Space (ElementarySchwartz m' n' r' F') := elementarySchwartz_t2
  exact (AddMonoidHom.isUniformEmbedding_of_isEmbedding (f := T) hemb).isClosedEmbedding


/-- The two-torsion of the one-dimensional torus is a nontrivial proper
compact subgroup. It cannot be a product of whole torus factors in this model. -/
theorem circle_twoTorsion_compact_proper :
    ∃ K : AddSubgroup (AddCircle (1 : ℝ)), IsCompact (K : Set (AddCircle (1 : ℝ))) ∧
      K ≠ ⊥ ∧ K ≠ ⊤ := by
  let C := AddCircle (1 : ℝ)
  let K : AddSubgroup C := (2 • AddMonoidHom.id C).ker
  have hMem (x : C) : x ∈ K ↔ x + x = 0 := by
    change (2 • AddMonoidHom.id C) x = 0 ↔ _
    simp [two_nsmul]
  have hHalf : ((1 / 2 : ℝ) : C) ≠ 0 := by
    intro h
    obtain ⟨j, hj⟩ := ((AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h)
    have h' : (j : ℝ) = 1 / 2 := by simpa [zsmul_eq_mul] using hj
    have h₀ : 0 < j := by exact_mod_cast (show (0 : ℝ) < (j : ℝ) by linarith)
    have h₁ : j < 1 := by exact_mod_cast (show (j : ℝ) < 1 by linarith)
    omega
  refine ⟨K, ?_, ?_, ?_⟩
  · rw [show (K : Set C) = {x | x + x = 0} from Set.ext hMem]
    exact (isClosed_eq (continuous_id.add continuous_id) continuous_const).isCompact
  · intro he
    have h : (((1 / 2 : ℝ) : C)) ∈ K := by
      apply (hMem _).mpr
      rw [← AddCircle.coe_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
      exact AddCircle.coe_period (1 : ℝ)
    rw [he] at h
    exact hHalf h
  · intro he
    have h : ((1 / 4 : ℝ) : C) ∈ K := he.symm ▸ AddSubgroup.mem_top _
    replace h := (hMem _).mp h
    rw [← AddCircle.coe_add, show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num] at h
    exact hHalf h


end

end Masullo
