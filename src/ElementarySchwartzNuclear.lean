import ElementarySchwartz
import DerivativeUnitCube
import NuclearSignedSums
import Mathlib.Analysis.PSeries
import Mathlib.Data.Set.Finite.List

/-!
# Nuclearity of elementary Schwartz spaces

The weighted cube estimates adapt the Apache-2.0 proof in
`RiemannMasullo/AppD_SchwartzBruhat/Sec1b.lean` at
`23cbb63d9a34c2ae8ab0ebd86074ea4c2a056978`.
-/

open Filter Function Set Topology
open scoped ContDiff ENNReal NNReal

namespace Masullo

noncomputable section

universe u v

/-- The product of the one-dimensional summable lattice weights is summable
over every finite product of integer lattices. -/
theorem summable_lattice_product {J : Type*} [Fintype J] :
    Summable (fun k : J → ℤ ↦ ∏ j, (1 + (k j : ℝ)^2)⁻¹) := by
  classical
  have h₁ : Summable (fun k : ℤ ↦ (1 + (k : ℝ)^2)⁻¹) := by
    have h := (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
    apply (summable_of_ne_finset_zero (s := ({0} : Finset ℤ)) (f := fun k : ℤ ↦ if k = 0 then (1:ℝ) else 0)
      (by simp)).add h |>.of_nonneg_of_le (fun _ ↦ by positivity)
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · simp only [ite_eq_right hk, zero_add, one_div]
      exact inv_anti₀ (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hk)) (by linarith)
  have hFin (n : ℕ) : Summable (fun k : Fin n → ℤ ↦ ∏ i, (1 + (k i : ℝ)^2)⁻¹) := by
    induction n with
    | zero => exact .of_finite
    | succ n ih =>
      have h := h₁.mul_of_nonneg ih (fun _ ↦ by positivity) (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ by positivity)
      apply (Fin.consEquiv (fun _ : Fin (n+1) ↦ ℤ)).summable_iff.mp
      simpa [Function.comp_def, Fin.prod_univ_succ, mul_comm] using h
  let e := Fintype.equivFin J
  let t := Equiv.arrowCongr e (Equiv.refl ℤ)
  apply (t.summable_iff.mpr (hFin (Fintype.card J))).congr
  intro k
  change (∏ i, (1 + (k (e.symm i) : ℝ)^2)⁻¹) = _
  exact e.symm.prod_comp (fun i ↦ (1 + (k i : ℝ)^2)⁻¹)

private def schwartzCubeWeight {J : Type*} [Fintype J] (d : J → ℕ) (k : J → ℤ) : ℝ :=
  ∏ j, ((2 * (1 + (k j : ℝ)^2))^(d j) * (1 + (k j : ℝ)^2))

private def schwartzCubePolynomial {J : Type*} [Fintype J] (d : J → ℕ) : MvPolynomial J ℂ :=
  ∏ j, (8 * (1 + MvPolynomial.X j ^ 2))^(d j + 1)

/-- A single positive polynomial controls the lattice weight throughout the unit cube. -/
private theorem schwartzCubeWeight_le {J : Type*} [Fintype J] (d : J → ℕ) (k : J → ℤ)
    (x : J → ℝ) (hx : ∀ j, (k j : ℝ) ≤ x j ∧ x j ≤ k j + 1) :
    schwartzCubeWeight d k ≤ ‖MvPolynomial.eval (fun j ↦ (x j : ℂ)) (schwartzCubePolynomial d)‖ := by
  unfold schwartzCubeWeight schwartzCubePolynomial
  rw [map_prod, norm_prod]
  apply Finset.prod_le_prod (fun j _ ↦ by positivity) (fun j _ ↦ ?_)
  have hpos : 0 ≤ 8 * (1 + x j ^ 2) := by positivity
  have he : MvPolynomial.eval (fun j ↦ (x j : ℂ)) (8 * (1 + MvPolynomial.X j ^ 2)) =
      ((8 * (1 + x j ^ 2) : ℝ) : ℂ) := by simp
  rw [map_pow, he, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos, pow_succ]
  have hsmall : (k j : ℝ)^2 ≤ 2*x j^2 + 2 := by
    have hl := mul_nonneg (sub_nonneg.mpr (hx j).1) (sub_nonneg.mpr (hx j).2)
    nlinarith [sq_nonneg (x j - ((k j : ℝ) - x j))]
  have h₁ : 0 ≤ 2 * (1 + (k j : ℝ)^2) := by positivity
  have h₂ : 2 * (1+(k j : ℝ)^2) ≤ 8*(1+x j^2) := by linarith [sq_nonneg (x j)]
  exact mul_le_mul (pow_le_pow_left₀ h₁ h₂ (d j)) (by linarith [sq_nonneg (k j : ℝ)]) (by exact add_nonneg zero_le_one (sq_nonneg (k j : ℝ))) (pow_nonneg hpos _)

/-- Multiplying by a coordinate monomial spends only the polynomial part of the
weight, leaving a summable factor on the cube labels. -/
private theorem schwartzCube_monomial_weight {J : Type*} [Fintype J] (d : J → ℕ) (k : J → ℤ)
    (x : J → ℝ) (hx : ∀ j, (k j : ℝ) ≤ x j ∧ x j ≤ k j + 1) :
    (∏ j, |x j|^d j) ≤ (∏ j, (1 + (k j : ℝ)^2)⁻¹) * schwartzCubeWeight d k := by
  rw [schwartzCubeWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun j _ ↦ ?_)
  rw [mul_left_comm, inv_mul_cancel₀ (by positivity), mul_one]
  apply pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨?_,?_⟩)
  · linarith [(hx j).1, sq_nonneg ((k j : ℝ)+1), sq_nonneg (k j : ℝ)]
  · linarith [(hx j).2, sq_nonneg ((k j : ℝ)-1), sq_nonneg (k j : ℝ)]

/-- Evaluation of a higher derivative on fixed vectors is a fixed finite
linear combination of coordinate partials. -/
private theorem elementary_iterated_expansion {m n r k : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (v : Fin k → EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    ∃ (s : Finset ((Fin m → ℕ) × (Fin n → ℕ))) (c : ((Fin m → ℕ) × (Fin n → ℕ)) → ℝ),
      ∀ (f : ElementaryLCAModel m n r F → ℂ) a b,
      ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x a b)) → ∀ x,
        iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x v =
          ∑ p ∈ s, c p • elementaryPartial f p.1 p.2 x a b := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let J := Fin m ⊕ Fin n
  let B := elementaryFibreBasis m n
  let T := Fin k → J
  choose β γ hpartial using fun t : T ↦ elementaryIteratedFDeriv_basis
    (m := m) (n := n) (r := r) (F := F) t
  let indices (t : T) := (β t, γ t)
  let coeff (t : T) := ∏ i, B.repr (v i) (t i)
  let s := Finset.univ.image indices
  refine ⟨s, fun p ↦ ∑ t ∈ Finset.univ.filter (fun t ↦ indices t = p), coeff t, ?_⟩
  intro f a b hf x
  let D := iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x
  have hterm (t : T) : D (fun i ↦ B (t i)) =
      elementaryPartial f (indices t).1 (indices t).2 x a b :=
    hpartial t f a b hf x
  change D.toMultilinearMap v = _
  conv_lhs => rw [show v = (fun i ↦ ∑ j, B.repr (v i) j • B j) from
    funext fun i ↦ (B.sum_repr (v i)).symm]
  rw [D.toMultilinearMap.map_sum]
  simp_rw [D.toMultilinearMap.map_smul_univ, ContinuousMultilinearMap.coe_coe,
    hterm, Finset.sum_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (t := s)
    (fun t _ ↦ Finset.mem_image_of_mem indices (Finset.mem_univ t))]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun t ht ↦ ?_
  rw [(Finset.mem_filter.mp ht).2]

/-- Choosing the opposite phase at each value of a functional realizes the sum
of their norms as the norm of one signed sum. -/
private theorem sum_norm_linear_signed {E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : E →ₗ[ℂ] ℂ) {n : ℕ} (f : Fin n → E) :
    ∃ c : Fin n → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧ ∑ i, ‖L (f i)‖ = ‖L (∑ i, c i • f i)‖ := by
  let c (i) : ℂ := (‖L (f i)‖ : ℂ) / L (f i)
  have hc (i) : ‖c i‖ ≤ 1 := by
    change ‖(‖L (f i)‖ : ℂ) / L (f i)‖ ≤ 1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self_le_one _
  have he (i) : c i * L (f i) = (‖L (f i)‖ : ℂ) := by
    by_cases h : L (f i) = 0
    · simp [c,h]
    · exact div_mul_cancel₀ _ h
  refine ⟨c,hc,?_⟩
  simp only [map_sum, map_smul, smul_eq_mul, he, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)]

/-- Each polynomially weighted directional derivative admits a neighborhood
bound for the sum of absolute evaluations at a common point. -/
private theorem elementary_signed_point_bound {m n r : ℕ} {F : Type u}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (p : MvPolynomial (Fin m ⊕ Fin r) ℂ)
    (v : List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :
    ∃ U ∈ 𝓝 (0 : ElementarySchwartz m n r F), ∀ (N : ℕ) (f : Fin N → ElementarySchwartz m n r F),
      (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
      ∀ x a b, ‖MvPolynomial.eval (Sum.elim (fun i ↦ (x.1 i : ℂ)) (fun j ↦ (a j : ℂ))) p‖ *
        ∑ i, ‖listDerivative (fun y ↦ f i (elementaryCover y a b)) v x‖ ≤ 1 := by
  classical
  let E := ElementarySchwartz m n r F
  obtain ⟨T, c, hT⟩ := elementary_iterated_expansion (r := r) (F := F) v.get
  choose q hq hqp using fun t : (Fin m → ℕ) × (Fin n → ℕ) ↦
    elementarySchwartz_polynomial_weight_continuous_seminorm (F := F) p t.1 t.2
  let Q : Seminorm ℂ E := ∑ t ∈ T, ‖c t‖₊ • q t
  have hQ : Continuous Q := Seminorm.continuous_finsetSum fun t _ ↦ (hq t).const_smul _
  refine ⟨Q.ball 0 1, Q.ball_mem_nhds hQ zero_lt_one, fun N f hcomb x a b ↦ ?_⟩
  let w := MvPolynomial.eval (Sum.elim (fun i ↦ (x.1 i : ℂ)) (fun j ↦ (a j : ℂ))) p
  choose L hL using fun t : (Fin m → ℕ) × (Fin n → ℕ) ↦
    elementaryPartial_evaluation_continuousLinear (F := F) t.1 t.2 x a b
  let D : E →ₗ[ℂ] ℂ := ∑ t ∈ T, (c t : ℂ) • (L t).toLinearMap
  have hD (s : E) : D s = listDerivative (fun y ↦ s (elementaryCover y a b)) v x := by
    rw [listDerivative, hT s.val a b (s.property.1 a b) x]
    simp [D, hL, Complex.real_smul]
  have hle (s : E) : ‖w‖ * ‖D s‖ ≤ Q s := by
    have hqv (t) : ‖w‖ * ‖L t s‖ ≤ q t s := by
      rw [hL]
      apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
      rw [hqp]
      exact le_iSup_of_le x (le_iSup_of_le a (le_iSup_of_le b le_rfl))
    change _ ≤ FunLike.coeAddMonoidHom _ _ _ (∑ t ∈ T, ‖c t‖₊ • q t) s
    rw [map_sum, Finset.sum_apply]
    simp only [D, LinearMap.sum_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg w)).trans
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht ↦ ?_
    rw [norm_smul, Complex.norm_real, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hqv t) (norm_nonneg _)
  obtain ⟨c', hc', hsum⟩ := sum_norm_linear_signed D f
  change ‖w‖ * _ ≤ _
  simp_rw [← hD, hsum]
  exact (hle _).trans (Q.mem_ball_zero.mp (hcomb c' hc')).le

/-- Assemble the real and torus coordinates of one unit cube. -/
private def schwartzCubeMap (m n : ℕ) : ((Fin m ⊕ Fin n) → ℝ) →L[ℝ]
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
  let getR := ContinuousLinearMap.pi (fun i : Fin m ↦ ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m ⊕ Fin n ↦ ℝ) (.inl i))
  let getT := ContinuousLinearMap.pi (fun j : Fin n ↦ ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m ⊕ Fin n ↦ ℝ) (.inr j))
  (((EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap).comp getR).prod
    (((EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap).comp getT)

private def schwartzCubeOrigin {m n r : ℕ} (k : (Fin m ⊕ Fin r) → ℤ) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) :=
  (WithLp.toLp 2 (fun i ↦ (k (.inl i) : ℝ)),0)

/-- On each real cube and lattice fibre a fixed extra polynomial weight
controls the sum of mixed partials even at independently chosen points. -/
private theorem elementary_signed_cube_bound {m n r : ℕ} {F : Type u}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (d : (Fin m ⊕ Fin r) → ℕ) (v : List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :
    ∃ U ∈ 𝓝 (0 : ElementarySchwartz m n r F), ∀ (N : ℕ) (f : Fin N → ElementarySchwartz m n r F),
      (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
      ∀ (k : (Fin m ⊕ Fin r) → ℤ) b (u : Fin N → (Fin m ⊕ Fin n) → ℝ), (∀ i j, u i j ∈ Icc 0 1) →
      ∑ i, ‖listDerivative (fun x ↦ f i (elementaryCover x (fun j ↦ k (.inr j)) b)) v
        (schwartzCubeOrigin k + schwartzCubeMap m n (u i))‖ ≤ 2^Fintype.card (Fin m ⊕ Fin n) / schwartzCubeWeight d k := by
  classical
  let J := Fin m ⊕ Fin n
  let A := schwartzCubeMap m n
  let p := schwartzCubePolynomial d
  choose U hU he using fun l : List J ↦ elementary_signed_point_bound (F := F) p (l.map (fun j ↦ A (Pi.single j 1)) ++ v)
  let T := {l : List J | l.length ≤ Fintype.card J}
  refine ⟨⋂ l ∈ T, U l, (Filter.biInter_mem (List.finite_length_le J _)).mpr fun l _ ↦ hU l, fun N f hc k b u hu ↦ ?_⟩
  let origin := schwartzCubeOrigin (n := n) k
  let z (j : Fin r) := k (.inr j)
  have hW : 0 < schwartzCubeWeight d k := Finset.prod_pos fun _ _ ↦ by positivity
  rw [div_eq_mul_inv]
  apply sum_norm_of_cube_bounds A origin _ (fun i ↦ (f i).property.1 z b) v _ _ u hu
  intro l hl x hx
  let y := origin + A x
  let coord := Sum.elim (fun i : Fin m ↦ y.1 i) (fun j : Fin r ↦ (z j : ℝ))
  have hcoord (j) : (k j : ℝ) ≤ coord j ∧ coord j ≤ k j + 1 := by
    cases j with
    | inl i =>
      change (k (.inl i) : ℝ) ≤ (k (.inl i) : ℝ) + x (.inl i) ∧ (k (.inl i) : ℝ) + x (.inl i) ≤ k (.inl i) + 1
      constructor <;> linarith [(hx (.inl i)).1,(hx (.inl i)).2]
    | inr j => change (k (.inr j) : ℝ) ≤ k (.inr j) ∧ (k (.inr j) : ℝ) ≤ k (.inr j) + 1; exact ⟨le_rfl, by linarith⟩
  have hC := he l N f (fun c hc' ↦ mem_iInter₂.mp (hc c hc') l hl) y z b
  have hw := schwartzCubeWeight_le d k coord hcoord
  have hz : (fun j ↦ (coord j : ℂ)) = Sum.elim (fun i ↦ (y.1 i : ℂ)) (fun j ↦ (z j : ℂ)) := by
    funext j
    cases j with
    | inl i => rfl
    | inr i => exact Complex.ofReal_intCast _
  rw [hz] at hw
  rw [← mul_one (schwartzCubeWeight d k)⁻¹]
  apply (le_inv_mul_iff₀ hW).mpr
  exact (mul_le_mul_of_nonneg_right hw (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans hC

/-- Each elementary seminorm can be estimated at one lifted point up to a
factor of two. The zero seminorm value permits any point. -/
private theorem elementary_some_weighted_value {m n r : ℕ} {F : Type u}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (i : ElementarySchwartzIndex m n r) (f : ElementarySchwartz m n r F) :
    ∃ x a b, elementarySchwartzSeminorm i f ≤ 2 * ‖((∏ j, (x.1 j : ℂ)^i.1 j) *
      (∏ j, (a j : ℂ)^i.2.2.2 j)) * elementaryPartial f i.2.1 i.2.2.1 x a b‖ := by
  let q := elementarySchwartzSeminorm i f
  by_cases h : q = 0
  · refine ⟨0,0,0,?_⟩
    change q ≤ _
    rw [h]
    positivity
  by_contra! hu
  have hle : elementarySchwartzBound f.val i ≤ ENNReal.ofReal (q/2) := by
    refine iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ (by norm_num : (0:ℝ)<2), mul_comm]
    exact (hu x a b).le
  have hq := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  have hqpos : 0 ≤ q / 2 := div_nonneg (apply_nonneg _ _) (by norm_num)
  rw [ENNReal.toReal_ofReal hqpos] at hq
  change q ≤ q / 2 at hq
  exact h (le_antisymm (by linarith) (apply_nonneg _ _))

/-- Regroup a finite sum by labels and dominate it by a summable majorant. -/
private theorem sum_le_tsum_of_label {N : ℕ} {T : Type*} [DecidableEq T] (label : Fin N → T) (f : Fin N → ℝ)
    (g : T → ℝ) (hg : Summable g) (hpos : ∀ t, 0 ≤ g t)
    (h : ∀ t, ∑ i ∈ Finset.univ.filter (fun i ↦ label i = t), f i ≤ g t) :
    ∑ i, f i ≤ ∑' t, g t := by
  classical
  let S := Finset.univ.image label
  rw [← Finset.sum_fiberwise_of_maps_to (t := S) (fun i hi ↦ Finset.mem_image_of_mem label hi)]
  exact (Finset.sum_le_sum fun t _ ↦ h t).trans (hg.sum_le_tsum S (fun t _ ↦ hpos t))

/-- Each seminorm of an elementary Schwartz space satisfies the absolute
summability estimate on a suitable neighborhood of signed sums. -/
private theorem elementary_seminorm_signed_bound {m n r : ℕ} {F : Type u}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (idx : ElementarySchwartzIndex m n r) :
    ∃ U ∈ 𝓝 (0 : ElementarySchwartz m n r F), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (f : Fin N → ElementarySchwartz m n r F),
        (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
          ∑ i, elementarySchwartzSeminorm idx (f i) ≤ C := by
  classical
  let J := Fin m ⊕ Fin n
  let K := Fin m ⊕ Fin r
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let d : K → ℕ := Sum.elim idx.1 idx.2.2.2
  let v : List X := (List.ofFn fun j ↦ List.replicate (idx.2.1 j) (EuclideanSpace.single j 1,0)).flatten ++
    (List.ofFn fun j ↦ List.replicate (idx.2.2.1 j) (0,EuclideanSpace.single j 1)).flatten
  let dec (k : K → ℤ) := ∏ j, (1 + (k j : ℝ)^2)⁻¹
  have hdec : Summable dec := summable_lattice_product
  have hdec0 (k) : 0 ≤ dec k := Finset.prod_nonneg fun _ _ ↦ by positivity
  let B : ℝ := 2^Fintype.card J
  let g (w : (K → ℤ) × F) := (2*B) * dec w.1
  have hg : Summable g := by
    have hs := hdec.mul_of_nonneg (show Summable (fun _ : F ↦ (1:ℝ)) from .of_finite) hdec0 (fun _ ↦ zero_le_one)
    simpa only [g,mul_one] using hs.mul_left (2*B)
  have hpos (w) : 0 ≤ g w := mul_nonneg (by positivity) (hdec0 w.1)
  obtain ⟨U,hU,hC⟩ := elementary_signed_cube_bound (F := F) d v
  refine ⟨U,hU,∑' w, g w, tsum_nonneg hpos, fun N f hc ↦ ?_⟩
  choose x a b hv using fun i ↦ elementary_some_weighted_value idx (f i)
  let k (i : Fin N) : K → ℤ := Sum.elim (fun j ↦ ⌊(x i).1 j⌋) (a i)
  let u (i : Fin N) : J → ℝ := Sum.elim (fun j ↦ Int.fract ((x i).1 j)) (fun j ↦ Int.fract ((x i).2 j))
  have hu (i j) : u i j ∈ Icc 0 1 := by
    cases j <;> exact ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  let y (i : Fin N) := schwartzCubeOrigin (n := n) (k i) + schwartzCubeMap m n (u i)
  have hyR (i j) : (y i).1 j = (x i).1 j := by
    change (⌊(x i).1 j⌋ : ℝ) + Int.fract ((x i).1 j) = _
    exact Int.floor_add_fract _
  have hycover (i) : elementaryCover (x i) (a i) (b i) = elementaryCover (y i) (a i) (b i) := by
    refine Prod.ext (by ext j; exact (hyR i j).symm) (Prod.ext (funext fun j ↦ ?_) rfl)
    change (((x i).2 j : ℝ) : AddCircle (1:ℝ)) = ((0 + Int.fract ((x i).2 j) : ℝ) : AddCircle (1:ℝ))
    simp
  let D (w : (K → ℤ) × F) (i : Fin N) := ‖listDerivative
    (fun t ↦ f i (elementaryCover t (fun j ↦ w.1 (.inr j)) w.2)) v
    (schwartzCubeOrigin w.1 + schwartzCubeMap m n (u i))‖
  let label (i : Fin N) := (k i,b i)
  have htest (i) : elementarySchwartzSeminorm idx (f i) ≤ 2 * (dec (k i) * schwartzCubeWeight d (k i)) * D (label i) i := by
    have hpartial := (elementaryPartial_descends (f i).val idx.2.1 idx.2.2.1 (a i) (b i)
      ((f i).property.1 (a i) (b i))).2 _ _ (hycover i)
    have hmul : ‖(∏ j, ((x i).1 j : ℂ)^idx.1 j) * (∏ j, (a i j : ℂ)^idx.2.2.2 j)‖ ≤
        dec (k i) * schwartzCubeWeight d (k i) := by
      let z : K → ℝ := Sum.elim (fun j ↦ (x i).1 j) (fun j ↦ (a i j : ℝ))
      have hz (j) : (k i j : ℝ) ≤ z j ∧ z j ≤ k i j + 1 := by
        cases j with
        | inl j => exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
        | inr j => exact ⟨le_rfl, le_add_of_nonneg_right zero_le_one⟩
      have h := schwartzCube_monomial_weight d (k i) z hz
      rw [Fintype.prod_sum_type] at h
      simpa [norm_mul, norm_prod, norm_pow, Complex.norm_real, Complex.norm_intCast, Real.norm_eq_abs, d,z,dec] using h
    have hv' := hv i
    change elementarySchwartzSeminorm idx (f i) ≤ 2 * ‖_ * elementaryPartial (f i).val idx.2.1 idx.2.2.1 (x i) (a i) (b i)‖ at hv'
    rw [norm_mul, hpartial, ← mul_assoc] at hv'
    exact hv'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by norm_num)) (norm_nonneg _))
  refine sum_le_tsum_of_label label _ g hg hpos (fun w ↦ ?_)
  let S := Finset.univ.filter (fun i ↦ label i = w)
  have hW : 0 < schwartzCubeWeight d w.1 := Finset.prod_pos fun _ _ ↦ by positivity
  have hle : ∑ i ∈ S, elementarySchwartzSeminorm idx (f i) ≤ ∑ i ∈ S, (2*(dec w.1 * schwartzCubeWeight d w.1)) * D w i := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have he := (Finset.mem_filter.mp hi).2
    have hk : k i = w.1 := congrArg Prod.fst he
    calc
      _ ≤ 2 * (dec (k i) * schwartzCubeWeight d (k i)) * D (label i) i := htest i
      _ = _ := congrArg₂ (· * ·) (congrArg (fun k ↦ 2 * (dec k * schwartzCubeWeight d k)) hk) (congrArg (fun w ↦ D w i) he)
  rw [← Finset.mul_sum] at hle
  have hnn : 0 ≤ 2 * (dec w.1 * schwartzCubeWeight d w.1) := mul_nonneg (by norm_num) (mul_nonneg (hdec0 _) hW.le)
  have hsub : ∑ i ∈ S, D w i ≤ ∑ i, D w i := Finset.sum_le_univ_sum_of_nonneg fun i ↦ norm_nonneg _
  refine hle.trans ((mul_le_mul_of_nonneg_left hsub hnn).trans ?_)
  have hs : ∑ i, D w i ≤ B / schwartzCubeWeight d w.1 := hC N f hc w.1 w.2 u hu
  refine (mul_le_mul_of_nonneg_left hs hnn).trans_eq ?_
  change _ = 2 * B * dec w.1
  field_simp

/-- It suffices to check the signed-sum criterion on a generating family of
seminorms: the bounds are stable under sums, nonnegative multiples and domination. -/
private theorem nuclear_of_generating_signed_bounds {E : Type u} {I : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [T2Space E] [PolynormableSpace ℂ E] (p : I → Seminorm ℂ E)
    (hp : WithSeminorms p) (h : ∀ i, ∃ U ∈ 𝓝 (0 : E), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (f : Fin N → E), (∀ c : Fin N → ℂ, (∀ i, ‖c i‖ ≤ 1) → ∑ i, c i • f i ∈ U) →
        ∑ j, p i (f j) ≤ C) : NuclearLocallyConvex.{v, u} E := by
  classical
  apply nuclearLocallyConvex_of_signedSum_bound
  intro q hq
  obtain ⟨s, c, _, hqc⟩ := Seminorm.bound_of_continuous hp q hq
  choose U hU C hC hBound using h
  refine ⟨⋂ i ∈ (↑s : Set I), U i, (Filter.biInter_mem s.finite_toSet).mpr fun i _ ↦ hU i,
    (c : ℝ) * ∑ i ∈ s, C i, mul_nonneg c.coe_nonneg (Finset.sum_nonneg fun i _ ↦ hC i),
    fun N f hf ↦ ?_⟩
  calc
    (∑ j, q (f j)) ≤ ∑ j, (c : ℝ) * ∑ i ∈ s, p i (f j) := by
      apply Finset.sum_le_sum
      intro j _
      exact (hqc (f j)).trans (mul_le_mul_of_nonneg_left
        (Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun i _ ↦ apply_nonneg _ _) fun i hi ↦
          Finset.single_le_sum (fun i _ ↦ apply_nonneg _ _) hi) c.coe_nonneg)
    _ = (c : ℝ) * ∑ i ∈ s, ∑ j, p i (f j) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi ↦ hBound i N f fun a ha ↦ mem_iInter₂.mp (hf a ha) i hi)
      c.coe_nonneg

/-- Smoothness controls independent evaluations on each unit cube, and rapid
decay makes the resulting cube bounds summable. -/
theorem elementarySchwartz_nuclear {m n r : ℕ} {F : Type u} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    NuclearLocallyConvex.{v, u} (ElementarySchwartz m n r F) := by
  let : T2Space (ElementarySchwartz m n r F) := elementarySchwartz_t2
  exact nuclear_of_generating_signed_bounds elementarySchwartzSeminorm elementarySchwartz_withSeminorms
    elementary_seminorm_signed_bound

end

end Masullo
