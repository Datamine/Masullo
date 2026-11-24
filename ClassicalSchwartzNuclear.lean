import ElementarySchwartzNuclear
import ElementarySchwartzComplete
import SchwartzComplete
import FrechetFactorization
import NuclearFrechetStrongDual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Montel

/-!
# Nuclearity of classical Schwartz spaces

The purely real membership comparison adapts the Apache-2.0 original proofs in
`RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean` and
`RiemannMasullo/ForMathlib/Analysis/InnerProductSpace/PiL2.lean` at
`23cbb63d9a34c2ae8ab0ebd86074ea4c2a056978`.
-/

open Filter Function Set Topology
open scoped ContDiff ENNReal NNReal SchwartzMap

namespace Masullo

noncomputable section

universe u v

/-- The norm of a multilinear map on finite Euclidean spaces is bounded by the sum
of its norms on coordinate basis tuples. -/
private theorem norm_multilinear_le_sum_euclidean_basis {ι κ F : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : ι ↦ EuclideanSpace ℝ κ) F) :
    ‖T‖ ≤ ∑ t : ι → κ, ‖T (fun i ↦ EuclideanSpace.single (t i) 1)‖ := by
  classical
  let e (j : κ) := EuclideanSpace.single j (1 : ℝ)
  apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  have hv (i : ι) : (∑ j, v i j • e j) = v i := by
    simpa [e] using (EuclideanSpace.basisFun κ ℝ).sum_repr (v i)
  have hT : T v = ∑ t : ι → κ, (∏ i, v i (t i)) • T (fun i ↦ e (t i)) := by
    calc
      T v = T.toMultilinearMap (fun i ↦ ∑ j, v i j • e j) := by simp only [hv]; rfl
      _ = _ := by
        rw [T.toMultilinearMap.map_sum (fun i j ↦ v i j • e j)]
        exact Finset.sum_congr rfl fun t _ ↦ T.toMultilinearMap.map_smul_univ _ _
  rw [hT, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
  rw [norm_smul, norm_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ PiLp.norm_apply_le _ _))
    (norm_nonneg _)

/-- Paper: Definition D.1.3.1, p. 750. On the purely real factor the paper's
membership condition agrees with Mathlib's Schwartz class. -/
theorem elementarySchwartzSubmodule_real_iff {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℂ) :
    (fun g : ElementaryLCAModel m 0 0 PUnit.{1} ↦ f g.1) ∈
        elementarySchwartzSubmodule m 0 0 PUnit.{1} ↔
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ, (s : _ → ℂ) = f := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let X := E × EuclideanSpace ℝ (Fin 0)
  let g : ElementaryLCAModel m 0 0 PUnit.{1} → ℂ := fun p ↦ f p.1
  let P : X →L[ℝ] E := ContinuousLinearMap.fst ℝ E _
  let J : E →L[ℝ] X := ContinuousLinearMap.inl ℝ E _
  let coord (j : Fin m) : E := EuclideanSpace.single j 1
  let liftedCoord (j : Fin m) : X := (coord j, 0)
  let directions (β : Fin m → ℕ) := (List.ofFn fun j ↦ List.replicate (β j) (liftedCoord j)).flatten
  let mixedPartial (β : Fin m → ℕ) (x : E) : ℂ :=
    iteratedFDeriv ℝ (directions β).length f x (fun j ↦ ((directions β).get j).1)
  let weight (α : Fin m → ℕ) (x : E) : ℝ := ∏ j, ‖x j‖ ^ α j
  -- The torus and lattice indices are empty, so only the real coordinates contribute.
  have hBound (hf : ContDiff ℝ ∞ f) (i : ElementarySchwartzIndex m 0 0) :
      elementarySchwartzBound g i =
        ⨆ x : E, ENNReal.ofReal (weight i.1 x * ‖mixedPartial i.2.1 x‖) := by
    have hPartial (xt : X) (a : Fin 0 → ℤ) (b : PUnit.{1}) :
        elementaryPartial g i.2.1 i.2.2.1 xt a b = mixedPartial i.2.1 xt.1 := by
      let l : List X := directions i.2.1 ++
        (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0, EuclideanSpace.single j 1)).flatten
      have hl : l = directions i.2.1 := by simp [l]
      change (fun v : List X ↦ iteratedFDeriv ℝ v.length (f ∘ P) xt v.get) l = _
      rw [hl]
      change iteratedFDeriv ℝ (directions i.2.1).length (f ∘ P) xt (directions i.2.1).get = _
      rw [P.iteratedFDeriv_comp_right hf xt (WithTop.coe_le_coe.mpr le_top),
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      rfl
    simp only [elementarySchwartzBound, hPartial, Finset.univ_eq_empty (α := Fin 0),
      Finset.prod_empty, mul_one, ENNReal.coe_nnreal_eq, coe_nnnorm, norm_mul, norm_prod,
      norm_pow, Complex.norm_real, iSup_const]
    exact (show Function.Surjective (Prod.fst : X → E) from fun x ↦ ⟨(x, 0), rfl⟩).iSup_comp
      (fun x ↦ ENNReal.ofReal (weight i.1 x * ‖mixedPartial i.2.1 x‖))
  -- Group any tuple of coordinate directions by its multiplicities.
  have hCoord (hf : ContDiff ℝ ∞ f) {n : ℕ} (t : Fin n → Fin m) (x : E) :
      iteratedFDeriv ℝ n f x (fun j ↦ coord (t j)) = mixedPartial (fun j ↦ (List.ofFn t).count j) x := by
    let β (j : Fin m) := (List.ofFn t).count j
    let l := (List.finRange m).flatMap fun j ↦ List.replicate (β j) j
    have hPerm : (List.ofFn t).Perm l := by
      apply List.perm_iff_count.mpr
      intro j
      rw [List.count_flatMap, ← Fin.sum_univ_def]
      simp [List.count_replicate, β]
    have hDirs : l.map liftedCoord = directions β := by
      simp [l, directions, List.ofFn_eq_map, List.flatMap, Function.comp_def]
    have h := iteratedFDeriv_apply_list_perm hf (Prod.fst : X → E) (hPerm.map liftedCoord) x
    rw [hDirs, List.map_ofFn] at h
    let eval (s : Σ k, Fin k → X) := iteratedFDeriv ℝ s.1 f x (fun j ↦ (s.2 j).1)
    exact (congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨n, liftedCoord ∘ t⟩)).symm.trans h
  change ((∀ (a : Fin 0 → ℤ) (b : PUnit.{1}), ContDiff ℝ ∞ (f ∘ P)) ∧
    ∀ i, elementarySchwartzBound g i < (⊤ : ℝ≥0∞)) ↔ _
  constructor
  · rintro ⟨hs, hb⟩
    have hf : ContDiff ℝ ∞ f := (hs 0 PUnit.unit).comp J.contDiff
    refine ⟨⟨f, hf, ?_⟩, rfl⟩
    intro k n
    let α (i : Option (Fin m)) : Fin m → ℕ := i.elim 0 (fun j ↦ Pi.single j k)
    let β (t : Fin n → Fin m) (j : Fin m) := (List.ofFn t).count j
    let idx (i : Option (Fin m)) (t : Fin n → Fin m) :
        ElementarySchwartzIndex m 0 0 := (α i, β t, 0, 0)
    obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun p : Option (Fin m) × (Fin n → Fin m) ↦
      (elementarySchwartzBound g (idx p.1 p.2)).toReal)
    refine ⟨((m : ℝ) + 1) ^ k * (Fintype.card (Fin n → Fin m) * C), fun x ↦ ?_⟩
    -- Include the constant weight so the maximum exists even when m = 0.
    let c (i : Option (Fin m)) : ℝ := i.elim 1 (fun j ↦ ‖x j‖)
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ c Finset.univ_nonempty
    have hsum : ‖x‖ ≤ ∑ j, ‖x j‖ := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr x]
      refine (norm_sum_le _ _).trans_eq ?_
      simp only [norm_smul, OrthonormalBasis.norm_eq_one, EuclideanSpace.basisFun_repr, mul_one]
    have hsize : ‖x‖ ≤ ((m : ℝ) + 1) * c i := calc
      _ ≤ ∑ _j : Fin m, c i :=
        hsum.trans (Finset.sum_le_sum fun j _ ↦ hi (some j) (Finset.mem_univ _))
      _ ≤ _ := by
        have hnonneg : 0 ≤ c i := zero_le_one.trans (hi none (Finset.mem_univ _))
        simp [add_mul, hnonneg]
    have hw : weight (α i) x = c i ^ k := by
      cases i <;> simp [weight, α, c, Pi.single, Function.update, apply_ite]
    have hpow : ‖x‖ ^ k ≤ ((m : ℝ) + 1) ^ k * weight (α i) x := by
      rw [hw, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hsize k
    let T := iteratedFDeriv ℝ n f x
    have hpoint (t : Fin n → Fin m) : weight (α i) x * ‖T (fun j ↦ coord (t j))‖ ≤ C := by
      rw [show T (fun j ↦ coord (t j)) = mixedPartial (β t) x from hCoord hf t x]
      have hle : ENNReal.ofReal (weight (α i) x * ‖mixedPartial (β t) x‖) ≤
          elementarySchwartzBound g (idx i t) := by
        rw [hBound hf]
        exact le_iSup (fun y ↦ ENNReal.ofReal (weight (α i) y * ‖mixedPartial (β t) y‖)) x
      have h := ENNReal.toReal_mono (hb (idx i t)).ne hle
      rw [ENNReal.toReal_ofReal (by dsimp [weight]; positivity)] at h
      exact h.trans (hC (mem_range_self (i, t)))
    calc
      ‖x‖ ^ k * ‖T‖ ≤ (((m : ℝ) + 1) ^ k * weight (α i) x) *
          ∑ t : Fin n → Fin m, ‖T (fun j ↦ coord (t j))‖ :=
        mul_le_mul hpow (norm_multilinear_le_sum_euclidean_basis T) (norm_nonneg _) (by positivity)
      _ = ((m : ℝ) + 1) ^ k * ∑ t : Fin n → Fin m, weight (α i) x * ‖T (fun j ↦ coord (t j))‖ := by
        rw [mul_assoc, Finset.mul_sum]
      _ ≤ ((m : ℝ) + 1) ^ k * ∑ _t : Fin n → Fin m, C :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ ↦ hpoint t) (by positivity)
      _ = _ := by simp
  · rintro ⟨s, rfl⟩
    refine ⟨fun _ _ ↦ s.smooth'.comp P.contDiff, fun i ↦ ?_⟩
    rw [hBound s.smooth']
    obtain ⟨C, -, hC⟩ := s.decay (∑ j, i.1 j) (directions i.2.1).length
    refine lt_of_le_of_lt (b := ENNReal.ofReal C)
      (iSup_le fun x ↦ ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_lt_top
    have hw : weight i.1 x ≤ ‖x‖ ^ (∑ j, i.1 j) := calc
      _ ≤ ∏ j, ‖x‖ ^ i.1 j :=
        Finset.prod_le_prod (fun _ _ ↦ by positivity) fun j _ ↦
          pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x j) _
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
    have he (j : Fin (directions i.2.1).length) : ‖((directions i.2.1).get j).1‖ = 1 := by
      have hmem := List.get_mem (directions i.2.1) j
      simp only [directions, List.mem_flatten, List.mem_ofFn] at hmem
      obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hmem
      rw [List.eq_of_mem_replicate hq]
      change ‖(EuclideanSpace.single q (1 : ℝ) : E)‖ = 1
      simpa only [EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one q
    have hD : ‖mixedPartial i.2.1 x‖ ≤ ‖iteratedFDeriv ℝ (directions i.2.1).length s x‖ := by
      simpa only [mixedPartial, he, Finset.prod_const_one, mul_one] using
        (iteratedFDeriv ℝ (directions i.2.1).length s x).le_opNorm
          (fun j ↦ ((directions i.2.1).get j).1)
    exact (mul_le_mul hw hD (norm_nonneg _) (by positivity)).trans (hC x)

/-- The purely real elementary Schwartz model uses the classical Schwartz topology. -/
theorem classicalSchwartz_equiv_elementary (m : ℕ) :
    ∃ e : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) ≃L[ℂ] ElementarySchwartz m 0 0 PUnit.{1},
      ∀ f x, e f x = f x.1 := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let S := 𝓢(E, ℂ)
  let T := ElementarySchwartz m 0 0 PUnit.{1}
  let P := ElementaryLCAModel m 0 0 PUnit.{1}
  let A : S →ₗ[ℂ] T :=
    { toFun := fun f ↦ ⟨fun x : P ↦ f x.1,
        (elementarySchwartzSubmodule_real_iff _).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  have hA (f : S) (x : P) : A f x = f x.1 := rfl
  have hSurj : Surjective A := by
    intro s
    have hs (x : P) : s (x.1, 0, 0, 0) = s x :=
      congrArg s (Prod.ext rfl (Subsingleton.elim _ _))
    obtain ⟨f, hf⟩ :=
      (elementarySchwartzSubmodule_real_iff (fun x : E ↦ s (x, 0, 0, 0))).mp
        (show (fun x : P ↦ s (x.1, 0, 0, 0)) ∈ elementarySchwartzSubmodule m 0 0 PUnit.{1} by
          rw [show (fun x : P ↦ s (x.1, 0, 0, 0)) = s.val from funext hs]
          exact s.property)
    exact ⟨f, Subtype.ext (funext fun x ↦ (congrFun hf x.1).trans (hs x))⟩
  let e := LinearEquiv.ofBijective A ⟨fun f g h ↦ SchwartzMap.ext fun x ↦
    congrArg (fun s : T ↦ s (x, 0, 0, 0)) h, hSurj⟩
  obtain ⟨hT, hpoly, hmetric, hcomplete⟩ := elementarySchwartz_isFrechet
    (m := m) (n := 0) (r := 0) (F := PUnit.{1})
  letI : T2Space T := hT
  letI : PolynormableSpace ℂ T := hpoly
  letI : ContinuousSMul ℂ T := (PolynormableSpace.withSeminorms ℂ T).continuousSMul
  letI : TopologicalSpace.MetrizableSpace T := hmetric
  letI : CompleteSpace T := hcomplete
  letI : CompleteSpace S := completeSpace_schwartzMap
  have hClosed : IsClosed (A.graph : Set (S × T)) := by
    have heq : (A.graph : Set (S × T)) = ⋂ x : P, {q : S × T | q.2 x = q.1 x.1} := by
      ext q
      change q.2 = A q.1 ↔ q ∈ ⋂ x : P, {q : S × T | q.2 x = q.1 x.1}
      constructor
      · intro h
        exact mem_iInter.mpr fun x ↦ (congrArg (fun s : T ↦ s x) h).trans (hA q.1 x)
      · intro h
        exact Subtype.ext (funext fun x ↦ (mem_iInter.mp h x).trans (hA q.1 x).symm)
    rw [heq]
    apply isClosed_iInter
    intro x
    obtain ⟨L, hL⟩ := elementaryPartial_evaluation_continuousLinear
      (m := m) (n := 0) (r := 0) (F := PUnit.{1}) 0 0 (x.1, 0) 0 0
    have hEv : Continuous (fun s : T ↦ s x) := L.continuous.congr fun f ↦ by
      rw [hL, elementaryPartial_zero]
      exact congrArg f (Prod.ext rfl (Subsingleton.elim _ _))
    exact isClosed_eq (hEv.comp continuous_snd)
      (((BoundedContinuousFunction.evalCLM ℂ x.1).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ)).continuous.comp continuous_fst)
  have hc : Continuous A := frechet_continuous_of_closed_graph A hClosed
  letI : (uniformity T).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace T := BaireSpace.of_completelyPseudoMetrizable
  letI : @CompleteSpace S (IsTopologicalAddGroup.rightUniformSpace S) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  have ho : IsOpenMap A := isOpenMap_of_surjective_complete_baire
    (⟨A, hc⟩ : S →L[ℂ] T) hSurj
  exact ⟨⟨e, hc, e.toEquiv.continuous_symm_iff.mpr ho⟩, hA⟩

/-- Complex Schwartz functions on a finite-dimensional real normed space
are nuclear for their classical Schwartz topology. -/
theorem classicalSchwartz_nuclear (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : NuclearLocallyConvex.{v, u} 𝓢(V, ℂ) := by
  let m := Module.finrank ℝ V
  let E := EuclideanSpace ℝ (Fin m)
  let L : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E, m])
  let p := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (F := ℂ)
  let q := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (F := ℂ)
  let c := ContinuousLinearEquiv.equivOfInverse p q
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (L.symm_apply_apply x))
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (L.apply_symm_apply x))
  obtain ⟨e, _⟩ := classicalSchwartz_equiv_elementary m
  exact nuclearLocallyConvex_of_equiv (c.trans e).symm elementarySchwartz_nuclear

/-- The classical Schwartz topology is Fréchet. -/
theorem classicalSchwartz_isFrechet (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    IsFrechetTVS 𝓢(V, ℂ) := by
  letI : CompleteSpace 𝓢(V, ℂ) := completeSpace_schwartzMap
  letI : (uniformity 𝓢(V, ℂ)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  refine ⟨inferInstance, (schwartz_withSeminorms ℂ V ℂ).toPolynormableSpace,
    UniformSpace.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- Tempered distributions are nuclear in the topology of bounded convergence. -/
theorem classicalSchwartz_strongDual_nuclear (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : NuclearLocallyConvex.{u, u} (StrongDual ℂ 𝓢(V, ℂ)) :=
  strongDual_nuclear_of_nuclear_frechet (classicalSchwartz_isFrechet V) (classicalSchwartz_nuclear V)

theorem classicalSchwartz_strongDual_complete (V : Type u)
    [NormedAddCommGroup V] [NormedSpace ℝ V] : CompleteSpace (StrongDual ℂ 𝓢(V, ℂ)) := by
  letI : TopologicalSpace.MetrizableSpace 𝓢(V, ℂ) := (classicalSchwartz_isFrechet V).choose_spec.2.1
  infer_instance

theorem classicalSchwartz_strongDual_montel (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : MontelSpace ℂ (StrongDual ℂ 𝓢(V, ℂ)) := by
  letI := classicalSchwartz_strongDual_complete V
  exact ⟨fun _ hs hb ↦
    (nuclearLocallyConvex_totallyBounded (classicalSchwartz_strongDual_nuclear V) hb).isCompact_of_isClosed hs⟩

end

end Masullo
