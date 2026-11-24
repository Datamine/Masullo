import EuclideanSchwartzCurrying

open Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {d : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "X₀" => EuclideanSpace ℝ (Fin d)

private abbrev HasSchwartzScalarTests (u : X₀ → 𝓢(Y, ℂ)) : Prop :=
  ∀ l : StrongDual ℂ 𝓢(Y, ℂ), ∃ g : 𝓢(X₀, ℂ), ∀ x, g x = l (u x)

private theorem exists_schwartzUncurry_firstDerivative (u : X₀ → 𝓢(Y, ℂ))
    (hu : HasSchwartzScalarTests u) (v : X₀) :
    ∃ D : X₀ → 𝓢(Y, ℂ), HasSchwartzScalarTests D ∧
      ∀ x (l : StrongDual ℂ 𝓢(Y, ℂ)),
        HasDerivAt (fun t : ℝ => l (u (x + t • v))) (l (D x)) 0 := by
  letI : CompleteSpace 𝓢(Y, ℂ) := completeSpace_schwartzMap
  letI : PolynormableSpace ℂ 𝓢(Y, ℂ) := (schwartz_withSeminorms ℂ Y ℂ).toPolynormableSpace
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hscalar (l : StrongDual ℂ 𝓢(Y, ℂ)) : ContDiff ℝ ∞ (fun x => l (u x)) := by
    obtain ⟨g, hg⟩ := hu l
    exact (funext hg) ▸ g.smooth'
  have h (x : X₀) : ∃ z : 𝓢(Y, ℂ), ∀ l : StrongDual ℂ 𝓢(Y, ℂ),
      HasDerivAt (fun t : ℝ => l (u (x + t • v))) (l z) 0 := by
    have he (l : StrongDual ℂ 𝓢(Y, ℂ)) :
        ContDiffOn ℝ 2 (fun z : Fin d → ℝ => l (u (e.symm z))) univ :=
      (((hscalar l).comp e.symm.contDiff).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
    obtain ⟨z, hz⟩ := weak_coordinate_derivative (𝕜 := ℝ) isOpen_univ
      (u ∘ e.symm) he (e x) (mem_univ _) (e v)
    refine ⟨z, fun l => ?_⟩
    have hline : (fun t : ℝ => l ((u ∘ e.symm) (e x + t • e v))) =
        fun t => l (u (x + t • v)) := by
      funext t
      change l (u (e.symm (e x + t • e v))) = _
      rw [← e.map_smul, ← e.map_add, e.symm_apply_apply]
    exact hline ▸ hz l
  choose D hD using h
  refine ⟨D, ?_, hD⟩
  intro l
  obtain ⟨g, hg⟩ := hu l
  refine ⟨LineDeriv.lineDerivOp v g, fun x => ?_⟩
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hcomp := (g.hasFDerivAt x).comp_hasDerivAt_of_eq 0 hline (by simp)
  have hh : HasDerivAt (fun t : ℝ => g (x + t • v)) (l (D x)) 0 :=
    (hD x l).congr_of_eventuallyEq (.of_forall fun t => hg (x + t • v))
  exact hcomp.deriv.symm.trans hh.deriv

private theorem hasSchwartzScalarTests_lineDeriv (u : X₀ → 𝓢(Y, ℂ))
    (hu : HasSchwartzScalarTests u) (w : Y) :
    HasSchwartzScalarTests (fun x => LineDeriv.lineDerivOp w (u x)) := by
  intro l
  exact hu (l.comp (LineDeriv.lineDerivOpCLM ℂ 𝓢(Y, ℂ) w))

private def schwartzEvaluation (y : Y) : 𝓢(Y, ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ Y ℂ)

private theorem hasDerivAt_schwartzUncurry_second (u : X₀ → 𝓢(Y, ℂ))
    (x : X₀) (y w : Y) :
    HasDerivAt (fun t : ℝ => u x (y + t • w)) (LineDeriv.lineDerivOp w (u x) y) 0 := by
  have hline : HasDerivAt (fun t : ℝ => y + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  exact ((u x).hasFDerivAt y).comp_hasDerivAt_of_eq 0 hline (by simp)


private def euclideanProductEquiv (a b : ℕ) :
    EuclideanSpace ℝ (Fin (a + b)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b) :=
  (EuclideanSpace.equiv (Fin (a + b)) ℝ).trans
    ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (a + b) => ℝ)
        (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm.trans
      ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin a) (Fin b) (fun _ => ℝ)).trans
        ((EuclideanSpace.equiv (Fin a) ℝ).symm.prodCongr (EuclideanSpace.equiv (Fin b) ℝ).symm)))

private theorem euclideanProductEquiv_basis_left (a b : ℕ) (i : Fin a) :
    euclideanProductEquiv a b (EuclideanSpace.basisFun (Fin (a + b)) ℝ (finSumFinEquiv (Sum.inl i))) =
      (EuclideanSpace.basisFun (Fin a) ℝ i, 0) := by
  classical
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
  apply Prod.ext
  · ext j
    change (PiLp.single 2 (finSumFinEquiv (Sum.inl i)) 1 : EuclideanSpace ℝ (Fin (a + b))) (finSumFinEquiv (Sum.inl j)) =
      (PiLp.single 2 i 1 : EuclideanSpace ℝ (Fin a)) j
    simp [PiLp.single_apply]
  · ext j
    change (PiLp.single 2 (finSumFinEquiv (Sum.inl i)) 1 : EuclideanSpace ℝ (Fin (a + b))) (finSumFinEquiv (Sum.inr j)) = 0
    have h : finSumFinEquiv (Sum.inr j) ≠ finSumFinEquiv (Sum.inl i) :=
      fun he => Sum.inr_ne_inl (finSumFinEquiv.injective he)
    simp only [PiLp.single_apply, h, ite_false]

private theorem euclideanProductEquiv_basis_right (a b : ℕ) (i : Fin b) :
    euclideanProductEquiv a b (EuclideanSpace.basisFun (Fin (a + b)) ℝ (finSumFinEquiv (Sum.inr i))) =
      (0, EuclideanSpace.basisFun (Fin b) ℝ i) := by
  classical
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
  apply Prod.ext
  · ext j
    change (PiLp.single 2 (finSumFinEquiv (Sum.inr i)) 1 : EuclideanSpace ℝ (Fin (a + b))) (finSumFinEquiv (Sum.inl j)) = 0
    have h : finSumFinEquiv (Sum.inl j) ≠ finSumFinEquiv (Sum.inr i) :=
      fun he => Sum.inl_ne_inr (finSumFinEquiv.injective he)
    simp only [PiLp.single_apply, h, ite_false]
  · ext j
    change (PiLp.single 2 (finSumFinEquiv (Sum.inr i)) 1 : EuclideanSpace ℝ (Fin (a + b))) (finSumFinEquiv (Sum.inr j)) =
      (PiLp.single 2 i 1 : EuclideanSpace ℝ (Fin b)) j
    simp [PiLp.single_apply]


private theorem exists_schwartz_of_directional_family {a : ℕ}
    (P : (EuclideanSpace ℝ (Fin a) → ℂ) → Prop)
    (hcon : ∀ u, P u → Continuous u)
    (hdecay : ∀ u, P u → ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖u x‖ ≤ C)
    (hdir : ∀ u, P u → ∀ i : Fin a, ∃ v, P v ∧ ∀ x,
      HasDerivAt (fun t : ℝ => u (x + t • EuclideanSpace.basisFun (Fin a) ℝ i)) (v x) 0)
    (u : EuclideanSpace ℝ (Fin a) → ℂ) (hu : P u) :
    ∃ g : 𝓢(EuclideanSpace ℝ (Fin a), ℂ), ∀ x, g x = u x := by
  classical
  let E := EuclideanSpace ℝ (Fin a)
  let e := (EuclideanSpace.equiv (Fin a) ℝ).symm
  let b := EuclideanSpace.basisFun (Fin a) ℝ
  have hb (i : Fin a) : e (Pi.single i 1) = b i := by
    change WithLp.toLp 2 (Pi.single i 1) = _
    rw [EuclideanSpace.basisFun_apply]
    rfl
  have hAll (m : ℕ) (f : E → ℂ) (hf : P f) :
      ContDiff ℝ (m : ℕ∞ω) (f ∘ e) := by
    induction m generalizing f with
    | zero => exact contDiff_zero.mpr ((hcon f hf).comp e.continuous)
    | succ m ih =>
      choose D hPD hD using hdir f hf
      have hF (z : Fin a → ℝ) : HasFDerivAt (f ∘ e)
          (coordinateDifferential (fun i => D i (e z))) z := by
        apply hasFDerivAt_of_continuous_coordinate_derivatives isOpen_univ
          (f ∘ e) (fun i z => D i (e z)) _ _ (mem_univ z)
        · intro i y _
          simpa only [Function.comp_def, e.map_add, e.map_smul, hb] using hD i (e y)
        · exact fun i => (ih (D i) (hPD i)).continuous.continuousOn
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun z => (hF z).differentiableAt, by simp, fun v => ?_⟩
      have H : ContDiff ℝ (m : ℕ∞ω) (fun z => ∑ i, v i • D i (e z)) :=
        ContDiff.sum fun i _ => (ih (D i) (hPD i)).const_smul (v i)
      convert H using 1
      funext z
      rw [(hF z).fderiv, coordinateDifferential_apply]
  have hs (f : E → ℂ) (hf : P f) : ContDiff ℝ ∞ f := by
    have hc := (contDiff_infty.mpr (fun m => hAll m f hf)).comp e.symm.contDiff
    exact (show (f ∘ e) ∘ e.symm = f from funext fun x => by
      change f (e (e.symm x)) = f x
      rw [e.apply_symm_apply]) ▸ hc
  have hd {f g : E → ℂ} (hf : P f) (i : Fin a)
      (hg : ∀ x, HasDerivAt (fun t : ℝ => f (x + t • b i)) (g x) 0)
      (x : E) : fderiv ℝ f x (b i) = g x := by
    have hline : HasDerivAt (fun t : ℝ => x + t • b i) (b i) 0 := by
      let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight (b i)
      have H : HasFDerivAt (fun t : ℝ => x + t • b i) L 0 := L.hasFDerivAt.const_add x
      have h := H.hasDerivAt
      change HasDerivAt _ ((1 : ℝ) • b i) 0 at h
      rwa [one_smul] at h
    have h := (((hs f hf).differentiable (by simp) x).hasFDerivAt).comp_hasDerivAt_of_eq
      0 hline (by simp)
    exact h.deriv.symm.trans (hg x).deriv
  have hWords (n : ℕ) (j : Fin n → Fin a) : P (euclideanCoordinateDerivative n j u) := by
    induction n with
    | zero => exact hu
    | succ n ih =>
      let v := euclideanCoordinateDerivative n (Fin.tail j) u
      obtain ⟨g, hg, hG⟩ := hdir v (ih (Fin.tail j)) (j 0)
      have he : euclideanCoordinateDerivative (n + 1) j u = g :=
        funext (hd (ih (Fin.tail j)) (j 0) hG)
      exact he.symm ▸ hg
  refine ⟨⟨u, hs u hu, fun k n => ?_⟩, fun _ => rfl⟩
  choose B hB using fun j : Fin n → Fin a => hdecay _ (hWords n j) k
  let M := ∑ j, max (B j) 0
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨(a : ℝ) ^ n * M, fun x => ?_⟩
  let T := ‖x‖ ^ k • iteratedFDeriv ℝ n u x
  have hT : ‖T‖ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n u x‖ := by
    dsimp only [T]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [← hT]
  apply (euclideanMultilinear_norm_bounds T).2 M hM
  intro j
  change ‖(‖x‖ ^ k • iteratedFDeriv ℝ n u x) (fun i => b (j i))‖ ≤ M
  rw [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity), ← euclideanCoordinateDerivative_eq (hs u hu)]
  exact (hB j x).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun i _ => le_max_right (B i) 0) (Finset.mem_univ j)))


/-- A Schwartz-valued Schwartz function on a Euclidean space evaluates to
a joint Schwartz function on the product of the Euclidean spaces. -/
theorem exists_schwartzUncurry {a b : ℕ} {I : Type*}
    {p : SeminormFamily ℂ 𝓢(EuclideanSpace ℝ (Fin b), ℂ) I} (hp : WithSeminorms p)
    (u : EuclideanSpace ℝ (Fin a) → 𝓢(EuclideanSpace ℝ (Fin b), ℂ))
    (hu : ∀ i, ∃ f : 𝓢(EuclideanSpace ℝ (Fin a), LocalBanach (p i)),
      ∀ x, f x = localBanachDenseMap (p i) (u x)) :
    ∃ f : 𝓢(EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b), ℂ),
      ∀ x y, f (x, y) = u x y := by
  let A := EuclideanSpace ℝ (Fin a)
  let B := EuclideanSpace ℝ (Fin b)
  let E := EuclideanSpace ℝ (Fin (a + b))
  let e := euclideanProductEquiv a b
  let V (v : A → 𝓢(B, ℂ)) (x : E) := v (e x).1 (e x).2
  let P (g : E → ℂ) := ∃ v : A → 𝓢(B, ℂ), HasSchwartzScalarTests v ∧ g = V v
  have hP (v : A → 𝓢(B, ℂ)) (hv : HasSchwartzScalarTests v) :=
    schwartzUncurry_continuous_and_decay_zero hp v
      ((localBanach_schwartz_iff_scalar hp v).mpr hv)
  have hc (g : E → ℂ) (hg : P g) : Continuous g := by
    obtain ⟨v, hv, rfl⟩ := hg
    exact (hP v hv).1.comp e.continuous
  have hw (g : E → ℂ) (hg : P g) (k : ℕ) :
      ∃ M : ℝ, ∀ x, ‖x‖ ^ k * ‖g x‖ ≤ M := by
    obtain ⟨v, hv, rfl⟩ := hg
    obtain ⟨C₁, h₁⟩ := (hP v hv).2 k 0
    obtain ⟨C₂, h₂⟩ := (hP v hv).2 0 k
    refine ⟨‖e.symm.toContinuousLinearMap‖ ^ k * max C₁ C₂, fun x => ?_⟩
    have hnorm : ‖x‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e x‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
        e.symm.toContinuousLinearMap.le_opNorm (e x)
    have H : ‖e x‖ ^ k * ‖V v x‖ ≤ max C₁ C₂ := by
      rw [Prod.norm_def]
      rcases le_total ‖(e x).1‖ ‖(e x).2‖ with h | h
      · rw [max_eq_right h]
        exact (by simpa only [pow_zero, one_mul] using h₂ (e x).1 (e x).2 :
          ‖(e x).2‖ ^ k * ‖V v x‖ ≤ C₂).trans (le_max_right _ _)
      · rw [max_eq_left h]
        exact (by simpa only [pow_zero, one_mul] using h₁ (e x).1 (e x).2 :
          ‖(e x).1‖ ^ k * ‖V v x‖ ≤ C₁).trans (le_max_left _ _)
    calc
      _ ≤ (‖e.symm.toContinuousLinearMap‖ * ‖e x‖) ^ k * ‖V v x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (norm_nonneg _)
      _ = ‖e.symm.toContinuousLinearMap‖ ^ k * (‖e x‖ ^ k * ‖V v x‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left H (by positivity)
  have hdir (g : E → ℂ) (hg : P g) (i : Fin (a + b)) :
      ∃ g', P g' ∧ ∀ x,
        HasDerivAt (fun t : ℝ => g (x + t • EuclideanSpace.basisFun (Fin (a + b)) ℝ i)) (g' x) 0 := by
    obtain ⟨v, hv, rfl⟩ := hg
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective i
    rcases j with j | j
    · let w := EuclideanSpace.basisFun (Fin a) ℝ j
      obtain ⟨D, hD, hDer⟩ := exists_schwartzUncurry_firstDerivative v hv w
      refine ⟨V D, ⟨D, hD, rfl⟩, fun x => ?_⟩
      have he : e (EuclideanSpace.basisFun (Fin (a + b)) ℝ (finSumFinEquiv (Sum.inl j))) =
          (w, 0) := euclideanProductEquiv_basis_left a b j
      have h := hDer (e x).1 (schwartzEvaluation (e x).2)
      apply h.congr_of_eventuallyEq
      filter_upwards [] with t
      change V v (x + t • EuclideanSpace.basisFun (Fin (a + b)) ℝ (finSumFinEquiv (Sum.inl j))) =
        v ((e x).1 + t • w) (e x).2
      simp only [V, map_add, map_smul, he, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_zero, add_zero]
    · let w := EuclideanSpace.basisFun (Fin b) ℝ j
      let D (z : A) := LineDeriv.lineDerivOp w (v z)
      refine ⟨V D, ⟨D, hasSchwartzScalarTests_lineDeriv v hv w, rfl⟩, fun x => ?_⟩
      have he : e (EuclideanSpace.basisFun (Fin (a + b)) ℝ (finSumFinEquiv (Sum.inr j))) =
          (0, w) := euclideanProductEquiv_basis_right a b j
      have h := hasDerivAt_schwartzUncurry_second v (e x).1 (e x).2 w
      apply h.congr_of_eventuallyEq
      filter_upwards [] with t
      change V v (x + t • EuclideanSpace.basisFun (Fin (a + b)) ℝ (finSumFinEquiv (Sum.inr j))) =
        v (e x).1 ((e x).2 + t • w)
      simp only [V, map_add, map_smul, he, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_zero, add_zero]
  obtain ⟨g, hg⟩ := exists_schwartz_of_directional_family P hc hw hdir (V u)
    ⟨u, (localBanach_schwartz_iff_scalar hp u).mp hu, rfl⟩
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm g, fun x y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change g (e.symm (x, y)) = _
  rw [hg]
  change u (e (e.symm (x, y))).1 (e (e.symm (x, y))).2 = _
  rw [e.apply_symm_apply]


/-- The Euclidean Schwartz currying map is a continuous linear equivalence. -/
theorem exists_schwartzCurryEquiv {a b : ℕ} {I : Type*} [Countable I]
    {p : SeminormFamily ℂ 𝓢(EuclideanSpace ℝ (Fin b), ℂ) I} (hp : WithSeminorms p) :
    ∃ C : ContinuousLinearEquiv (RingHom.id ℂ)
        𝓢(EuclideanSpace ℝ (Fin a) × EuclideanSpace ℝ (Fin b), ℂ)
        (localBanachSchwartz (X := EuclideanSpace ℝ (Fin a)) hp),
      ∀ f x i, (C f).val i x = localBanachDenseMap (p i) (schwartzSlice x f) := by
  let X := EuclideanSpace ℝ (Fin a)
  let Y := EuclideanSpace ℝ (Fin b)
  let A := 𝓢(X × Y, ℂ)
  let B := localBanachSchwartz (X := X) hp
  obtain ⟨C, hInj, hC⟩ := exists_schwartzCurryCLM (d := a) hp
  have hSurj : Surjective C := by
    intro g
    have h (x : X) : ∃ u : 𝓢(Y, ℂ), ∀ i, g.val i x = localBanachDenseMap (p i) u := by
      obtain ⟨u, hu⟩ := g.property x
      exact ⟨u, fun i => (congrFun hu i).symm⟩
    choose u hu using h
    obtain ⟨f, hf⟩ := exists_schwartzUncurry hp u (fun i => ⟨g.val i, fun x => hu x i⟩)
    refine ⟨f, ?_⟩
    apply Subtype.ext
    funext i
    apply SchwartzMap.ext
    intro x
    have he : schwartzSlice x f = u x := SchwartzMap.ext (fun y => hf x y)
    rw [hC, he]
    exact (hu x i).symm
  let L := LinearEquiv.ofBijective C.toLinearMap ⟨hInj, hSurj⟩
  letI : CompleteSpace A := completeSpace_schwartzMap
  letI : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  letI : CompleteSpace 𝓢(Y, ℂ) := completeSpace_schwartzMap
  letI : @CompleteSpace 𝓢(Y, ℂ) (@IsTopologicalAddGroup.rightUniformSpace _ _ _ hp.topologicalAddGroup) := by
    have hEq : @IsTopologicalAddGroup.rightUniformSpace _ _ _ hp.topologicalAddGroup =
        (inferInstance : UniformSpace 𝓢(Y, ℂ)) := IsUniformAddGroup.rightUniformSpace_eq
    rw [hEq]
    infer_instance
  letI : CompleteSpace B := localBanachSchwartz_complete hp inferInstance
  have hB := localBanachSchwartz_frechet (X := X) hp inferInstance
  letI : TopologicalSpace.MetrizableSpace B := hB.2.2.1
  letI : IsUniformAddGroup B := IsUniformInducing.isUniformAddGroup B.subtype
    isUniformEmbedding_subtype_val.isUniformInducing
  letI : (uniformity B).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  letI : BaireSpace B := BaireSpace.of_completelyPseudoMetrizable
  have hOpen : IsOpenMap C := isOpenMap_of_surjective_complete_baire C hSurj
  exact ⟨⟨L, C.continuous, L.toEquiv.continuous_symm_iff.mpr hOpen⟩, hC⟩


end
end Masullo
