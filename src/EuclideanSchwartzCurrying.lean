import SchwartzPartialIntegral
import SchwartzScalarTestEquivalence
import EuclideanCoordinateDerivatives
import FrechetFactorization

open Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo
noncomputable section
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
/-- Finite-dimensional scalarizations of a Schwartz-valued slice map are smooth. -/
theorem schwartzSlice_contDiff_scalar {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d) × Y, ℂ))
    (l : 𝓢(Y, ℂ) →L[ℂ] ℂ) :
    ContDiff ℝ ∞ (fun x => l (schwartzSlice x f)) := by
  let X := EuclideanSpace ℝ (Fin d)
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm
  let E (i : Fin d) : X := e (Pi.single i 1)
  let F (g : 𝓢(X × Y, ℂ)) (z : Fin d → ℝ) := l (schwartzSlice (e z) g)
  let D (i : Fin d) (g : 𝓢(X × Y, ℂ)) := LineDeriv.lineDerivOp (E i, (0 : Y)) g
  have hD (i : Fin d) (g : 𝓢(X × Y, ℂ)) (z : Fin d → ℝ) :
      HasDerivAt (fun t : ℝ => F g (z + t • Pi.single i 1)) (F (D i g) z) 0 := by
    simpa only [F, D, E, map_add, map_smul] using schwartzSlice_hasDerivAt_scalar g (e z) (E i) l
  have hAll (m : ℕ) (g : 𝓢(X × Y, ℂ)) : ContDiff ℝ (m : ℕ∞ω) (F g) := by
    induction m generalizing g with
    | zero =>
      exact contDiff_zero.mpr (l.continuous.comp ((continuous_schwartzSlice g).comp e.continuous))
    | succ m ih =>
      have hF (z : Fin d → ℝ) : HasFDerivAt (F g)
          (coordinateDifferential (fun i => F (D i g) z)) z :=
        hasFDerivAt_of_continuous_coordinate_derivatives isOpen_univ (F g) (fun i => F (D i g))
          (fun i z _ => hD i g z) (fun i => (ih (D i g)).continuous.continuousOn) (mem_univ z)
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun z => (hF z).differentiableAt, by simp, fun v => ?_⟩
      have hs : ContDiff ℝ (m : ℕ∞ω) (fun z => ∑ i, v i • F (D i g) z) :=
        ContDiff.sum fun i _ => (ih (D i g)).const_smul (v i)
      convert hs using 1
      funext z
      rw [(hF z).fderiv, coordinateDifferential_apply]
  have hs : ContDiff ℝ ∞ (F f) := contDiff_infty.mpr (fun m => hAll m f)
  have heq : F f ∘ e.symm = (fun x => l (schwartzSlice x f)) := by
    funext x
    change l (schwartzSlice (e (e.symm x)) f) = l (schwartzSlice x f)
    rw [e.apply_symm_apply]
  exact heq ▸ hs.comp e.symm.contDiff

private theorem schwartzSlice_scalar_fderiv {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d) × Y, ℂ))
    (l : 𝓢(Y, ℂ) →L[ℂ] ℂ) (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun z => l (schwartzSlice z f)) x v =
      l (schwartzSlice x (LineDeriv.lineDerivOp (v, (0 : Y)) f)) := by
  let g (z : EuclideanSpace ℝ (Fin d)) := l (schwartzSlice z f)
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hg : HasFDerivAt g (fderiv ℝ g x) x :=
    ((schwartzSlice_contDiff_scalar f l).differentiable (by simp) x).hasFDerivAt
  have hd := hg.comp_hasDerivAt_of_eq 0 hline (by simp)
  exact hd.deriv.symm.trans (schwartzSlice_hasDerivAt_scalar f x v l).deriv

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem exists_schwartzSlice_scalar_weight_bound (f : 𝓢(X × Y, ℂ))
    (l : 𝓢(Y, ℂ) →L[ℂ] ℂ) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖x‖ ^ m * ‖l (schwartzSlice x f)‖ ≤ M := by
  let p := schwartzSeminormFamily ℂ Y ℂ
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ Y ℂ)
    ((normSeminorm ℂ ℂ).comp l.toLinearMap) l.continuous.norm
  let B (a : ℕ × ℕ) := ({(a.1, a.2), (a.1 + m, a.2)} : Finset (ℕ × ℕ)).sup
    (schwartzSeminormFamily ℂ (X × Y) ℂ) f
  let M := ∑ a ∈ s, B a
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => apply_nonneg _ _
  refine ⟨(C : ℝ) * M, mul_nonneg C.coe_nonneg hM, fun x => ?_⟩
  have hv := hC (schwartzSlice x f)
  change ‖l (schwartzSlice x f)‖ ≤ (C : ℝ) * s.sup p (schwartzSlice x f) at hv
  have hw : 0 < max 1 (‖x‖ ^ m) := zero_lt_one.trans_le (le_max_left _ _)
  have hsup : s.sup p (schwartzSlice x f) ≤ M / max 1 (‖x‖ ^ m) := by
    apply Seminorm.finset_sup_apply_le (div_nonneg hM hw.le)
    rintro ⟨k, n⟩ ha
    apply (le_div_iff₀' hw).mpr
    exact (schwartzSlice_weighted_seminorm f k m n x).trans
      (Finset.single_le_sum (f := B) (fun _ _ => apply_nonneg _ _) ha)
  calc
    _ ≤ max 1 (‖x‖ ^ m) * ‖l (schwartzSlice x f)‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    _ ≤ max 1 (‖x‖ ^ m) * ((C : ℝ) * (M / max 1 (‖x‖ ^ m))) :=
      mul_le_mul_of_nonneg_left (hv.trans (mul_le_mul_of_nonneg_left hsup C.coe_nonneg)) hw.le
    _ = _ := by field_simp

private def horizontalSchwartzDerivatives :
    List X → 𝓢(X × Y, ℂ) → 𝓢(X × Y, ℂ)
  | [], f => f
  | v :: s, f => LineDeriv.lineDerivOp (v, (0 : Y)) (horizontalSchwartzDerivatives s f)

private theorem iteratedDirectionalDerivative_schwartzSlice_scalar {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d) × Y, ℂ))
    (l : 𝓢(Y, ℂ) →L[ℂ] ℂ) (v : List (EuclideanSpace ℝ (Fin d))) :
    iteratedDirectionalDerivative v (fun x => l (schwartzSlice x f)) =
      fun x => l (schwartzSlice x (horizontalSchwartzDerivatives v f)) := by
  induction v with
  | nil => rfl
  | cons v s ih =>
    funext x
    simp only [iteratedDirectionalDerivative, horizontalSchwartzDerivatives, ih]
    exact schwartzSlice_scalar_fderiv (horizontalSchwartzDerivatives s f) l x v

/-- Every continuous scalar test of a curried Euclidean Schwartz function is
a scalar Schwartz function in the first variable. -/
theorem exists_schwartz_schwartzSlice_scalar {d : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d) × Y, ℂ))
    (l : 𝓢(Y, ℂ) →L[ℂ] ℂ) :
    ∃ g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ), ∀ x, g x = l (schwartzSlice x f) := by
  let X := EuclideanSpace ℝ (Fin d)
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let u (x : X) := l (schwartzSlice x f)
  have hu : ContDiff ℝ ∞ u := schwartzSlice_contDiff_scalar f l
  refine ⟨⟨u, hu, fun k n => ?_⟩, fun _ => rfl⟩
  classical
  let F (j : Fin n → Fin d) := horizontalSchwartzDerivatives (List.ofFn (fun i => b (j i))) f
  choose B hB hBound using fun j : Fin n → Fin d =>
    exists_schwartzSlice_scalar_weight_bound (F j) l k
  let M := ∑ j, B j
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => hB j
  refine ⟨(d : ℝ) ^ n * M, fun x => ?_⟩
  let T := ‖x‖ ^ k • iteratedFDeriv ℝ n u x
  have hn : ‖T‖ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n u x‖ := by
    dsimp only [T]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [← hn]
  apply (euclideanMultilinear_norm_bounds T).2 M hM
  intro j
  change ‖(‖x‖ ^ k • iteratedFDeriv ℝ n u x) (fun i => b (j i))‖ ≤ M
  rw [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity),
    ← iteratedDirectionalDerivative_ofFn hu, iteratedDirectionalDerivative_schwartzSlice_scalar]
  exact (hBound j x).trans (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ j))

/-- The Euclidean forward curry lies in the local Banach coordinate Schwartz space. -/
theorem schwartzSlice_mem_localBanachSchwartz {d : ℕ}
    {I : Type*} {p : SeminormFamily ℂ 𝓢(Y, ℂ) I} (hp : WithSeminorms p)
    (f : 𝓢(EuclideanSpace ℝ (Fin d) × Y, ℂ)) :
    ∀ i, ∃ g : 𝓢(EuclideanSpace ℝ (Fin d), LocalBanach (p i)),
      ∀ x, g x = localBanachDenseMap (p i) (schwartzSlice x f) :=
  (localBanach_schwartz_iff_scalar hp (fun x => schwartzSlice x f)).mpr
    (exists_schwartz_schwartzSlice_scalar f)

/-- Currying into any one Banach coordinate is a continuous linear map. -/
theorem exists_schwartzCurry_coordinateCLM {d : ℕ} {I : Type*}
    {p : SeminormFamily ℂ 𝓢(Y, ℂ) I} (hp : WithSeminorms p) (i : I) :
    ∃ C : 𝓢(EuclideanSpace ℝ (Fin d) × Y, ℂ) →L[ℂ]
        𝓢(EuclideanSpace ℝ (Fin d), LocalBanach (p i)),
      ∀ f x, C f x = localBanachDenseMap (p i) (schwartzSlice x f) := by
  let X := EuclideanSpace ℝ (Fin d)
  let A := 𝓢(X × Y, ℂ)
  let B := 𝓢(X, LocalBanach (p i))
  let D := localBanachMap (p i) (hp.continuous_seminorm i)
  have h (f : A) : ∃ g : B, ∀ x, g x = D (schwartzSlice x f) :=
    schwartzSlice_mem_localBanachSchwartz hp f i
  choose C hC using h
  let L : A →ₗ[ℂ] B :=
    ⟨⟨C, fun f g => by
      apply SchwartzMap.ext
      intro x
      simp only [hC, add_apply, map_add]⟩, fun a f => by
      apply SchwartzMap.ext
      intro x
      simp only [hC, smul_apply, map_smul, RingHom.id_apply]⟩
  have hgraph : IsClosed (L.graph : Set (A × B)) := by
    have he : (L.graph : Set (A × B)) =
        ⋂ x : X, {fg : A × B | fg.2 x = D (schwartzSlice x fg.1)} := by
      ext fg
      change fg ∈ L.graph ↔ _
      rw [L.mem_graph_iff, mem_iInter]
      constructor
      · intro h x
        change fg.2 x = D (schwartzSlice x fg.1)
        change fg.2 = C fg.1 at h
        rw [h]
        exact hC fg.1 x
      · intro h
        apply SchwartzMap.ext
        intro x
        exact (h x).trans (hC fg.1 x).symm
    rw [he]
    apply isClosed_iInter
    intro x
    have hB : Continuous (fun b : B => b x) :=
      ((BoundedContinuousFunction.evalCLM ℂ x).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X (LocalBanach (p i)))).continuous
    exact isClosed_eq (hB.comp continuous_snd) ((D.comp (schwartzSlice x)).continuous.comp continuous_fst)
  letI : CompleteSpace A := completeSpace_schwartzMap
  letI : CompleteSpace B := completeSpace_schwartzMap
  letI : FirstCountableTopology A := (schwartz_withSeminorms ℂ (X × Y) ℂ).firstCountableTopology
  letI : FirstCountableTopology B :=
    (schwartz_withSeminorms ℂ X (LocalBanach (p i))).firstCountableTopology
  exact ⟨⟨L, frechet_continuous_of_closed_graph L hgraph⟩, hC⟩

/-- Euclidean currying gives a continuous linear injection into the corrected
Schwartz space with values in the second Schwartz space. -/
theorem exists_schwartzCurryCLM {d : ℕ} {I : Type*} {p : SeminormFamily ℂ 𝓢(Y, ℂ) I}
    (hp : WithSeminorms p) :
    ∃ C : 𝓢(EuclideanSpace ℝ (Fin d) × Y, ℂ) →L[ℂ]
        localBanachSchwartz (X := EuclideanSpace ℝ (Fin d)) hp,
      Function.Injective C ∧
      ∀ f x i, (C f).val i x = localBanachDenseMap (p i) (schwartzSlice x f) := by
  let X := EuclideanSpace ℝ (Fin d)
  let A := 𝓢(X × Y, ℂ)
  choose C hC using fun i => exists_schwartzCurry_coordinateCLM (d := d) hp i
  let F : A →L[ℂ] (∀ i, 𝓢(X, LocalBanach (p i))) := ContinuousLinearMap.pi C
  let B := schwartzIntoSubmodule (X := X) (localBanachDiagonal hp).range
  let L : A →L[ℂ] B := F.codRestrict B (fun f x => ⟨schwartzSlice x f, (funext (fun i => hC i f x)).symm⟩)
  refine ⟨L, ?_, fun f x i => hC i f x⟩
  intro f g h
  apply SchwartzMap.ext
  rintro ⟨x, y⟩
  change schwartzSlice x f y = schwartzSlice x g y
  apply congrArg (fun u : 𝓢(Y, ℂ) => u y)
  apply (localBanachDiagonal_isInducing hp).isEmbedding.injective
  funext i
  exact (hC i f x).symm.trans ((congrArg (fun u : B => u.val i x) h).trans (hC i g x))

variable {d : ℕ} {I : Type*}
  {p : SeminormFamily ℂ 𝓢(Y, ℂ) I}

private theorem coords_arbitrary_seminorm (hp : WithSeminorms p)
    (u : EuclideanSpace ℝ (Fin d) → 𝓢(Y, ℂ))
    (hu : ∀ i, ∃ f : 𝓢(EuclideanSpace ℝ (Fin d), LocalBanach (p i)),
      ∀ x, f x = localBanachDenseMap (p i) (u x))
    (q : Seminorm ℂ 𝓢(Y, ℂ)) (hq : Continuous q) :
    ∃ g : 𝓢(EuclideanSpace ℝ (Fin d), LocalBanach q),
      ∀ x, g x = localBanachDenseMap q (u x) := by
  let Q := localBanachMap q hq
  have h (l : StrongDual ℂ (LocalBanach q)) :
      ∃ g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ), ∀ x, g x = l (Q (u x)) :=
    (localBanach_schwartz_iff_scalar hp u).mp hu (l.comp Q)
  have hdiff : ContDiff ℝ ∞ (fun x => Q (u x)) := by
    apply contDiff_euclidean_of_scalar
    intro l
    obtain ⟨g, he⟩ := h l
    exact (funext he) ▸ g.smooth'
  exact exists_schwartz_of_scalar_tests _ hdiff h

/-- The reverse evaluation of a Schwartz-valued map is jointly continuous
and satisfies every product weight of order zero. -/
theorem schwartzUncurry_continuous_and_decay_zero (hp : WithSeminorms p)
    (u : EuclideanSpace ℝ (Fin d) → 𝓢(Y, ℂ))
    (hu : ∀ i, ∃ f : 𝓢(EuclideanSpace ℝ (Fin d), LocalBanach (p i)),
      ∀ x, f x = localBanachDenseMap (p i) (u x)) :
    Continuous (fun z : EuclideanSpace ℝ (Fin d) × Y => u z.1 z.2) ∧
      ∀ k m : ℕ, ∃ C : ℝ, ∀ x y, ‖x‖ ^ k * (‖y‖ ^ m * ‖u x y‖) ≤ C := by
  refine ⟨?_, fun k m => ?_⟩
  · have hcu : Continuous u := by
      apply (localBanachDiagonal_isInducing hp).continuous_iff.mpr
      apply continuous_pi
      intro i
      obtain ⟨f, hf⟩ := hu i
      exact f.continuous.congr hf
    let B := SchwartzMap.toBoundedContinuousFunctionCLM ℂ Y ℂ
    have hEval : Continuous (fun z : (BoundedContinuousFunction Y ℂ) × Y => z.1 z.2) := continuous_eval
    exact hEval.comp (((B.continuous.comp hcu).comp continuous_fst).prodMk continuous_snd)
  · let q := SchwartzMap.seminorm ℂ m 0 (E := Y) (F := ℂ)
    have hq : Continuous q :=
      (schwartz_withSeminorms ℂ Y ℂ).continuous_seminorm (m,0)
    obtain ⟨g, hg⟩ := coords_arbitrary_seminorm hp u hu q hq
    refine ⟨SchwartzMap.seminorm ℂ k 0 g, fun x y => ?_⟩
    have hv : ‖y‖ ^ m * ‖u x y‖ ≤ q (u x) :=
      SchwartzMap.norm_pow_mul_le_seminorm ℂ (u x) m y
    calc
      _ ≤ ‖x‖ ^ k * q (u x) := mul_le_mul_of_nonneg_left hv (by positivity)
      _ = ‖x‖ ^ k * ‖g x‖ := by rw [hg, norm_localBanachDenseMap]
      _ ≤ _ := SchwartzMap.norm_pow_mul_le_seminorm ℂ g k x

end
end Masullo
