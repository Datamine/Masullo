import PeriodicBanachCoordinates
import SmoothFunctionExhaustion
import EuclideanSchwartzUncurrying
import Mathlib.Analysis.LocallyConvex.HahnBanach

open Filter Function Set Topology
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {I E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

private theorem exists_finite_support_dual [PolynormableSpace ℂ E]
    (l : StrongDual ℂ (I → E)) :
    ∃ s : Finset I, ∃ e : I → StrongDual ℂ E, ∀ f : I → E, l f = ∑ i ∈ s, e i (f i) := by
  classical
  let h := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := h.topologicalAddGroup
  letI : ContinuousSMul ℂ E := h.continuousSMul
  let q : SeminormFamily ℂ E {q : Seminorm ℂ E // Continuous q} := Subtype.val
  let p : SeminormFamily ℂ (I → E) (Σ _ : I, {q : Seminorm ℂ E // Continuous q}) :=
    SeminormFamily.sigma (fun i => q.comp (LinearMap.proj i))
  have hp : WithSeminorms p := withSeminorms_pi (fun _ : I => h)
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hp
    ((normSeminorm ℂ ℂ).comp l.toLinearMap) l.continuous.norm
  let t := s.image Sigma.fst
  let F (i : I) : E →L[ℂ] (I → E) := ContinuousLinearMap.single ℂ (fun _ => E) i
  refine ⟨t, fun i => l.comp (F i), fun f => ?_⟩
  let g := ∑ i ∈ t, F i (f i)
  have hg (j : I) (hj : j ∈ t) : g j = f j := by
    change (∑ i ∈ t, Pi.single i (f i)) j = f j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      exact Pi.single_eq_of_ne hij.symm _
    · exact fun h => (h hj).elim
  have hzero : l (f - g) = 0 := by
    have hq := hC (f - g)
    have hs : s.sup p (f - g) ≤ 0 := by
      apply Seminorm.finset_sup_apply_le le_rfl
      intro j hj
      change j.2.val ((f - g) j.1) ≤ 0
      rw [Pi.sub_apply, hg j.1 (Finset.mem_image_of_mem _ hj), sub_self, map_zero]
    apply norm_eq_zero.mp
    exact le_antisymm ((hq.trans (mul_le_mul_of_nonneg_left hs C.coe_nonneg)).trans_eq (mul_zero _))
      (norm_nonneg _)
  have he : l f = l g := sub_eq_zero.mp (by rwa [← map_sub])
  exact he.trans (map_sum l (fun i => F i (f i)) t)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- To test weak smoothness into a subspace of a product, it suffices
to test each coordinate against the continuous scalar functionals of that coordinate. -/
theorem weaklySmooth_submodule_pi [PolynormableSpace ℂ E]
    (S : Submodule ℂ (I → E)) (f : X → S)
    (h : ∀ i (l : StrongDual ℂ E), ContDiff ℝ ∞ (fun x => l ((f x).val i)))
    (l : StrongDual ℂ S) : ContDiff ℝ ∞ (fun x => l (f x)) := by
  let hE := PolynormableSpace.withSeminorms ℂ E
  letI : IsTopologicalAddGroup E := hE.topologicalAddGroup
  letI : ContinuousSMul ℂ E := hE.continuousSMul
  letI : PolynormableSpace ℂ (I → E) := (withSeminorms_pi (fun _ : I => hE)).toPolynormableSpace
  obtain ⟨l', hl'⟩ := StrongDual.exists_extension S l
  obtain ⟨s, a, ha⟩ := exists_finite_support_dual l'
  have hs : ContDiff ℝ ∞ (fun x => ∑ i ∈ s, a i ((f x).val i)) :=
    ContDiff.sum (fun i _ => h i (a i))
  exact (funext fun x => (ha (f x).val).symm.trans (hl' (f x))) ▸ hs


section Euclidean

variable {a b : ℕ}

local notation "U" => EuclideanSpace ℝ (Fin a)
local notation "V" => EuclideanSpace ℝ (Fin b)
local notation "T" => smoothExhaustionSpace (X := EuclideanSpace ℝ (Fin b))

private theorem smoothCutoff_product_compact (n m : ℕ) :
    HasCompactSupport (fun z : U × V => smoothExhaustionCutoff n z.1 *
      smoothExhaustionCutoff m z.2) := by
  have hU : IsCompact (tsupport (smoothExhaustionCutoff (X := U) n)) :=
    smoothExhaustionCutoff_compact n
  have hV : IsCompact (tsupport (smoothExhaustionCutoff (X := V) m)) :=
    smoothExhaustionCutoff_compact m
  apply (hU.prod hV).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.prod isClosed_closure)
  intro z hz
  have h : smoothExhaustionCutoff n z.1 * smoothExhaustionCutoff m z.2 ≠ 0 := hz
  exact ⟨subset_closure (left_ne_zero_of_mul h), subset_closure (right_ne_zero_of_mul h)⟩

private theorem eventually_smoothExhaustionCutoff_one {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (x : W) :
    ∃ n : ℕ, ∀ᶠ z in 𝓝 x, smoothExhaustionCutoff n z = 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  refine ⟨n, ?_⟩
  have h : x ∈ Metric.ball 0 ((n : ℝ)+1) := Metric.mem_ball.mpr
    (by rw [dist_zero_right]; linarith)
  filter_upwards [Metric.isOpen_ball.mem_nhds h] with z hz
  exact smoothExhaustionCutoff_eq_one n z (by
    have hh := (Metric.mem_ball.mp hz).le
    rwa [dist_zero_right] at hh)

/-- Currying a jointly smooth function gives a weakly smooth function with
values in the compact-open smooth function space of the second variable. -/
theorem weaklySmooth_smoothExhaustion_curry (f : U × V → ℂ) (hf : ContDiff ℝ ∞ f)
    (l : StrongDual ℂ T) :
    ContDiff ℝ ∞ (fun x : U => l (smoothExhaustionPack (fun y => f (x,y))
      (hf.comp (contDiff_const.prodMk contDiff_id)))) := by
  let F (x : U) : T := smoothExhaustionPack (fun y => f (x,y))
    (hf.comp (contDiff_const.prodMk contDiff_id))
  letI : PolynormableSpace ℂ 𝓢(V, ℂ) := (schwartz_withSeminorms ℂ V ℂ).toPolynormableSpace
  change ContDiff ℝ ∞ (fun x => l (F x))
  apply weaklySmooth_submodule_pi _ F
  intro m A
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨n, hn⟩ := eventually_smoothExhaustionCutoff_one x
  let w (z : U × V) := smoothExhaustionCutoff n z.1 * smoothExhaustionCutoff m z.2
  have hw : ContDiff ℝ ∞ w :=
    ((smoothExhaustionCutoff_smooth n).comp contDiff_fst).mul
      ((smoothExhaustionCutoff_smooth m).comp contDiff_snd)
  let g := ((smoothCutoff_product_compact (a := a) (b := b) n m).smul_right (f' := f)).toSchwartzMap
    (hw.smul hf)
  apply (schwartzSlice_contDiff_scalar g A).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hn] with z hz
  have he : (F z).val m = schwartzSlice z g := by
    apply SchwartzMap.ext
    intro y
    change smoothExhaustionCutoff m y • f (z,y) = (smoothExhaustionCutoff n z *
      smoothExhaustionCutoff m y) • f (z,y)
    rw [hz, one_mul]
  rw [he]

/-- Evaluating a weakly smooth map into the compact-open smooth function
space gives a jointly smooth map. Compact localization reduces the proof
to the Schwartz uncurrying isomorphism. -/
theorem contDiff_smoothExhaustion_uncurry (F : U → T)
    (hF : ∀ l : StrongDual ℂ T, ContDiff ℝ ∞ (fun x => l (F x))) :
    ContDiff ℝ ∞ (fun z : U × V => smoothExhaustionEval z.2 (F z.1)) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨x,y⟩
  obtain ⟨n, hn⟩ := eventually_smoothExhaustionCutoff_one x
  obtain ⟨m, hm⟩ := eventually_smoothExhaustionCutoff_one y
  let u (z : U) : 𝓢(V, ℂ) := smoothExhaustionCutoff n z • (F z).val m
  let P : T →L[ℂ] 𝓢(V, ℂ) :=
    (ContinuousLinearMap.proj m).comp (smoothExhaustionSpace (X := V)).subtypeL
  have hs (l : StrongDual ℂ 𝓢(V, ℂ)) : ∃ g : 𝓢(U, ℂ), ∀ z, g z = l (u z) := by
    let v (z : U) := l (P (F z))
    have hv : ContDiff ℝ ∞ v := hF (l.comp P)
    let g := ((smoothExhaustionCutoff_compact (X := U) n).smul_right (f' := v)).toSchwartzMap
      ((smoothExhaustionCutoff_smooth n).smul hv)
    refine ⟨g, fun z => ?_⟩
    change smoothExhaustionCutoff n z • l ((F z).val m) =
      l (smoothExhaustionCutoff n z • (F z).val m)
    exact (l.map_smul _ _).symm
  let h := schwartz_withSeminorms ℂ V ℂ
  obtain ⟨g, hg⟩ := exists_schwartzUncurry h u ((localBanach_schwartz_iff_scalar h u).mpr hs)
  apply g.smooth'.contDiffAt.congr_of_eventuallyEq
  have h₁ : Tendsto (Prod.fst : U × V → U) (𝓝 (x,y)) (𝓝 x) :=
    continuous_fst.continuousAt.tendsto
  have h₂ : Tendsto (Prod.snd : U × V → V) (𝓝 (x,y)) (𝓝 y) :=
    continuous_snd.continuousAt.tendsto
  filter_upwards [h₁.eventually hn, h₂.eventually hm] with z hz hy
  change smoothExhaustionEval z.2 (F z.1) = g z
  rcases z with ⟨a,b⟩
  rw [hg, show u a b = smoothExhaustionCutoff n a • (F a).val m b from rfl,
    smoothExhaustion_localization_eval, hz, hy, one_smul, one_smul]

/-- Ordinary smooth currying, with the usual compact-open derivative topology
on the smooth target and weak scalar tests for its smooth maps. -/
def smoothExhaustion_curryEquiv :
    {f : U × V → ℂ // ContDiff ℝ ∞ f} ≃
      {F : U → T // ∀ l : StrongDual ℂ T, ContDiff ℝ ∞ (fun x => l (F x))} where
  toFun f := ⟨fun x => smoothExhaustionPack (fun y => f.val (x,y))
      (f.property.comp (contDiff_const.prodMk contDiff_id)),
    weaklySmooth_smoothExhaustion_curry f.val f.property⟩
  invFun F := ⟨fun z => smoothExhaustionEval z.2 (F.val z.1),
    contDiff_smoothExhaustion_uncurry F.val F.property⟩
  left_inv f := by
    apply Subtype.ext
    funext z
    exact smoothExhaustionEval_pack (fun y => f.val (z.1,y))
      (f.property.comp (contDiff_const.prodMk contDiff_id)) z.2
  right_inv F := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    funext m
    apply SchwartzMap.ext
    intro y
    exact (smoothExhaustion_localization_eval (F.val x) m y).symm

end Euclidean


section PeriodicTarget

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

theorem smoothExhaustion_ext (f g : smoothExhaustionSpace (X := Y))
    (h : ∀ y, smoothExhaustionEval y f = smoothExhaustionEval y g) : f = g := by
  apply Subtype.ext
  funext n
  apply SchwartzMap.ext
  intro y
  rw [smoothExhaustion_localization_eval, smoothExhaustion_localization_eval, h]

/-- The smooth functions on the cover that are invariant under the period group. -/
def smoothExhaustionPeriodic (L : AddSubgroup Y) :
    Submodule ℂ (smoothExhaustionSpace (X := Y)) where
  carrier := {f | ∀ y (l : L), smoothExhaustionEval (y+l.val) f = smoothExhaustionEval y f}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hf hg y l => by simp only [map_add, hf y l, hg y l]
  smul_mem' := fun c _ hf y l => by rw [map_smul, map_smul, hf y l]

theorem isClosed_smoothExhaustionPeriodic (L : AddSubgroup Y) :
    IsClosed (smoothExhaustionPeriodic L : Set (smoothExhaustionSpace (X := Y))) := by
  have he : (smoothExhaustionPeriodic L : Set (smoothExhaustionSpace (X := Y))) =
      ⋂ y : Y, ⋂ l : L, {f | smoothExhaustionEval (y+l.val) f = smoothExhaustionEval y f} := by
    ext f
    change (∀ y (l : L), smoothExhaustionEval (y+l.val) f = smoothExhaustionEval y f) ↔ _
    simp only [mem_iInter, mem_ofPred_eq]
  rw [he]
  exact isClosed_iInter fun y => isClosed_iInter fun l =>
    isClosed_eq (smoothExhaustionEval (y+l.val)).continuous (smoothExhaustionEval y).continuous

theorem smoothExhaustionPeriodic_frechet (L : AddSubgroup Y) :
    IsFrechetTVS (smoothExhaustionPeriodic L) :=
  isFrechetTVS_closedSubmodule smoothExhaustionSpace_frechet _
    (isClosed_smoothExhaustionPeriodic L)

end PeriodicTarget

section PeriodicCurry

variable {a b : ℕ}

local notation "U" => EuclideanSpace ℝ (Fin a)
local notation "V" => EuclideanSpace ℝ (Fin b)
local notation "T" => smoothExhaustionSpace (X := EuclideanSpace ℝ (Fin b))

/-- Ordinary smooth currying for two periodic covers. A zero subgroup gives
the Euclidean case on that factor. -/
def smoothExhaustionPeriodic_curryEquiv (K : AddSubgroup U) (L : AddSubgroup V) :
    {f : U × V → ℂ // ContDiff ℝ ∞ f ∧
      (∀ x y (k : K), f (x+k.val,y) = f (x,y)) ∧
      (∀ x y (l : L), f (x,y+l.val) = f (x,y))} ≃
    {F : U → smoothExhaustionPeriodic L //
      (∀ x (k : K), F (x+k.val) = F x) ∧
      (∀ l : StrongDual ℂ (smoothExhaustionPeriodic L), ContDiff ℝ ∞ (fun x => l (F x)))} := by
  letI : PolynormableSpace ℂ T := (smoothExhaustionSpace_frechet (X := V)).2.1
  letI : IsTopologicalAddGroup T := (smoothExhaustionSpace_frechet (X := V)).1
  letI : ContinuousSMul ℂ T := (PolynormableSpace.withSeminorms ℂ T).continuousSMul
  let F₀ (f : U × V → ℂ) (hf : ContDiff ℝ ∞ f) (x : U) : T :=
    smoothExhaustionPack (fun y => f (x,y)) (hf.comp (contDiff_const.prodMk contDiff_id))
  let F (f : U × V → ℂ) (hf : ContDiff ℝ ∞ f)
      (h : ∀ x y (l : L), f (x,y+l.val) = f (x,y)) (x : U) :
      smoothExhaustionPeriodic L :=
    ⟨F₀ f hf x, fun y l => by
      change smoothExhaustionEval (y+l.val)
        (smoothExhaustionPack (fun t => f (x,t)) _) =
        smoothExhaustionEval y (smoothExhaustionPack (fun t => f (x,t)) _)
      simp only [smoothExhaustionEval_pack, h]⟩
  refine
    { toFun := fun f => ⟨F f.val f.property.1 f.property.2.2, ?_, ?_⟩
      invFun := fun G => ⟨fun z => smoothExhaustionEval z.2 (G.val z.1).val, ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x k
    apply Subtype.ext
    apply smoothExhaustion_ext
    intro y
    change smoothExhaustionEval y (F₀ f.val f.property.1 (x+k.val)) =
      smoothExhaustionEval y (F₀ f.val f.property.1 x)
    simp only [F₀, smoothExhaustionEval_pack, f.property.2.1]
  · intro l
    obtain ⟨g, hg⟩ := StrongDual.exists_extension (smoothExhaustionPeriodic L) l
    have h := weaklySmooth_smoothExhaustion_curry f.val f.property.1 g
    exact (funext fun x => hg (F f.val f.property.1 f.property.2.2 x)) ▸ h
  · apply contDiff_smoothExhaustion_uncurry (fun x => (G.val x).val)
    intro l
    exact G.property.2 (l.comp (smoothExhaustionPeriodic L).subtypeL)
  · intro x y k
    change smoothExhaustionEval y (G.val (x+k.val)).val = smoothExhaustionEval y (G.val x).val
    rw [G.property.1 x k]
  · intro x y l
    exact (G.val x).property y l
  · intro f
    apply Subtype.ext
    funext z
    change smoothExhaustionEval z.2 (F₀ f.val f.property.1 z.1) = f.val z
    simp only [F₀, smoothExhaustionEval_pack]
  · intro G
    apply Subtype.ext
    funext x
    apply Subtype.ext
    apply smoothExhaustion_ext
    intro y
    change smoothExhaustionEval y
      (smoothExhaustionPack (fun t => smoothExhaustionEval t (G.val x).val)
        (smoothExhaustionEval_contDiff (G.val x).val)) =
      smoothExhaustionEval y (G.val x).val
    exact smoothExhaustionEval_pack _ _ _

end PeriodicCurry


section OrdinaryLinear

variable {a b : ℕ}

local notation "U" => EuclideanSpace ℝ (Fin a)
local notation "V" => EuclideanSpace ℝ (Fin b)

/-- Jointly smooth functions on the covers with the given periods. -/
def jointSmoothPeriodic (K : AddSubgroup U) (L : AddSubgroup V) :
    Submodule ℂ (U × V → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f ∧
      (∀ x y (k : K), f (x+k.val,y) = f (x,y)) ∧
      (∀ x y (l : L), f (x,y+l.val) = f (x,y))}
  zero_mem' := ⟨contDiff_const, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1,
    fun x y k => by simp only [Pi.add_apply, hf.2.1 x y k, hg.2.1 x y k],
    fun x y l => by simp only [Pi.add_apply, hf.2.2 x y l, hg.2.2 x y l]⟩
  smul_mem' := fun c _ hf => ⟨hf.1.const_smul c,
    fun x y k => by simp only [Pi.smul_apply, hf.2.1 x y k],
    fun x y l => by simp only [Pi.smul_apply, hf.2.2 x y l]⟩

/-- Smooth families of periodic smooth functions, using scalar tests for smoothness. -/
def curriedSmoothPeriodic (K : AddSubgroup U) (L : AddSubgroup V) :
    Submodule ℂ (U → smoothExhaustionPeriodic L) where
  carrier := {F | (∀ x (k : K), F (x+k.val) = F x) ∧
      (∀ l : StrongDual ℂ (smoothExhaustionPeriodic L), ContDiff ℝ ∞ (fun x => l (F x)))}
  zero_mem' := ⟨fun _ _ => rfl, fun l => by simpa only [Pi.zero_apply, map_zero] using
    (contDiff_const : ContDiff ℝ ∞ (fun _ : U => (0 : ℂ)))⟩
  add_mem' := fun hf hg => ⟨fun x k => by simp only [Pi.add_apply, hf.1 x k, hg.1 x k],
    fun l => by simpa only [Pi.add_apply, map_add] using (hf.2 l).add (hg.2 l)⟩
  smul_mem' := fun c _ hf => ⟨fun x k => by simp only [Pi.smul_apply, hf.1 x k],
    fun l => by simpa only [Pi.smul_apply, map_smul] using (hf.2 l).const_smul c⟩

/-- Evaluation of the ordinary forward curry is the original joint function. -/
@[simp] theorem smoothExhaustionPeriodic_curryEquiv_eval (K : AddSubgroup U) (L : AddSubgroup V)
    (f : jointSmoothPeriodic K L) (x : U) (y : V) :
    smoothExhaustionEval y (((smoothExhaustionPeriodic_curryEquiv K L) f).val x).val = f.val (x,y) := by
  change smoothExhaustionEval y (smoothExhaustionPack (fun z => f.val (x,z))
    (f.property.1.comp (contDiff_const.prodMk contDiff_id))) = f.val (x,y)
  exact smoothExhaustionEval_pack _ _ _

/-- The bijection of ordinary smooth functions is linear for every choice
of periodic or Euclidean factors. -/
def ordinarySmooth_curryLinearEquiv (K : AddSubgroup U) (L : AddSubgroup V) :
    jointSmoothPeriodic K L ≃ₗ[ℂ] curriedSmoothPeriodic K L where
  toEquiv := smoothExhaustionPeriodic_curryEquiv K L
  map_add' := fun f g => by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    apply smoothExhaustion_ext
    intro y
    change smoothExhaustionEval y (((smoothExhaustionPeriodic_curryEquiv K L) (f+g)).val x).val =
      smoothExhaustionEval y
        ((((smoothExhaustionPeriodic_curryEquiv K L) f).val x).val +
          (((smoothExhaustionPeriodic_curryEquiv K L) g).val x).val)
    rw [map_add, smoothExhaustionPeriodic_curryEquiv_eval,
      smoothExhaustionPeriodic_curryEquiv_eval, smoothExhaustionPeriodic_curryEquiv_eval]
    rfl
  map_smul' := fun c f => by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    apply smoothExhaustion_ext
    intro y
    change smoothExhaustionEval y (((smoothExhaustionPeriodic_curryEquiv K L) (c • f)).val x).val =
      smoothExhaustionEval y (c • (((smoothExhaustionPeriodic_curryEquiv K L) f).val x).val)
    rw [map_smul, smoothExhaustionPeriodic_curryEquiv_eval, smoothExhaustionPeriodic_curryEquiv_eval]
    rfl

end OrdinaryLinear


section OrdinaryCompatibility

variable {a b : ℕ}
local notation "U" => EuclideanSpace ℝ (Fin a)
local notation "V" => EuclideanSpace ℝ (Fin b)

/-- Evaluating the ordinary linear curry recovers the original joint values. -/
theorem ordinarySmooth_curryLinearEquiv_eval (K : AddSubgroup U) (L : AddSubgroup V)
    (f : jointSmoothPeriodic K L) (x : U) (y : V) :
    smoothExhaustionEval y (((ordinarySmooth_curryLinearEquiv K L) f).val x).val =
      f.val (x,y) :=
  smoothExhaustionPeriodic_curryEquiv_eval K L f x y

/-- Localization commutes with currying. A constant weight of one denotes
a Euclidean factor, and a torus uses its compact cutoff on the cover. -/
theorem schwartzSlice_eq_localized_ordinaryCurry (K : AddSubgroup U) (L : AddSubgroup V)
    (f : jointSmoothPeriodic K L) (g : 𝓢(U × V, ℂ)) (α : U → ℂ) (β : V → ℂ)
    (h : ∀ x y, g (x,y) = (α x * β y) • f.val (x,y))
    (x : U) (v : 𝓢(V, ℂ))
    (hv : ∀ y, v y = β y • smoothExhaustionEval y
      (((ordinarySmooth_curryLinearEquiv K L) f).val x).val) :
    schwartzSlice x g = α x • v := by
  apply SchwartzMap.ext
  intro y
  change g (x,y) = α x • v y
  rw [h, hv, ordinarySmooth_curryLinearEquiv_eval, smul_smul]

end OrdinaryCompatibility


/-- On a torus the compact-open derivative topology controls every uniform
derivative through the cutoff on one fixed ball. -/
theorem smoothExhaustionTorus_derivative_le (d n : ℕ)
    (f : smoothExhaustionPeriodic (euclideanIntegerLattice d)) (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ n (fun y => smoothExhaustionEval y f.val) x‖ ≤
      SchwartzMap.seminorm ℂ 0 n (f.val.val d) := by
  let u (y : EuclideanSpace ℝ (Fin d)) := smoothExhaustionEval y f.val
  have hu : ContDiff ℝ ∞ u := smoothExhaustionEval_contDiff f.val
  obtain ⟨j, hj⟩ := euclideanTorus_exists_norm_lt d x
  have hp : iteratedFDeriv ℝ n u (x+j.val) = iteratedFDeriv ℝ n u x := by
    rw [← iteratedFDeriv_comp_add_right]
    exact congrFun (congrArg (iteratedFDeriv ℝ n) (funext fun y => f.property y j)) x
  have he : (smoothExhaustionPack u hu).val d = f.val.val d :=
    SchwartzMap.ext fun y => (smoothExhaustion_localization_eval f.val d y).symm
  change ‖iteratedFDeriv ℝ n u x‖ ≤ _
  rw [← hp, ← he]
  exact smoothExhaustion_derivative_le u hu d n (x+j.val) hj

/-- Uniform derivatives conversely control all the cutoff seminorms of a
smooth periodic function. -/
theorem smoothExhaustionTorus_seminorm_le (d m k n : ℕ)
    (f : smoothExhaustionPeriodic (euclideanIntegerLattice d))
    {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (fun y => smoothExhaustionEval y f.val) x‖ ≤ M) :
    SchwartzMap.seminorm ℂ k n (f.val.val m) ≤
      (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k i
        ((smoothExhaustionCutoff_compact (X := EuclideanSpace ℝ (Fin d)) m).toSchwartzMap
          (smoothExhaustionCutoff_smooth m))) * M := by
  let u (y : EuclideanSpace ℝ (Fin d)) := smoothExhaustionEval y f.val
  have hu : ContDiff ℝ ∞ u := smoothExhaustionEval_contDiff f.val
  have he : (smoothExhaustionPack u hu).val m = f.val.val m :=
    SchwartzMap.ext fun y => (smoothExhaustion_localization_eval f.val m y).symm
  rw [← he]
  exact smoothExhaustion_seminorm_le u hu m k n hM (fun i hi x _ => h i hi x)

end
end Masullo
