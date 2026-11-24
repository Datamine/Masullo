import SchwartzBanachCoordinates
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2

open Bornology Filter Function Set Topology UniformSpace
open scoped ContDiff SchwartzMap

namespace Masullo

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A smooth compact cutoff which is nonzero somewhere on each lattice orbit. -/
structure PeriodicLocalization (L : AddSubgroup X) where
  weight : X → ℂ
  smooth : ContDiff ℝ ∞ weight
  compact : HasCompactSupport weight
  cover : ∀ x, ∃ k : L, weight (x + k.val) ≠ 0

variable {L : AddSubgroup X}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Equations characterizing localized periodic maps without division. -/
def IsLocalizedPeriodic (b : PeriodicLocalization L) (f : X → V) : Prop :=
  ∀ (x : X) (k : L), b.weight (x + k.val) • f x = b.weight x • f (x + k.val)

private theorem isLocalizedPeriodic_of_periodic (b : PeriodicLocalization L)
    (u : X → V) (hu : ∀ x (k : L), u (x + k.val) = u x) :
    IsLocalizedPeriodic b (fun x => b.weight x • u x) := by
  intro x k
  change b.weight (x + k.val) • (b.weight x • u x) = b.weight x • (b.weight (x + k.val) • u (x + k.val))
  rw [hu x k, smul_smul, smul_smul, mul_comm]

/-- A smooth cutoff meeting every orbit recovers a periodic function from
the localization equations. Compactness of the cutoff is only needed for decay estimates. -/
theorem exists_periodic_of_localization_equations (weight : X → ℂ)
    (smooth : ContDiff ℝ ∞ weight) (cover : ∀ x, ∃ k : L, weight (x + k.val) ≠ 0)
    (f : X → V) (hf : ContDiff ℝ ∞ f)
    (h : ∀ (x : X) (k : L), weight (x + k.val) • f x = weight x • f (x + k.val)) :
    ∃ u : X → V, ContDiff ℝ ∞ u ∧ (∀ x (k : L), u (x + k.val) = u x) ∧
        ∀ x, f x = weight x • u x := by
  let r (x : X) := (cover x).choose
  have hr (x : X) : weight (x + (r x).val) ≠ 0 := (cover x).choose_spec
  let u (x : X) := (weight (x + (r x).val))⁻¹ • f (x + (r x).val)
  have hu (x : X) (k : L) (hk : weight (x + k.val) ≠ 0) :
      u x = (weight (x + k.val))⁻¹ • f (x + k.val) := by
    let z := x + (r x).val
    let w := x + k.val
    have hh := h z (k - r x)
    have hw : z + (k - r x : L).val = w := by
      change x + (r x).val + (k.val - (r x).val) = x + k.val
      abel
    rw [hw] at hh
    change (weight z)⁻¹ • f z = (weight w)⁻¹ • f w
    calc
      _ = (weight w)⁻¹ • (weight w • ((weight z)⁻¹ • f z)) :=
        (inv_smul_smul₀ hk _).symm
      _ = (weight w)⁻¹ • ((weight z)⁻¹ • (weight w • f z)) := by
        rw [smul_comm (weight w) (weight z)⁻¹]
      _ = _ := by rw [hh, inv_smul_smul₀ (hr x)]
  have hp (x : X) (k : L) : u (x + k.val) = u x := by
    let l := r x - k
    have he : x + k.val + l.val = x + (r x).val := by
      change x + k.val + ((r x).val - k.val) = _
      abel
    have hn : weight (x + k.val + l.val) ≠ 0 := he.symm ▸ hr x
    simpa only [he, u] using hu (x + k.val) l hn
  have huv (x : X) : f x = weight x • u x := by
    have hh := congrArg ((weight (x + (r x).val))⁻¹ • ·) (h x (r x))
    rw [inv_smul_smul₀ (hr x), smul_comm (weight (x + (r x).val))⁻¹ (weight x)] at hh
    exact hh
  refine ⟨u, ?_, hp, huv⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  let k := r x
  have hb : ContDiffAt ℝ ∞ (fun y : X => weight (y + k.val)) x :=
    smooth.contDiffAt.comp x (contDiff_id.add contDiff_const).contDiffAt
  have hf : ContDiffAt ℝ ∞ (fun y : X => f (y + k.val)) x :=
    hf.contDiffAt.comp x
      (contDiff_id.add contDiff_const).contDiffAt
  apply ((hb.inv (hr x)).smul hf).congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, weight (y + k.val) ≠ 0 :=
    hb.continuousAt.eventually_ne (hr x)
  exact hn.mono fun y hy => hu y k hy

/-- The closed localization equations recover a smooth periodic map from a Schwartz map. -/
theorem isLocalizedPeriodic_iff_exists_periodic (b : PeriodicLocalization L) (f : 𝓢(X, V)) :
    IsLocalizedPeriodic b f ↔
      ∃ u : X → V, ContDiff ℝ ∞ u ∧ (∀ x (k : L), u (x + k.val) = u x) ∧
        ∀ x, f x = b.weight x • u x := by
  refine ⟨fun h => exists_periodic_of_localization_equations b.weight b.smooth b.cover f f.smooth' h, ?_⟩
  rintro ⟨u, -, hp, hu⟩
  rw [funext hu]
  exact isLocalizedPeriodic_of_periodic b u hp

/-- Localizing a smooth periodic map gives a Schwartz map. -/
def periodicLocalization_schwartz (b : PeriodicLocalization L) (u : X → V)
    (hu : ContDiff ℝ ∞ u) : 𝓢(X, V) :=
  (b.compact.smul_right (f' := u)).toSchwartzMap (b.smooth.smul hu)

/-- The period group of the usual Euclidean cover of a torus. -/
def euclideanIntegerLattice (d : ℕ) : AddSubgroup (EuclideanSpace ℝ (Fin d)) where
  carrier := {x | ∀ i, ∃ m : ℤ, (m : ℝ) = x i}
  zero_mem' := fun i => ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i
    obtain ⟨m, hm⟩ := hx i
    obtain ⟨n, hn⟩ := hy i
    exact ⟨m + n, by simp only [Int.cast_add, PiLp.add_apply, hm, hn]⟩
  neg_mem' := by
    intro x hx i
    obtain ⟨m, hm⟩ := hx i
    exact ⟨-m, by simp only [Int.cast_neg, PiLp.neg_apply, hm]⟩

private def euclideanTorusBump (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨(d : ℝ) + 1, (d : ℝ) + 2, by positivity, by linarith⟩

private theorem euclideanTorus_has_representative (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ k : euclideanIntegerLattice d,
      x + k.val ∈ Metric.ball 0 (euclideanTorusBump d).rIn := by
  let U := EuclideanSpace ℝ (Fin d)
  let q : U := WithLp.toLp 2 (fun i => ((-⌊x i⌋ : ℤ) : ℝ))
  let k : euclideanIntegerLattice d := ⟨q, fun i => ⟨-⌊x i⌋, rfl⟩⟩
  refine ⟨k, ?_⟩
  have hcoord (i : Fin d) : ‖(x + q) i‖ ≤ 1 := by
    change ‖x i + ((-⌊x i⌋ : ℤ) : ℝ)‖ ≤ 1
    rw [Int.cast_neg, ← sub_eq_add_neg, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
    linarith [Int.lt_floor_add_one (x i)]
  have hsq : ‖x + q‖ ^ 2 ≤ (d : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ =>
        (pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2).trans_eq (one_pow _)
      _ = _ := by simp
  rw [Metric.mem_ball, dist_zero_right]
  change ‖x + q‖ < (d : ℝ) + 1
  nlinarith [sq_nonneg (d : ℝ), norm_nonneg (x + q)]

/-- A fixed compact ball contains a representative of every torus orbit. -/
theorem euclideanTorus_exists_norm_lt (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ k : euclideanIntegerLattice d, ‖x + k.val‖ < (d : ℝ) + 1 := by
  obtain ⟨k, hk⟩ := euclideanTorus_has_representative d x
  refine ⟨k, ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hk
  exact hk

/-- A compact localization covering every orbit on the Euclidean torus. -/
def euclideanTorusLocalization (d : ℕ) : PeriodicLocalization (euclideanIntegerLattice d) := by
  let v := euclideanTorusBump d
  refine ⟨fun x => Complex.ofReal (v x), Complex.ofRealCLM.contDiff.comp v.contDiff,
    v.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := euclideanTorus_has_representative d x
  refine ⟨k, ?_⟩
  rw [v.one_of_mem_closedBall (Metric.ball_subset_closedBall hk), Complex.ofReal_one]
  exact one_ne_zero

/-- Every torus orbit has a representative near which the cutoff equals one. -/
theorem euclideanTorusLocalization_eventually_one (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ k : euclideanIntegerLattice d, ∀ᶠ y in 𝓝 (x + k.val),
      (euclideanTorusLocalization d).weight y = 1 := by
  obtain ⟨k, hk⟩ := euclideanTorus_has_representative d x
  refine ⟨k, ?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds hk] with y hy
  change Complex.ofReal (euclideanTorusBump d y) = 1
  rw [(euclideanTorusBump d).one_of_mem_closedBall (Metric.ball_subset_closedBall hy),
    Complex.ofReal_one]

/-- If the cutoff equals one near a representative of every orbit,
the zero-weight localized seminorm controls derivatives on the whole cover. -/
theorem norm_iteratedFDeriv_le_of_localizedPeriodic (b : PeriodicLocalization L)
    (u : X → V) (hp : ∀ x (k : L), u (x + k.val) = u x)
    (f : 𝓢(X, V)) (hf : ∀ y, f y = b.weight y • u y)
    (hcover : ∀ x, ∃ k : L, ∀ᶠ y in 𝓝 (x + k.val), b.weight y = 1)
    (n : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ n u x‖ ≤ SchwartzMap.seminorm ℂ 0 n f := by
  obtain ⟨k, hk⟩ := hcover x
  have hper : iteratedFDeriv ℝ n u (x + k.val) = iteratedFDeriv ℝ n u x := by
    rw [← iteratedFDeriv_comp_add_right]
    exact congrFun (congrArg (iteratedFDeriv ℝ n) (funext fun y => hp y k)) x
  have hloc : (f : X → V) =ᶠ[𝓝 (x + k.val)] u := by
    filter_upwards [hk] with y hy
    rw [hf y, hy, one_smul]
  rw [← hper, ← (hloc.iteratedFDeriv ℝ n).eq_of_nhds]
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f n (x + k.val)

/-- The zero-weight localized seminorm controls the uniform derivative on the whole cover. -/
theorem euclideanTorus_norm_iteratedFDeriv_le (d n : ℕ)
    (u : EuclideanSpace ℝ (Fin d) → V) (hu : ContDiff ℝ ∞ u)
    (hp : ∀ x (k : euclideanIntegerLattice d), u (x + k.val) = u x)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ n u x‖ ≤ SchwartzMap.seminorm ℂ 0 n
      (periodicLocalization_schwartz (euclideanTorusLocalization d) u hu) :=
  norm_iteratedFDeriv_le_of_localizedPeriodic (euclideanTorusLocalization d)
    u hp _ (fun _ => rfl) (euclideanTorusLocalization_eventually_one d) n x

/-- Uniform bounds through order `n` control every localized Schwartz seminorm of order `n`. -/
theorem periodicLocalization_seminorm_le (b : PeriodicLocalization L) (k n : ℕ)
    (u : X → V) (hu : ContDiff ℝ ∞ u) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ m ≤ n, ∀ x, ‖iteratedFDeriv ℝ m u x‖ ≤ M) :
    SchwartzMap.seminorm ℂ k n (periodicLocalization_schwartz b u hu) ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k i
        (b.compact.toSchwartzMap b.smooth)) * M := by
  let g := b.compact.toSchwartzMap b.smooth
  apply SchwartzMap.seminorm_le_bound ℂ k n _
  · exact mul_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) hM
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => b.weight y • u y) x‖ ≤ _
  calc
    _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i b.weight x‖ * ‖iteratedFDeriv ℝ (n - i) u x‖ :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_smul_le b.smooth hu x (WithTop.coe_le_coe.mpr le_top))
        (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ i b.weight x‖) * ‖iteratedFDeriv ℝ (n - i) u x‖ := by
      rw [Finset.mul_sum]
      congr 1
      ext i
      ring
    _ ≤ (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k i g) * M := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℂ k i g x) (Nat.cast_nonneg _))
        (hbound (n - i) (Nat.sub_le _ _) x) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))

section ProductTarget

variable {I : Type*} {E : I → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]

/-- The periodic subspace of the coordinatewise Schwartz localization. -/
def localizedPeriodicSubmodule (b : PeriodicLocalization L) (K : Submodule ℂ (∀ i, E i)) :
    Submodule ℂ (schwartzIntoSubmodule (X := X) K) where
  carrier := {f | ∀ i, IsLocalizedPeriodic b (f.val i)}
  zero_mem' := fun i x k => by
    change b.weight (x + k.val) • (0 : E i) = b.weight x • 0
    simp
  add_mem' := by
    intro f g hf hg i x k
    change b.weight (x + k.val) • (f.val i x + g.val i x) =
      b.weight x • (f.val i (x + k.val) + g.val i (x + k.val))
    rw [smul_add, smul_add, hf i x k, hg i x k]
  smul_mem' := by
    intro c f hf i x k
    change b.weight (x + k.val) • (c • f.val i x) = b.weight x • (c • f.val i (x + k.val))
    rw [smul_comm (b.weight (x + k.val)) c, smul_comm (b.weight x) c, hf i x k]

theorem isClosed_localizedPeriodicSubmodule (b : PeriodicLocalization L)
    (K : Submodule ℂ (∀ i, E i)) : IsClosed (localizedPeriodicSubmodule b K :
      Set (schwartzIntoSubmodule (X := X) K)) := by
  let A := schwartzIntoSubmodule (X := X) K
  have he : (localizedPeriodicSubmodule b K : Set A) =
      ⋂ i : I, ⋂ x : X, ⋂ k : L, {f : A |
        b.weight (x + k.val) • f.val i x = b.weight x • f.val i (x + k.val)} := by
    ext f
    simp only [mem_iInter, mem_ofPred_eq]
    rfl
  rw [he]
  refine isClosed_iInter fun i => isClosed_iInter fun x => isClosed_iInter fun k => ?_
  have hev (y : X) : Continuous (fun f : A => f.val i y) := by
    have h₁ : Continuous (fun g : 𝓢(X, E i) => g y) :=
      ((BoundedContinuousFunction.evalCLM ℂ y).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X (E i))).continuous
    have h₂ : Continuous (fun f : A => f.val i) := (continuous_apply i).comp continuous_subtype_val
    exact h₁.comp h₂
  exact isClosed_eq ((hev x).const_smul _) ((hev (x + k.val)).const_smul _)

end ProductTarget

section Completeness

private theorem quasiComplete_of_closedSubmodule
    {W : Type*} [AddCommGroup W] [Module ℂ W] [UniformSpace W] [QuasiCompleteSpace ℂ W]
    (M : Submodule ℂ W) (hM : IsClosed (M : Set W)) : QuasiCompleteSpace ℂ M := by
  constructor
  intro B hB hClosed
  have he : IsUniformInducing (Subtype.val : M → W) :=
    isUniformEmbedding_subtype_val.isUniformInducing
  exact he.isComplete_iff.mp
    (QuasiCompleteSpace.quasiComplete (hB.image M.subtypeL)
      (hM.isClosedEmbedding_subtypeVal.isClosedMap B hClosed))

variable {I Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
  {p : SeminormFamily ℂ Y I}

/-- The derivative topology on vector-valued periodic functions, expressed
by Schwartz localization in the Banach coordinates of the target. -/
abbrev localBanachPeriodic (b : PeriodicLocalization L) (hp : WithSeminorms p) :=
  localizedPeriodicSubmodule b (localBanachDiagonal hp).range

/-- The fixed cutoff defines the family of all weighted coordinate derivative seminorms. -/
theorem localBanachPeriodic_withSeminorms
    (b : PeriodicLocalization L) (hp : WithSeminorms p) :
    ∃ q : SeminormFamily ℂ (localBanachPeriodic b hp) (Σ _ : I, ℕ × ℕ),
      WithSeminorms q ∧ ∀ i k n (f : localBanachPeriodic b hp),
        q ⟨i, (k, n)⟩ f = SchwartzMap.seminorm ℂ k n (f.val.val i) := by
  let M := localizedPeriodicSubmodule b (localBanachDiagonal hp).range
  have hs := schwartzIntoSubmodule_withSeminorms (X := X) (localBanachDiagonal hp).range
  have hq := LinearMap.withSeminorms_induced (E := M) (σ₁₂ := RingHom.id ℂ) hs M.subtype
  exact ⟨_, hq, fun _ _ _ _ => rfl⟩

theorem localBanachPeriodic_quasiComplete [T0Space Y]
    (b : PeriodicLocalization L) (hp : WithSeminorms p)
    (hQ : @QuasiCompleteSpace ℂ Y _ (@IsTopologicalAddGroup.rightUniformSpace Y _ _ hp.topologicalAddGroup)
      _ _) : QuasiCompleteSpace ℂ (localBanachPeriodic b hp) :=
  letI : QuasiCompleteSpace ℂ (localBanachSchwartz (X := X) hp) :=
    localBanachSchwartz_quasiComplete hp hQ
  quasiComplete_of_closedSubmodule _ (isClosed_localizedPeriodicSubmodule b _)

theorem localBanachPeriodic_complete [T0Space Y]
    (b : PeriodicLocalization L) (hp : WithSeminorms p)
    (hc : @CompleteSpace Y (@IsTopologicalAddGroup.rightUniformSpace Y _ _ hp.topologicalAddGroup)) :
    CompleteSpace (localBanachPeriodic b hp) :=
  letI : CompleteSpace (localBanachSchwartz (X := X) hp) := localBanachSchwartz_complete hp hc
  (isClosed_localizedPeriodicSubmodule b (localBanachDiagonal hp).range).isComplete.completeSpace_coe

theorem localBanachPeriodic_frechet [Countable I] [T0Space Y]
    (b : PeriodicLocalization L) (hp : WithSeminorms p)
    (hc : @CompleteSpace Y (@IsTopologicalAddGroup.rightUniformSpace Y _ _ hp.topologicalAddGroup)) :
    IsFrechetTVS (localBanachPeriodic b hp) :=
  isFrechetTVS_closedSubmodule (localBanachSchwartz_frechet (X := X) hp hc) _
    (isClosed_localizedPeriodicSubmodule b _)

private def localizedPeriodicCoordinates (b : PeriodicLocalization L) (hp : WithSeminorms p)
    (u : X → Y) (hper : ∀ x (k : L), u (x + k.val) = u x)
    (hs : ∀ i, ContDiff ℝ ∞ (fun x => localBanachDenseMap (p i) (u x))) :
    localBanachPeriodic b hp := by
  let f (i : I) := periodicLocalization_schwartz b (fun x => localBanachDenseMap (p i) (u x)) (hs i)
  have hm (x : X) : (fun i => f i x) ∈ (localBanachDiagonal hp).range := by
    refine ⟨b.weight x • u x, ?_⟩
    funext i
    exact (localBanachDenseMap (p i)).map_smul _ _
  exact ⟨⟨f, hm⟩, fun i => isLocalizedPeriodic_of_periodic b _ (fun x k => congrArg
    (localBanachDenseMap (p i)) (hper x k))⟩

/-- The localized model consists of actual target-valued periodic functions
which are smooth in each local Banach coordinate. -/
def localBanachPeriodic_equiv [T0Space Y]
    (b : PeriodicLocalization L) (hp : WithSeminorms p) :
    ↥(localBanachPeriodic b hp) ≃
      {u : X → Y // (∀ x (k : L), u (x + k.val) = u x) ∧
        ∀ i, ContDiff ℝ ∞ (fun x => localBanachDenseMap (p i) (u x))} := by
  let D := localBanachDiagonal hp
  let K := D.range
  have hD : Injective D := (localBanachDiagonal_isInducing hp).isEmbedding.injective
  let e := LinearEquiv.ofInjective D.toLinearMap hD
  let A := {u : X → Y // (∀ x (k : L), u (x + k.val) = u x) ∧
    ∀ i, ContDiff ℝ ∞ (fun x => localBanachDenseMap (p i) (u x))}
  let T : A → localBanachPeriodic b hp := fun u =>
    localizedPeriodicCoordinates b hp u.val u.property.1 u.property.2
  have hT (u : A) (i : I) (x : X) : (T u).val.val i x =
      b.weight x • localBanachDenseMap (p i) (u.val x) := rfl
  refine (Equiv.ofBijective T ⟨?_, ?_⟩).symm
  · intro u v huv
    apply Subtype.ext
    funext x
    obtain ⟨k, hk⟩ := b.cover x
    apply hD
    funext i
    have h := congrArg (fun f : localBanachPeriodic b hp => f.val.val i (x + k.val)) huv
    rw [hT, hT, u.property.1 x k, v.property.1 x k] at h
    exact (smul_right_injective _ hk) h
  · intro f
    have hcomp (i : I) := (isLocalizedPeriodic_iff_exists_periodic b (f.val.val i)).mp (f.property i)
    choose g hgs hgp hgf using hcomp
    let r (x : X) := (b.cover x).choose
    let z (x : X) : K := ⟨fun i => f.val.val i x, f.val.property x⟩
    let u (x : X) := (b.weight (x + (r x).val))⁻¹ • e.symm (z (x + (r x).val))
    have he (i : I) (x : X) :
        localBanachDenseMap (p i) (e.symm (z x)) = f.val.val i x :=
      congrArg (fun y : K => y.val i) (e.apply_symm_apply (z x))
    have hu (i : I) (x : X) : localBanachDenseMap (p i) (u x) = g i x := by
      have hr : b.weight (x + (r x).val) ≠ 0 := (b.cover x).choose_spec
      change localBanachDenseMap (p i)
        ((b.weight (x + (r x).val))⁻¹ • e.symm (z (x + (r x).val))) = _
      rw [map_smul, he, hgf i, inv_smul_smul₀ hr, hgp i x (r x)]
    have hup (x : X) (k : L) : u (x + k.val) = u x := by
      apply hD
      funext i
      change localBanachDenseMap (p i) (u (x + k.val)) = localBanachDenseMap (p i) (u x)
      rw [hu, hu, hgp]
    have hus (i : I) : ContDiff ℝ ∞ (fun x => localBanachDenseMap (p i) (u x)) :=
      (funext (hu i)).symm ▸ hgs i
    refine ⟨⟨u, hup, hus⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply SchwartzMap.ext
    intro x
    rw [hT, hu, hgf]

end Completeness


end
end Masullo
