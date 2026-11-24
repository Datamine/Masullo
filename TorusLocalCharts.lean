/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
e30083aa6d3b501a52d9c562dc6c336cce761145.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import LocalLinearSubgroup
import PontryaginQuotientLimits
import PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Order.WellQuasiOrder
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Baire.LocallyCompactRegular

open Bornology Filter Set Topology
open scoped Pointwise

namespace Masullo

noncomputable section

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean space admits charts in
some fixed finite real dimension. -/
def IsLocallyEuclidean (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) X)

/-- Coordinatewise circle exponentials are injective on the closed unit ball. -/
private theorem circleExp_coord_injective {ι : Type*} [Fintype ι] {v w : EuclideanSpace ℝ ι}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (h : ∀ i, Circle.exp (v i) = Circle.exp (w i)) : v = w := by
  ext i
  have hvi : |v i| ≤ 1 := (by simpa using PiLp.norm_apply_le v i : |v i| ≤ ‖v‖).trans hv
  have hwi : |w i| ≤ 1 := (by simpa using PiLp.norm_apply_le w i : |w i| ≤ ‖w‖).trans hw
  have h2 : (1 : ℝ) - (-1) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  exact Circle.exp_injOn_Icc h2 (abs_le.mp hvi) (abs_le.mp hwi) (h i)

/-- Near the identity, every point of a finite-dimensional torus has a small coordinatewise
logarithm. -/
private theorem eventually_exists_small_circleLog {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (1 : ι → Circle), ∃ v : EuclideanSpace ℝ ι, ‖v‖ < ε ∧
      ∀ i, Circle.exp (v i) = z i := by
  let lg : (ι → Circle) → EuclideanSpace ℝ ι := fun z ↦
    (EuclideanSpace.equiv ι ℝ).symm (fun i ↦ Complex.arg (z i : ℂ))
  have hlg : ContinuousAt lg 1 := by
    apply (EuclideanSpace.equiv ι ℝ).symm.continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    have h1 : ((1 : ι → Circle) i : ℂ) ∈ Complex.slitPlane := by simp
    show ContinuousAt (fun z : ι → Circle ↦ Complex.arg (z i : ℂ)) 1
    exact (Complex.continuousAt_arg h1).comp (f := fun z : ι → Circle ↦ (z i : ℂ))
      ((continuous_subtype_val.comp (continuous_apply i)).continuousAt)
  have hlg1 : lg 1 = 0 := by
    ext i
    simp [lg]
  have hev := hlg (Metric.ball_mem_nhds (lg 1) hε)
  filter_upwards [hev] with z hz
  refine ⟨lg z, by simpa [hlg1] using hz, fun i ↦ ?_⟩
  simp [lg]

section TorusCharts

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] in
open scoped Pointwise in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel has a
continuous local section over a ball in a linear subspace of the logarithm space. The
section is a local homomorphism, and the images of small balls are identity neighborhoods. -/
theorem exists_localSection_of_discrete_torusKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    ∃ (L : Submodule ℝ (EuclideanSpace ℝ ι)) (ρ : ℝ) (σ : L → G), 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ v : L, ‖v‖ < ρ → ∀ i, f (σ v) i = Circle.exp ((v : EuclideanSpace ℝ ι) i)) ∧
      ContinuousOn σ (Metric.ball 0 ρ) ∧
      (∀ v w : L, ‖v‖ < ρ → ‖w‖ < ρ → ‖v + w‖ < ρ → σ (v + w) = σ v * σ w) ∧
      (∀ ε > 0, σ '' Metric.ball 0 ε ∈ 𝓝 1) := by
  classical
  let ex : EuclideanSpace ℝ ι → (ι → Circle) := fun v i ↦ Circle.exp (v i)
  have hex : Continuous ex := continuous_pi fun i ↦ Circle.exp.continuous.comp (by fun_prop)
  have hex0 : ex 0 = 1 := funext fun i ↦ by simp [ex]
  have hexadd : ∀ v w, ex (v + w) = ex v * ex w := fun v w ↦ funext fun i ↦ by
    simp [ex, Circle.exp_add]
  have hexneg : ∀ v, ex (-v) = (ex v)⁻¹ := fun v ↦ funext fun i ↦ by simp [ex]
  -- A neighborhood meeting the kernel only at the identity.
  obtain ⟨O, hO, h1O, hOker⟩ : ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧
      ∀ x ∈ O, f x = 1 → x = 1 := by
    have hopen1 : IsOpen ({1} : Set f.toMonoidHom.ker) := isOpen_discrete _
    obtain ⟨U0, hU0o, hpre⟩ := isOpen_induced_iff.mp hopen1
    refine ⟨U0, hU0o, ?_, ?_⟩
    · have : (1 : f.toMonoidHom.ker) ∈ Subtype.val ⁻¹' U0 := by rw [hpre]; rfl
      exact this
    · intro x hx hfx
      have hmem : (⟨x, MonoidHom.mem_ker.mpr hfx⟩ : f.toMonoidHom.ker) ∈
          Subtype.val ⁻¹' U0 := hx
      rw [hpre] at hmem
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
  obtain ⟨W, hW, h1W, hWW⟩ := exists_open_nhds_one_mul_subset (hO.mem_nhds h1O)
  have hWW' : W ∩ W⁻¹ ∈ 𝓝 (1 : G) :=
    inter_mem (hW.mem_nhds h1W) (inv_mem_nhds_one G (hW.mem_nhds h1W))
  obtain ⟨V, hV, hVW, hVc⟩ := local_compact_nhds hWW'
  have hinj : ∀ x ∈ V, ∀ y ∈ V, f x = f y → x = y := by
    intro x hx y hy hxy
    have hy' : y⁻¹ ∈ W := (hVW hy).2
    have hm : x * y⁻¹ ∈ O := hWW (Set.mul_mem_mul (hVW hx).1 hy')
    have : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hOker _ hm this)
  obtain ⟨C, hC, -, hCinv, hCC⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  have h1C : (1 : G) ∈ C := mem_of_mem_nhds hC
  have hCV : C ⊆ V := fun x hx ↦ by simpa using hCC (Set.mul_mem_mul hx h1C)
  -- Small logarithms of values on `V` come from `C`.
  have hD : IsCompact (f '' (V \ interior C)) :=
    (hVc.diff isOpen_interior).image f.continuous
  have h1D : (1 : ι → Circle) ∉ f '' (V \ interior C) := by
    rintro ⟨x, ⟨hxV, hxC⟩, hfx⟩
    have : x = 1 := hinj x hxV 1 (mem_of_mem_nhds hV) (by rw [hfx, map_one])
    exact hxC (this ▸ mem_interior_iff_mem_nhds.mpr hC)
  obtain ⟨ε, hε, hεD⟩ : ∃ ε > 0, ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε →
      ex v ∉ f '' (V \ interior C) := by
    have hnhds : (f '' (V \ interior C))ᶜ ∈ 𝓝 (ex 0) := by
      rw [hex0]; exact hD.isClosed.isOpen_compl.mem_nhds h1D
    obtain ⟨ε, hε, H⟩ := Metric.mem_nhds_iff.mp (hex.continuousAt hnhds)
    exact ⟨ε, hε, fun v hv ↦ H (by simpa using hv)⟩
  have hlift : ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε → ∀ x ∈ V, f x = ex v → x ∈ C := by
    intro v hv x hx hfx
    by_contra hxC
    exact hεD v hv ⟨x, ⟨hx, fun h ↦ hxC (interior_subset h)⟩, hfx⟩
  -- The logarithms of the image form a closed local subgroup.
  set R := min (ε / 2) 1 with hRdef
  have hR : 0 < R := lt_min (half_pos hε) one_pos
  have hRε : R < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hR1 : R ≤ 1 := min_le_right _ _
  let A : Set (EuclideanSpace ℝ ι) := {v | ‖v‖ ≤ R ∧ ex v ∈ f '' V}
  have hAc : IsClosed A :=
    (isClosed_le continuous_norm continuous_const).inter
      ((hVc.image f.continuous).isClosed.preimage hex)
  have hA0 : (0 : EuclideanSpace ℝ ι) ∈ A :=
    ⟨by simp [hR.le], ⟨1, mem_of_mem_nhds hV, by rw [map_one, hex0]⟩⟩
  have hAmemC : ∀ v ∈ A, ∃ x ∈ C, f x = ex v := by
    rintro v ⟨hv, x, hx, hfx⟩
    exact ⟨x, hlift v (hv.trans_lt hRε) x hx hfx, hfx⟩
  have hAsym : ∀ v ∈ A, -v ∈ A := by
    intro v hvA
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hvA
    have hxC' : x⁻¹ ∈ C := by rw [← hCinv]; simpa using hxC
    exact ⟨by simpa using hvA.1, x⁻¹, hCV hxC', by rw [map_inv, hfx, hexneg]⟩
  have hAadd : ∀ v ∈ A, ∀ w ∈ A, ‖v + w‖ ≤ R → v + w ∈ A := by
    intro v hv w hw hvw
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hv
    obtain ⟨y, hyC, hfy⟩ := hAmemC w hw
    exact ⟨hvw, x * y, hCC (Set.mul_mem_mul hxC hyC), by rw [map_mul, hfx, hfy, hexadd]⟩
  obtain ⟨L, ε₁, hε₁, hε₁R, hAL⟩ :=
    exists_subspace_ball_eq_of_localSubgroup hR hAc hA0 hAsym hAadd
  have hLA : ∀ v : EuclideanSpace ℝ ι, v ∈ L → ‖v‖ ≤ ε₁ → v ∈ A := by
    intro v hvL hv
    have : v ∈ (L : Set (EuclideanSpace ℝ ι)) ∩ Metric.closedBall 0 ε₁ :=
      ⟨hvL, by simpa using hv⟩
    rw [← hAL] at this
    exact this.1
  have hAL' : ∀ v ∈ A, ‖v‖ ≤ ε₁ → v ∈ L := by
    intro v hvA hv
    have : v ∈ A ∩ Metric.closedBall 0 ε₁ := ⟨hvA, by simpa using hv⟩
    rw [hAL] at this
    exact this.1
  let σ : L → G := fun v ↦ Function.invFunOn f C (ex v)
  have hσ : ∀ v : L, ‖v‖ < ε₁ → σ v ∈ C ∧ f (σ v) = ex v := by
    intro v hv
    exact Function.invFunOn_pos (hAmemC _ (hLA _ v.2 hv.le))
  refine ⟨L, ε₁, σ, hε₁, hε₁R.trans hR1, ?_, ?_, ?_, ?_⟩
  · intro v hv i
    exact congrFun (hσ v hv).2 i
  · rw [continuousOn_iff_continuous_domRestrict]
    let gV : V → (ι → Circle) := fun x ↦ f x
    have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
    have hgV : IsClosedEmbedding gV :=
      (f.continuous.comp continuous_subtype_val).isClosedEmbedding
        (fun x y hxy ↦ Subtype.ext (hinj x x.2 y y.2 hxy))
    let σ' : Metric.ball (0 : L) ε₁ → V := fun v ↦
      ⟨σ v, hCV (hσ v (mem_ball_zero_iff.mp v.2)).1⟩
    have hσ' : Continuous σ' := by
      rw [hgV.isInducing.continuous_iff]
      have e : gV ∘ σ' = fun v : Metric.ball (0 : L) ε₁ ↦ ex ((v : L) : EuclideanSpace ℝ ι) :=
        funext fun v ↦ (hσ v (mem_ball_zero_iff.mp v.2)).2
      rw [e]
      exact hex.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact continuous_subtype_val.comp hσ'
  · intro v w hv hw hvw
    have h1 := hσ v hv
    have h2 := hσ w hw
    have h3 := hσ (v + w) hvw
    refine hinj _ (hCV h3.1) _ (hCC (Set.mul_mem_mul h1.1 h2.1)) ?_
    rw [map_mul, h1.2, h2.2, h3.2, ← hexadd]
    rfl
  · intro ε' hε'
    set ε'' := min ε' ε₁ with hε''def
    have hε'' : 0 < ε'' := lt_min hε' hε₁
    have hnear : ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C ∧
        ∃ u : EuclideanSpace ℝ ι, ‖u‖ < ε'' ∧ ∀ i, Circle.exp (u i) = f x i := by
      refine Filter.Eventually.and (show ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C from
        isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hC)) ?_
      have ht : Tendsto f (𝓝 (1 : G)) (𝓝 1) := by
        have := (map_continuous f).tendsto (1 : G)
        rwa [map_one] at this
      exact ht.eventually (eventually_exists_small_circleLog hε'')
    apply Filter.mem_of_superset hnear
    rintro x ⟨hxC, u, hu, hux⟩
    have hfx : f x = ex u := funext fun i ↦ (hux i).symm
    have hu1 : ‖u‖ < ε₁ := hu.trans_le (min_le_right _ _)
    have huA : u ∈ A := ⟨hu1.le.trans hε₁R, x, hCV (interior_subset hxC), hfx⟩
    have huL : u ∈ L := hAL' u huA hu1.le
    refine ⟨⟨u, huL⟩, by simpa using hu.trans_le (min_le_left _ _), ?_⟩
    have hs := hσ ⟨u, huL⟩ (by simpa using hu1)
    exact hinj _ (hCV hs.1) _ (hCV (interior_subset hxC)) (by rw [hs.2, hfx])

omit [T2Space G] [LocallyCompactSpace G] in
/-- Translating a chart at the identity gives charts everywhere. -/
theorem isLocallyEuclidean_of_chart_at_one {k : ℕ}
    (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin k))) (he : (1 : G) ∈ e.source) :
    IsLocallyEuclidean G := by
  classical
  exact ⟨k, ⟨{
    atlas := Set.range fun g : G ↦
      ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
    chartAt := fun g ↦ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
    mem_chart_source := fun g ↦ by
      change g ∈ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).source ∩
        (Homeomorph.mulLeft g⁻¹) ⁻¹' e.source
      refine ⟨trivial, ?_⟩
      simpa using he
    chart_mem_atlas := fun g ↦ ⟨g, rfl⟩ }⟩⟩

omit [T2Space G] in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel makes
the group locally Euclidean. -/
theorem isLocallyEuclidean_of_torusHom_discreteKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    IsLocallyEuclidean G := by
  classical
  obtain ⟨L, ρ, σ, hρ, hρ1, hfσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel f hf
  have hσ0 : σ 0 = 1 := by
    have e := hσmul 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    rw [add_zero] at e
    exact mul_eq_left.mp e.symm
  let B := Metric.ball (0 : L) ρ
  let τ : B → G := fun v ↦ σ v
  have hτc : Continuous τ := continuousOn_iff_continuous_domRestrict.mp hσc
  have hτinj : Function.Injective τ := by
    intro v w hvw
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    have hw : ‖(w : L)‖ < ρ := mem_ball_zero_iff.mp w.2
    apply Subtype.ext
    apply Subtype.ext
    refine circleExp_coord_injective (hv.le.trans hρ1) (hw.le.trans hρ1) fun i ↦ ?_
    rw [← hfσ v hv i, ← hfσ w hw i]
    exact congrArg (fun x ↦ f x i) hvw
  have hτopen : IsOpenMap τ := by
    intro S hS
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨v, hvS, rfl⟩
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS v hvS
    set δ' := min δ (ρ - ‖(v : L)‖) with hδ'def
    have hδ' : 0 < δ' := lt_min hδ (sub_pos.mpr hv)
    have hδ'1 : δ' ≤ δ := min_le_left _ _
    have hδ'2 : δ' ≤ ρ - ‖(v : L)‖ := min_le_right _ _
    have hnhds : (fun x ↦ σ v * x) '' (σ '' Metric.ball (0 : L) δ') ∈ 𝓝 (σ v) := by
      rw [← map_mul_left_nhds_one (σ v)]
      exact image_mem_map (hσnhds δ' hδ')
    apply Filter.mem_of_superset hnhds
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : ‖w‖ < δ' := mem_ball_zero_iff.mp hw
    have hvw : ‖(v : L) + w‖ < ρ :=
      (norm_add_le _ _).trans_lt (by linarith)
    refine ⟨⟨(v : L) + w, mem_ball_zero_iff.mpr hvw⟩, hδS ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      simpa using hw'.trans_le hδ'1
    · exact (hσmul v w hv (by linarith [norm_nonneg (v : L)]) hvw)
  have hτ : IsOpenEmbedding τ := .of_continuous_injective_isOpenMap hτc hτinj hτopen
  let iso := (stdOrthonormalBasis ℝ L).repr
  let j : B → EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) := fun v ↦ iso v
  have hj : IsOpenEmbedding j :=
    iso.toHomeomorph.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  have : Nonempty B := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let e := (hτ.toOpenPartialHomeomorph τ).symm.trans (hj.toOpenPartialHomeomorph j)
  have he : (1 : G) ∈ e.source := by
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    exact ⟨⟨0, Metric.mem_ball_self hρ⟩, hσ0⟩
  exact isLocallyEuclidean_of_chart_at_one e he

end TorusCharts

section Structure

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] in
/-- Paper: Theorem D.1.4.3(1), p. 757. A locally compact Hausdorff abelian group
with a continuous homomorphism to a finite-dimensional torus and discrete kernel
is locally Euclidean.
Deviation: This isolates the local chart construction. On a sufficiently small
compact identity neighborhood the homomorphism is an embedding. In logarithm
coordinates its image near zero is a relatively closed local additive subgroup
of a finite-dimensional real vector space, hence locally a linear subspace.
Translation gives charts at every point. -/
theorem isLocallyEuclidean_of_discrete_torus_kernel {ι : Type*} [Finite ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    IsLocallyEuclidean G := by
  let : Fintype ι := Fintype.ofFinite ι
  exact isLocallyEuclidean_of_torusHom_discreteKernel f hf


open scoped Pointwise in
/-- A neighborhood containing no nontrivial cyclic subgroup lets finitely many
characters detect the identity locally. -/
private theorem exists_torusHom_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) :
    ∃ (t : Finset (PontryaginDual G)) (f : G →ₜ* (t → Circle)),
      DiscreteTopology f.toMonoidHom.ker := by
  classical
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV, hOne, hVV⟩ := exists_open_nhds_one_mul_subset (inter_mem hKnhds hW)
  have hVW : V ⊆ W := fun x hx ↦ (hVV (mul_one x ▸ Set.mul_mem_mul hx hOne)).2
  let S (χ : PontryaginDual G) : Set G := {x | χ x ≠ 1}
  have hCover : K \ V ⊆ ⋃ χ, S χ := by
    intro x hx
    have hx1 : x ≠ 1 := fun h ↦ hx.2 (h ▸ hOne)
    obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one hx1
    exact mem_iUnion.mpr ⟨χ, hχ⟩
  obtain ⟨t, ht⟩ := (hK.diff hV).elim_finite_subcover S
    (fun χ ↦ (isClosed_eq χ.continuous continuous_const).isOpen_compl) hCover
  let f : G →ₜ* (t → Circle) :=
    { toFun := fun x χ ↦ χ.val x
      map_one' := funext fun χ ↦ map_one χ.val
      map_mul' := fun x y ↦ funext fun χ ↦ map_mul χ.val x y
      continuous_toFun := continuous_pi fun χ ↦ χ.val.continuous }
  refine ⟨t, f, discreteTopology_of_isOpen_singleton_one ?_⟩
  have hKer (x : f.toMonoidHom.ker) (hx : (x : G) ∈ V) : x = 1 := by
    have hr (k : ℕ) : (x : G) ^ k ∈ V := by
      induction k with
      | zero => simpa using hOne
      | succ k ih =>
        have hKmem : (x : G) ^ (k + 1) ∈ K :=
          (hVV (pow_succ (x : G) k ▸ Set.mul_mem_mul ih hx)).1
        by_contra hn
        obtain ⟨χ, hχt, hχ⟩ := mem_iUnion₂.mp (ht ⟨hKmem, hn⟩)
        have hχx : χ (x : G) = 1 :=
          congrFun (MonoidHom.mem_ker.mp x.property) ⟨χ, hχt⟩
        exact hχ (by rw [map_pow, hχx, one_pow])
    exact Subtype.ext (hPow x fun k ↦ hVW (hr k))
  have hPreimage : (Subtype.val : f.toMonoidHom.ker → G) ⁻¹' V = {1} := by
    ext x
    exact ⟨fun hx ↦ mem_singleton_iff.mpr (hKer x hx), by
      rintro (rfl : x = 1)
      exact hOne⟩
  exact hPreimage ▸ hV.preimage continuous_subtype_val

private theorem isLocallyEuclidean_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) : IsLocallyEuclidean G := by
  obtain ⟨_, f, hf⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  exact isLocallyEuclidean_of_discrete_torus_kernel f hf

omit [T2Space G] in
/-- A compact generating neighborhood gives a finite-dimensional local chart on the dual. -/
theorem isLocallyEuclidean_dual_of_compactlyGenerated
    (h : IsCompactlyGeneratedGroup G) : IsLocallyEuclidean (PontryaginDual G) := by
  rcases h with ⟨K, _, hK, hGen⟩
  have hC : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  refine isLocallyEuclidean_of_noSmallCyclicSubgroups
    (pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (K, _)) ⟨hK, hC⟩) ?_
  intro χ hχ
  have hTrivial : K ⊆ (χ : G →ₜ* Circle).toMonoidHom.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro k _
    let φ : G →ₜ* Circle := χ
    change φ x ^ k ∈ Circle.centeredArc (Real.pi / 2)
    rw [← ContinuousMonoidHom.pow_apply]
    exact hχ k hx
  have hTop : ⊤ ≤ (χ : G →ₜ* Circle).toMonoidHom.ker :=
    hGen ▸ (Subgroup.closure_le _).mpr hTrivial
  exact PontryaginDual.ext fun x ↦ MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top x))

open scoped Pointwise in
/-- Circle-valued characters lift to real logarithms on a simply connected chart.
These logarithms rule out nontrivial cyclic subgroups in a smaller neighborhood. -/
theorem exists_nhds_one_of_isLocallyEuclidean (hG : IsLocallyEuclidean G) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
  obtain ⟨n, ⟨charts⟩⟩ := hG
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E (1 : G)
  have he : (1 : G) ∈ e.source := mem_chart_source E 1
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source he))
  -- Pull back a ball to obtain a simply connected identity neighborhood.
  let B := Metric.ball (e 1) r
  let U := e.symm '' B
  have hU : IsOpen U := (e.symm.isOpen_image_iff_of_subset_source hrb).mpr Metric.isOpen_ball
  have h1U : (1 : G) ∈ U :=
    ⟨e 1, Metric.mem_ball_self hr, e.left_inv he⟩
  let b : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hrb rfl
  let : ContractibleSpace B := (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self hr⟩
  let : SimplyConnectedSpace U := b.symm.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace B := Metric.isOpen_ball.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace U := b.symm.isOpenEmbedding.locallyPathConnectedSpace
  let : LocallyConnectedSpace G := ChartedSpace.locallyConnectedSpace E G
  obtain ⟨V₀, hV₀, h1V₀, hprod⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1U)
  obtain ⟨V, ⟨hV, h1V, hVconn⟩, hVsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (1 : G)).mem_iff.mp (hV₀.mem_nhds h1V₀)
  have hVV : V * V ⊆ U := (Set.mul_subset_mul hVsub hVsub).trans hprod
  have hVU : V ⊆ U := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx h1V)
  obtain ⟨K, hK, hKV, hKc⟩ := local_compact_nhds (hV.mem_nhds h1V)
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  by_contra hx1
  obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one hx1
  let χU : C(U, Circle) := ⟨fun u ↦ χ u, χ.continuous.comp continuous_subtype_val⟩
  let oneU : U := ⟨1, h1U⟩
  let oneV : V := ⟨1, h1V⟩
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    χU oneU 0 (Circle.exp_zero.trans (map_one χ).symm)
  have hl (u : U) : Circle.exp (L u) = χ u := congrFun hL u
  let incl (v : V) : U := ⟨v, hVU v.property⟩
  let mul (p : V × V) : U := ⟨p.1 * p.2, hVV (Set.mul_mem_mul p.1.property p.2.property)⟩
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  -- Uniqueness of lifts makes the logarithm additive on pairs from the smaller neighborhood.
  have hAdd (a b : V) : L (mul (a, b)) = L (incl a) + L (incl b) := by
    have hMul : Continuous mul :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _
    have hIncl : Continuous incl := continuous_subtype_val.subtype_mk _
    have hAgree : Circle.exp ∘ (fun p : V × V ↦ L (mul p)) =
        Circle.exp ∘ (fun p : V × V ↦ L (incl p.1) + L (incl p.2)) := by
      funext p
      simp [Circle.exp_add, hl, mul, incl, map_mul]
    have hStart : L (mul (oneV, oneV)) = L (incl oneV) + L (incl oneV) := by
      have hmul : mul (oneV, oneV) = oneU := Subtype.ext (one_mul 1)
      have hincl : incl oneV = oneU := rfl
      simp [hmul, hincl, hL0]
    exact congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq (L.continuous.comp hMul)
      ((L.continuous.comp (hIncl.comp continuous_fst)).add
        (L.continuous.comp (hIncl.comp continuous_snd))) hAgree (oneV, oneV) hStart) (a, b)
  -- A nonzero logarithm would grow without bound along the powers inside the compact set.
  let z (k : ℕ) : V := ⟨x ^ k, hKV (hx k)⟩
  have hPow (k : ℕ) : L (incl (z k)) = k * L (incl (z 1)) := by
    induction k with
    | zero =>
      have hz : incl (z 0) = oneU := Subtype.ext (pow_zero x)
      simpa [hz] using hL0
    | succ k ih =>
      have hz : incl (z (k + 1)) = mul (z k, z 1) := Subtype.ext (by simp [incl, mul, z, pow_succ])
      rw [hz, hAdd, ih, Nat.cast_succ, add_mul, one_mul]
  have hKb : IsCompact (Subtype.val ⁻¹' K : Set U) := by
    exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKc
      (Subtype.range_coe.symm ▸ hKV.trans hVU)
  obtain ⟨M, hM⟩ := (hKb.image L.continuous).isBounded.exists_norm_le
  have hZero : L (incl (z 1)) = 0 := by
    by_contra hNe
    obtain ⟨k, hk⟩ := exists_nat_gt (M / ‖L (incl (z 1))‖)
    have hLe := hM _ (mem_image_of_mem L (show incl (z k) ∈ Subtype.val ⁻¹' K from hx k))
    rw [hPow, norm_mul, Real.norm_natCast] at hLe
    exact (not_lt_of_ge hLe) ((div_lt_iff₀ (norm_pos_iff.mpr hNe)).mp hk)
  have hValue := hl (incl (z 1))
  rw [hZero, Circle.exp_zero] at hValue
  exact hχ (by simpa [incl, z] using hValue.symm)

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- A multiplicative local homomorphism on a real normed ball extends by repeated halving.
The value computed at any sufficiently small scale agrees with the extension. -/
private theorem exists_dyadicExtension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : ℝ} (hρ : 0 < ρ) (σ : E → G)
    (hσ : ∀ v w, ‖v‖ < ρ → ‖w‖ < ρ → ‖v + w‖ < ρ → σ (v + w) = σ v * σ w) :
    ∃ f : Multiplicative E →* G, ∀ v, ‖v‖ < ρ → f (Multiplicative.ofAdd v) = σ v := by
  classical
  let shrink (x : E) (n : ℕ) := ((1 / 2 : ℝ) ^ n) • x
  have hsmall (x : E) : ∃ n, ‖shrink x n‖ < ρ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos hρ (by positivity : 0 < ‖x‖ + 1)) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    rw [show ‖shrink x n‖ = (1 / 2 : ℝ) ^ n * ‖x‖ by
      simp [shrink, norm_smul]]
    have h := (lt_div_iff₀ (by positivity : 0 < ‖x‖ + 1)).mp hn
    nlinarith [show 0 ≤ (1 / 2 : ℝ) ^ n by positivity]
  have hhalf (x : E) (n : ℕ) : shrink x (n + 1) = (1 / 2 : ℝ) • shrink x n := by
    simp [shrink, pow_succ, smul_smul, mul_comm]
  let value (x : E) (n : ℕ) := σ (shrink x n) ^ (2 ^ n : ℕ)
  have hstep (x : E) (n : ℕ) (hn : ‖shrink x n‖ < ρ) :
      ‖shrink x (n + 1)‖ < ρ ∧ value x (n + 1) = value x n := by
    have hs : ‖shrink x (n + 1)‖ < ρ := by
      rw [hhalf, norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
      linarith [norm_nonneg (shrink x n)]
    have hdouble : shrink x (n + 1) + shrink x (n + 1) = shrink x n := by
      rw [hhalf, ← add_smul]
      norm_num
    have hh := hσ (shrink x (n + 1)) (shrink x (n + 1)) hs hs (hdouble ▸ hn)
    rw [hdouble, ← pow_two] at hh
    exact ⟨hs, by simp only [value, pow_succ', pow_mul, ← hh]⟩
  have hstable (x : E) {n m : ℕ} (h : n ≤ m) (hn : ‖shrink x n‖ < ρ) :
      ‖shrink x m‖ < ρ ∧ value x m = value x n := by
    induction m, h using Nat.le_induction with
    | base => exact ⟨hn, rfl⟩
    | succ m _ ih =>
      obtain ⟨hs, hv⟩ := hstep x m ih.1
      exact ⟨hs, hv.trans ih.2⟩
  let F (x : E) := value x (hsmall x).choose
  have hF (x : E) (n : ℕ) (hn : ‖shrink x n‖ < ρ) : F x = value x n := by
    let m := max (hsmall x).choose n
    exact ((hstable x (m := m) (le_max_left _ _) (hsmall x).choose_spec).2).symm.trans
      (hstable x (m := m) (le_max_right _ _) hn).2
  have h0 : σ 0 = 1 := by
    have h := hσ 0 0 (by simpa) (by simpa) (by simpa)
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  refine ⟨{ toFun := fun x => F x.toAdd, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · change F 0 = 1
    rw [hF 0 0 (by simpa [shrink] using hρ)]
    simp [value, shrink, h0]
  · intro x y
    let u := x.toAdd
    let v := y.toAdd
    let n := max (hsmall (u + v)).choose (max (hsmall u).choose (hsmall v).choose)
    have hu := (hstable u (m := n) (le_trans (le_max_left _ _) (le_max_right _ _))
      (hsmall u).choose_spec).1
    have hv := (hstable v (m := n) (le_trans (le_max_right _ _) (le_max_right _ _))
      (hsmall v).choose_spec).1
    have huv := (hstable (u + v) (m := n) (le_max_left _ _) (hsmall (u + v)).choose_spec).1
    change F (u + v) = F u * F v
    rw [hF _ n huv, hF _ n hu, hF _ n hv]
    have hsum : shrink (u + v) n = shrink u n + shrink v n := smul_add _ _ _
    simp only [value, hsum]
    rw [hσ _ _ hu hv (hsum ▸ huv), mul_pow]
  · intro v hv
    change F v = σ v
    rw [hF v 0 (by simpa [shrink] using hv)]
    simp [value, shrink]

set_option maxHeartbeats 1000000 in
/-- A locally Euclidean LCA group has a continuous open vector-group homomorphism
with discrete kernel. -/
theorem exists_euclidean_openHom (hG : IsLocallyEuclidean G) :
    ∃ (d : ℕ) (f : Multiplicative (EuclideanSpace ℝ (Fin d)) →* G),
      Continuous f ∧ IsOpenMap f ∧ DiscreteTopology f.ker := by
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean hG
  obtain ⟨t, c, hc⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  obtain ⟨L, ρ, σ, hρ, hρ1, hσc, hσcont, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel c hc
  obtain ⟨F, hF⟩ := exists_dyadicExtension hρ σ hσmul
  let e := (stdOrthonormalBasis ℝ L).repr
  let f := F.comp e.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom.toMultiplicative
  have hcont : Continuous F := by
    apply continuous_of_continuousAt_one F
    have hσ0 : ContinuousAt σ (0 : L) :=
      hσcont.continuousAt (Metric.ball_mem_nhds _ hρ)
    have heq : ∀ᶠ v in 𝓝 (0 : L), F (Multiplicative.ofAdd v) = σ v :=
      mem_of_superset (Metric.ball_mem_nhds (0 : L) hρ)
        (fun v hv => hF v (mem_ball_zero_iff.mp hv))
    exact hσ0.congr_of_eventuallyEq heq
  have hopen : IsOpenMap F := by
    apply IsTopologicalGroup.isOpenMap_iff_nhds_one.mpr
    intro U hU
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp
      (show Multiplicative.ofAdd ⁻¹' (F ⁻¹' U) ∈ 𝓝 (0 : L) from hU)
    have hmin : 0 < min r ρ := lt_min hr hρ
    refine mem_of_superset (hσnhds _ hmin) ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' := mem_ball_zero_iff.mp hv
    have h := hrU (mem_ball_zero_iff.mpr (hv'.trans_le (min_le_left _ _)))
    change F (Multiplicative.ofAdd v) ∈ U at h
    rwa [← hF v (hv'.trans_le (min_le_right _ _))]
  have hker : DiscreteTopology F.ker := by
    apply discreteTopology_of_isOpen_singleton_one
    let V : Set (Multiplicative L) := Multiplicative.toAdd ⁻¹' Metric.ball (0 : L) ρ
    have hV : IsOpen V := Metric.isOpen_ball
    have hpre : (Subtype.val : F.ker → Multiplicative L) ⁻¹' V = {1} := by
      ext x
      constructor
      · intro hx
        let v : L := x.val.toAdd
        have hv : ‖v‖ < ρ := mem_ball_zero_iff.mp (show v ∈ Metric.ball (0 : L) ρ from hx)
        have h1 : F x.val = 1 := MonoidHom.mem_ker.mp x.property
        have hσx : σ v = 1 := (hF v hv).symm.trans h1
        have hzero : (v : EuclideanSpace ℝ t) = 0 := by
          apply circleExp_coord_injective (hv.le.trans hρ1) (by simp)
          intro i
          calc
            _ = c (σ v) i := (hσc v hv i).symm
            _ = _ := by rw [hσx, map_one]; simp
        refine Set.mem_singleton_iff.mpr (Subtype.ext ?_)
        exact (show v = 0 from Subtype.ext hzero)
      · intro hx
        rw [Set.mem_singleton_iff.mp hx]
        change (0 : L) ∈ Metric.ball (0 : L) ρ
        exact Metric.mem_ball_self hρ
    exact hpre ▸ hV.preimage continuous_subtype_val
  let j : f.ker → F.ker := fun x => ⟨e.symm x.val.toAdd, x.property⟩
  refine ⟨_, f, hcont.comp e.symm.continuous, hopen.comp e.symm.toHomeomorph.isOpenMap, ?_⟩
  exact @DiscreteTopology.of_continuous_injective f.ker F.ker _ _ hker j
    ((e.symm.continuous.comp continuous_subtype_val).subtype_mk _)
    (fun x y h => Subtype.ext (e.symm.injective (congrArg Subtype.val h)))

omit [T2Space G] in
/-- If the dual is locally Euclidean, the subgroup generated by a suitable compact
neighborhood has no nontrivial characters on its quotient, so it equals the whole group. -/
private theorem isCompactlyGeneratedGroup_of_dual_locallyEuclidean
    (h : IsLocallyEuclidean (PontryaginDual G)) : IsCompactlyGeneratedGroup G := by
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean h
  obtain ⟨⟨K, U⟩, ⟨hK, hU⟩, hSub⟩ := pontryaginDual_nhds_one_hasBasis.mem_iff.mp hW
  obtain ⟨L, hL, hLnhds⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (K ∪ L)
  refine ⟨K ∪ L, mem_of_superset hLnhds subset_union_right, hK.union hL, ?_⟩
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
    (mem_of_superset hLnhds (subset_union_right.trans Subgroup.subset_closure))
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  have hKill (ψ : PontryaginDual (G ⧸ H)) : PontryaginDual.map q ψ = 1 := by
    let φ : G →ₜ* Circle := PontryaginDual.map q ψ
    apply hPow
    intro k
    apply hSub
    intro x hx
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr
      (Subgroup.subset_closure (Or.inl hx))
    change (φ ^ k) x ∈ U
    rw [ContinuousMonoidHom.pow_apply]
    change (PontryaginDual.map q ψ x) ^ k ∈ U
    rw [PontryaginDual.map_apply, hqx, map_one, one_pow]
    exact mem_of_mem_nhds hU
  refine eq_top_iff.mpr fun x _ ↦ (QuotientGroup.eq_one_iff x).mp ?_
  by_contra hx
  obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_apply_ne_one hx
  exact hψ (DFunLike.congr_fun (hKill ψ) x)

omit [T2Space G] in
/-- An LCA group is compactly generated exactly when its dual is locally Euclidean. -/
theorem isCompactlyGeneratedGroup_iff_dual_locallyEuclidean :
    IsCompactlyGeneratedGroup G ↔ IsLocallyEuclidean (PontryaginDual G) :=
  ⟨isLocallyEuclidean_dual_of_compactlyGenerated, isCompactlyGeneratedGroup_of_dual_locallyEuclidean⟩

open scoped Pointwise in
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.4.3(1), p. 757. A closed subgroup of a compactly generated
LCA group is compactly generated. -/
theorem isCompactlyGeneratedGroup_closedSubgroup (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup H := by
  classical
  obtain ⟨U, hU, hUc, hGen⟩ := hG
  -- Write every element as a product of finitely many fixed directions and a remainder in U.
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates
    ((hUc.union hUc.inv).mul hUc) ⟨1, mem_interior_iff_mem_nhds.mpr hU⟩
  let a (n : t → ℕ) : G := ∏ i : t, ((i : G)⁻¹) ^ n i
  have ha0 : a 0 = 1 := by simp [a]
  have haAdd (m n : t → ℕ) : a (m + n) = a m * a n := by
    simp only [a, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  have haSingle (i : t) : a (Pi.single i 1) = (i : G)⁻¹ := by
    unfold a
    rw [Finset.prod_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, pow_zero])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same, pow_one]
  have hStep (x : G) (hx : x ∈ U ∪ U⁻¹) (y : G)
      (hy : ∃ n : t → ℕ, ∃ u ∈ U, y = a n * u) :
      ∃ n : t → ℕ, ∃ u ∈ U, x * y = a n * u := by
    obtain ⟨n, u, hu, rfl⟩ := hy
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (ht (Set.mul_mem_mul hx hu))
    change i * (x * u) ∈ U at hiu
    refine ⟨n + Pi.single ⟨i, hi⟩ 1, i * (x * u), hiu, ?_⟩
    rw [haAdd, haSingle]
    simp [mul_assoc, mul_left_comm]
  have hRepresent (x : G) : ∃ n : t → ℕ, ∃ u ∈ U, x = a n * u := by
    have hx : x ∈ Subgroup.closure U := hGen.symm ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction_left (p := fun z _ ↦ ∃ n : t → ℕ, ∃ u ∈ U, z = a n * u)
      ⟨0, 1, mem_of_mem_nhds hU, by simp [ha0]⟩ ?_ ?_ hx
    · exact fun z hz y _ ↦ hStep z (Or.inl hz) y
    · exact fun z hz y _ ↦ hStep z⁻¹ (Or.inr (by simpa using hz)) y
  obtain ⟨V, hV, _, hVinv, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hUc
    ⟨1, mem_interior_iff_mem_nhds.mpr hV⟩
  -- For each translate, Dickson's lemma bounds the minimal nonzero exponent vectors.
  let P (i : s) (n : t → ℕ) : Prop :=
    n ≠ 0 ∧ ∃ u ∈ U, (i : G) * u ∈ V ∧ a n * u ∈ H
  let M : Set (t → ℕ) := {0} ∪ ⋃ i : s, {n | Minimal (P i) n}
  have hM : M.Finite := (finite_singleton 0).union (finite_iUnion fun i ↦
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (P i)))
  let K : Set G := (a '' M) * U
  let S : Set H := Subtype.val ⁻¹' K
  let J : Subgroup G := (Subgroup.closure S).map H.subtype
  have hK : IsCompact K := (hM.image a).isCompact.mul hUc
  have hUK : U ⊆ K := by
    intro u hu
    rw [← one_mul u, ← ha0]
    exact Set.mul_mem_mul (mem_image_of_mem a (Or.inl rfl)) hu
  have hMem (x : G) (hx : x ∈ H) (hxK : x ∈ K) : x ∈ J :=
    Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.subset_closure hxK, rfl⟩
  have hReduce (n : t → ℕ) : ∀ u ∈ U, a n * u ∈ H → a n * u ∈ J := by
    refine wellFounded_lt.induction (C := fun m ↦ ∀ u ∈ U, a m * u ∈ H → a m * u ∈ J) n ?_
    clear n
    intro n ih u hu hnu
    by_cases hn : n = 0
    · exact hMem _ hnu (Set.mul_mem_mul (mem_image_of_mem a (Or.inl hn)) hu)
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (hs hu)
    let j : s := ⟨i, hi⟩
    obtain ⟨m, hmn, hm⟩ := exists_minimal_le_of_wellFoundedLT (P j) n
      ⟨hn, u, hu, hiu, hnu⟩
    obtain ⟨hm0, v, hv, hiv, hmv⟩ := hm.prop
    obtain ⟨d, hd⟩ := exists_add_of_le hmn
    have hdn : d < n := by
      rw [hd]
      exact lt_add_of_pos_left d (lt_of_le_of_ne (fun i ↦ Nat.zero_le (m i)) hm0.symm)
    have huv : u / v ∈ U := by
      have hInv : (i * v)⁻¹ ∈ V := hVinv ▸ Set.mem_inv.mpr (by simpa using hiv)
      have hMul := hVV (Set.mul_mem_mul hiu hInv)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMul
    have hFactor : a n * u = (a m * v) * (a d * (u / v)) := by
      rw [hd, haAdd]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hdH : a d * (u / v) ∈ H := by
      simpa only [hFactor, inv_mul_cancel_left] using H.mul_mem (H.inv_mem hmv) hnu
    rw [hFactor]
    exact J.mul_mem (hMem _ hmv (Set.mul_mem_mul (mem_image_of_mem a
      (Or.inr (mem_iUnion.mpr ⟨j, hm⟩))) hv)) (ih d hdn (u / v) huv hdH)
  refine ⟨S, continuous_subtype_val.continuousAt.preimage_mem_nhds (mem_of_superset hU hUK),
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK, eq_top_iff.mpr ?_⟩
  intro x _
  obtain ⟨n, u, hu, hx⟩ := hRepresent x
  have hxJ : (x : G) ∈ J := hx ▸ hReduce n u hu (hx ▸ x.property)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxJ
  exact (Subtype.ext hyx : y = x) ▸ hy

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Theorem D.1.4.3(1), p. 757. The quotient of a compactly generated LCA
group by a closed subgroup is compactly generated. -/
theorem isCompactlyGeneratedGroup_quotient (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup (G ⧸ H) := by
  obtain ⟨U, hU, hCompact, hGen⟩ := hG
  let q := QuotientGroup.mk' H
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  refine ⟨q '' U, ?_, hCompact.image hq.continuous, ?_⟩
  · simpa only [map_one] using hq.isOpenMap.image_mem_nhds hU
  · rw [← MonoidHom.map_closure, hGen, Subgroup.map_top_of_surjective q hq.surjective]

/-- Paper: Lemma D.1.4.4, p. 758. The canonical restriction of bidual evaluation
identifies the group with the compatible families of duals of its open compactly
generated dual subgroups. Each factor is locally Euclidean. -/
theorem lca_dualSubgroups_inverseLimit :
    let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
    IsDirectedOrder I ∧
    ∃ (H : Subgroup ((J : I) → PontryaginDual J.val))
      (e : G ≃ₜ* H),
      (H : Set ((J : I) → PontryaginDual J.val)) =
        {a | ∀ (J K : I) (h : J ≤ K) (χ : J.val), a J χ = a K (Subgroup.inclusion h χ)} ∧
      (∀ x J (χ : J.val), (e x).val J χ = χ.val x) ∧
      ∀ J : I, IsLocallyEuclidean (PontryaginDual J.val) := by
  let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
  obtain ⟨γ, hEval, hEmb, hRange⟩ := lca_dualSubgroups_inverseLimit_iff_bidual (G := G)
  let H : Subgroup ((J : I) → PontryaginDual J.val) := γ.toMonoidHom.range
  let f : G →ₜ* H :=
    ⟨γ.toMonoidHom.rangeRestrict, γ.continuous.subtype_mk _⟩
  have hf : IsEmbedding f := hEmb.codRestrict H (fun x ↦ ⟨x, rfl⟩)
  have hSurj : Function.Surjective f := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  let e := MulEquiv.ofBijective f.toMonoidHom ⟨hf.injective, hSurj⟩
  have hOpen := hf.isInducing.isOpenMap (by rw [hSurj.range_eq]; exact isOpen_univ)
  refine ⟨(openCompactlyGeneratedSubgroups_colimit (G := PontryaginDual G)).1,
    H, e.toContinuousMulEquiv (fun _ ↦
    (hOpen.isQuotientMap f.continuous hSurj).isCoinducing.isOpen_preimage),
    hRange.mpr (pontryaginBidualEval_surjective (G := G)), hEval, ?_⟩
  intro J
  let : LocallyCompactSpace J.val := J.property.1.locallyCompactSpace
  exact isLocallyEuclidean_dual_of_compactlyGenerated J.property.2

end Structure

end

end Masullo
