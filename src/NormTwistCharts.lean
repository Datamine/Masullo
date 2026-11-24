/-
Adapted from the Apache-2.0 RiemannMasullo project, commit
cd84b23dd5e4f741037cf31aee06bc90161c6514.
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import NormOneClassCompact
import FinitePlaceHaar
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocalAtTarget
import IdelicArchimedeanCharacters
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Algebra.ProperAction.Basic

open Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal Manifold ContDiff NumberField RestrictedProduct

namespace Masullo

noncomputable section

/-- A splitting of a surjective modulation gives the unique kernel character and
complex exponent of a quasi-character. The absolute value is determined by the
real part of that exponent, which is the condition defining a vertical strip.
Adapted from RiemannMasullo commit 4b8ac225504ccf5f31eed72c0faf1defdcc7bc04. -/
theorem quasiCharacter_split_coordinates {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) [CompactSpace m.toMonoidHom.ker]
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) (c : G →ₜ* ℂ) :
    ∃! p : PontryaginDual m.toMonoidHom.ker × ℂ,
      (∀ (u : m.toMonoidHom.ker) (t : ℝ≥0ˣ),
        c ((u : G) * τ t) = (p.1 u : ℂ) * (((t.val : ℝ) : ℂ) ^ p.2)) ∧
      ∀ g : G, ‖c g‖ = ((m g).val : ℝ) ^ p.2.re := by
  let K := m.toMonoidHom.ker
  let d : K →ₜ* ℂ := ⟨c.toMonoidHom.comp K.subtype, c.continuous.comp continuous_subtype_val⟩
  have hnorm (u : K) : ‖d u‖ = 1 := by
    obtain ⟨v, -, hv⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty (α := K))
      d.continuous.norm.continuousOn
    have hbound (w : K) : ‖d w‖ ≤ ‖d v‖ := hv (Set.mem_univ w)
    have hle (w : K) : ‖d w‖ ≤ 1 := by
      have h := hbound (w * v)
      rw [map_mul, norm_mul] at h
      exact le_of_mul_le_mul_right (h.trans_eq (one_mul _).symm)
        (norm_pos_iff.mpr ((Group.isUnit v).map d).ne_zero)
    have hi := hle u⁻¹
    rw [map_inv, norm_inv] at hi
    exact le_antisymm (hle u) ((inv_le_one₀ (norm_pos_iff.mpr ((Group.isUnit u).map d).ne_zero)).mp hi)
  let χ : PontryaginDual K :=
    ⟨{ toFun := fun u => ⟨d u, mem_sphere_zero_iff_norm.mpr (hnorm u)⟩
       map_one' := Circle.ext (map_one d)
       map_mul' := fun x y => Circle.ext (map_mul d x y) },
      d.continuous.subtype_mk _⟩
  obtain ⟨z, hz, hz_unique⟩ := existsUnique_complexPower (c.comp τ)
  have hcoord (u : K) (t : ℝ≥0ˣ) :
      c ((u : G) * τ t) = (χ u : ℂ) * (((t.val : ℝ) : ℂ) ^ z) := by
    rw [map_mul]
    exact congrArg (d u * ·) (hz t)
  refine ⟨(χ, z), ⟨hcoord, ?_⟩, ?_⟩
  · intro g
    let t := m g
    let u : K := ⟨g * (τ t)⁻¹, by
      change m (g * (τ t)⁻¹) = 1
      rw [map_mul, map_inv, hτ t, mul_inv_cancel]⟩
    have hg : (u : G) * τ t = g := inv_mul_cancel_right g (τ t)
    rw [← hg, hcoord, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t))]
    rw [hg]
  · rintro ⟨χ', z'⟩ ⟨h', -⟩
    apply Prod.ext
    · apply DFunLike.ext
      intro u
      apply Circle.ext
      change (χ' u : ℂ) = (χ u : ℂ)
      have h := (h' u 1).symm.trans (hcoord u 1)
      simpa only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
        using h
    · apply hz_unique z'
      intro t
      have h := h' (1 : K) t
      change c ((1 : G) * τ t) = (χ' (1 : K) : ℂ) * _ at h
      rw [show χ' (1 : K) = 1 from map_one χ', Circle.coe_one, one_mul, one_mul] at h
      exact h

/-- A quasi-character in the relative vertical strip has its complex exponent in that strip. -/
theorem quasiCharacter_verticalStrip_coordinates {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) [CompactSpace m.toMonoidHom.ker]
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) (c : G →ₜ* ℂ)
    {I : Set ℝ} {σ : ℝ} (hI : σ ∈ I)
    (hσ : ∀ g : G, ‖c g‖ = ((m g).val : ℝ) ^ σ) :
    ∃! p : PontryaginDual m.toMonoidHom.ker × ℂ, p.2.re ∈ I ∧
      ∀ (u : m.toMonoidHom.ker) (t : ℝ≥0ˣ),
        c ((u : G) * τ t) = (p.1 u : ℂ) * (((t.val : ℝ) : ℂ) ^ p.2) := by
  obtain ⟨p, ⟨hp, hnorm⟩, huniq⟩ := quasiCharacter_split_coordinates m τ hτ c
  let t := Units.mk0 (2 : ℝ≥0) (by norm_num)
  have h := (hnorm (τ t)).symm.trans (hσ (τ t))
  rw [hτ t] at h
  have hRe : p.2.re = σ := (Real.rpow_right_inj (x := 2) (by norm_num) (by norm_num)).mp h
  refine ⟨p, ⟨by simpa only [hRe] using hI, hp⟩, fun q hq => huniq q ⟨hq.2, ?_⟩⟩
  intro g
  let K := m.toMonoidHom.ker
  let r := m g
  let u : K := ⟨g * (τ r)⁻¹, by
    change m (g * (τ r)⁻¹) = 1
    rw [map_mul, map_inv, hτ r, mul_inv_cancel]⟩
  have hg : (u : G) * τ r = g := inv_mul_cancel_right g (τ r)
  rw [← hg, hq.2, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt r)), hg]

/-- A complex-valued homomorphism with compact range inside the open unit ball about one
is trivial. -/
theorem monoidHom_eq_one_of_compact_range_subset_ball {G : Type*} [Monoid G]
    (q : G →* ℂ) (hK : IsCompact (Set.range q))
    (hq : Set.range q ⊆ Metric.ball 1 1) : q = 1 := by
  have hdist : Continuous (fun z : ℂ => ‖z - 1‖) :=
    (continuous_id.sub continuous_const).norm
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hK.exists_isMaxOn ⟨1, ⟨1, map_one q⟩⟩ hdist.continuousOn
  have hbound (y : G) : ‖q y - 1‖ ≤ ‖q x - 1‖ := hx (Set.mem_range_self y)
  have hclose : ‖q x - 1‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hq (Set.mem_range_self x)
  have hfactor : 1 < ‖q x + 1‖ := by
    have h := norm_add_le (q x + 1) (1 - q x)
    have hsum : q x + 1 + (1 - q x) = 2 := by ring
    rw [hsum, norm_sub_rev, Complex.norm_ofNat] at h
    linarith
  -- Squaring would increase the maximum distance from one if it were positive.
  have hsq := hbound (x ^ 2)
  have hsq_factor : q x ^ 2 - 1 = (q x + 1) * (q x - 1) := by ring
  rw [map_pow, hsq_factor, norm_mul] at hsq
  have hzero : ‖q x - 1‖ = 0 := by
    nlinarith [norm_nonneg (q x - 1)]
  ext y
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm ((hbound y).trans_eq hzero) (norm_nonneg _)))

/-- The trivial complex character of a compact monoid is isolated in the compact-open topology. -/
theorem isOpen_singleton_one_complex {G : Type*} [Monoid G] [TopologicalSpace G] [CompactSpace G] :
    IsOpen ({1} : Set (G →ₜ* ℂ)) := by
  let V : Set (G →ₜ* ℂ) := {c | Set.MapsTo c Set.univ (Metric.ball 1 1)}
  have hV : IsOpen V := isOpen_induced
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ Metric.isOpen_ball)
  have hVeq : V = {1} := by
    ext c
    rw [Set.mem_singleton_iff]
    refine ⟨fun hc ↦ ?_, ?_⟩
    · have h := monoidHom_eq_one_of_compact_range_subset_ball c.toMonoidHom
        (isCompact_range c.continuous) (by
          rintro _ ⟨x, rfl⟩
          exact hc (Set.mem_univ x))
      exact ContinuousMonoidHom.ext fun x => DFunLike.congr_fun h x
    · rintro rfl y _
      simp [Metric.mem_ball]
  simpa [hVeq] using hV

open Set Topology in
/-- A continuous complex-valued homomorphism on a product of compact monoids is trivial on
the elements that equal one in some fixed finite set of coordinates. -/
theorem exists_finset_complexCharacter_eq_one {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, CompactSpace (M i)] (c : (∀ i, M i) →ₜ* ℂ) :
    ∃ S : Finset ι, ∀ x : ∀ i, M i, (∀ i ∈ S, x i = 1) → c x = 1 := by
  classical
  have hV : c ⁻¹' Metric.ball 1 1 ∈ 𝓝 1 := c.continuous.continuousAt.preimage_mem_nhds
    (by
      change Metric.ball (1 : ℂ) 1 ∈ 𝓝 (c 1)
      rw [map_one]
      exact Metric.ball_mem_nhds _ zero_lt_one)
  rw [nhds_pi] at hV
  obtain ⟨S, V, hV, hsub⟩ := Filter.mem_pi'.mp hV
  let cut : (∀ i, M i) →* ∀ i, M i :=
    MonoidHom.pi fun i ↦ if i ∈ S then 1 else Pi.evalMonoidHom M i
  have hcut (x : ∀ i, M i) (i : ι) : cut x i = if i ∈ S then 1 else x i := by
    by_cases hi : i ∈ S <;> simp [cut, hi]
  have hc : Continuous cut := continuous_pi fun i ↦ by
    by_cases hi : i ∈ S
    · simpa only [hcut, hi, ite_true] using (continuous_const (y := (1 : M i)) :
        Continuous fun _ : ∀ j, M j ↦ (1 : M i))
    · simpa only [hcut, hi, ite_false] using
        (continuous_apply i : Continuous fun x : ∀ j, M j ↦ x i)
  let f := c.toMonoidHom.comp cut
  have hf : f = 1 := monoidHom_eq_one_of_compact_range_subset_ball f
    (isCompact_range (c.continuous.comp hc)) (by
      rintro _ ⟨x, rfl⟩
      apply hsub
      intro i hi
      change i ∈ S at hi
      rw [hcut, ite_eq_left hi]
      exact mem_of_mem_nhds (hV i))
  refine ⟨S, fun x hx ↦ ?_⟩
  have hfix : cut x = x := by
    funext i
    rw [hcut]
    split_ifs with hi
    · exact (hx i hi).symm
    · rfl
  exact hfix ▸ DFunLike.congr_fun hf x


/-- A map that agrees locally with a source chart followed by an inverse target chart
is a local diffeomorphism. -/
theorem isLocalDiffeomorph_of_chartAt {𝕜 E H M N : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I n N] (f : M → N)
    (hcenter : ∀ x, chartAt H x x ∈ (chartAt H (f x)).target)
    (heq : ∀ x y, y ∈ (chartAt H x).source → chartAt H x y ∈ (chartAt H (f x)).target →
      f y = (chartAt H (f x)).symm (chartAt H x y)) :
    IsLocalDiffeomorph I I n f := by
  intro x
  let a := chartAt H x
  let b := chartAt H (f x)
  let e := a.trans b.symm
  have ha : ContMDiffOn I I n a a.source := contMDiffOn_chart
  have ha' : ContMDiffOn I I n a.symm a.target := contMDiffOn_chart_symm
  have hb : ContMDiffOn I I n b b.source := contMDiffOn_chart
  have hb' : ContMDiffOn I I n b.symm b.target := contMDiffOn_chart_symm
  let φ : PartialDiffeomorph I I M N n :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := hb'.comp (ha.mono Set.inter_subset_left) Set.inter_subset_right
      contMDiffOn_invFun := ha'.comp (hb.mono Set.inter_subset_left) Set.inter_subset_right }
  rw [IsLocalDiffeomorphAt]
  exact ⟨φ, ⟨mem_chart_source H x, hcenter x⟩, fun y hy ↦ heq x y hy.1 hy.2⟩

/-- Paper: §3.1.1, p. 118. The space of quasi-characters has the compact-open topology.
Deviation: We use complex-valued continuous homomorphisms on a group, whose values are units. -/
abbrev QuasiCharacter (G : Type*) [Group G] [TopologicalSpace G] := G →ₜ* ℂ

section Generalities

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)

local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)


/-- The positive real units have the order topology and compact closed intervals. -/
private theorem nonnegRealUnits_orderTopology_and_compactIccSpace :
    OrderTopology ℝ≥0ˣ ∧ CompactIccSpace ℝ≥0ˣ := by
  let e := Nonneg.unitsHomeomorphPos ℝ
  let f : ℝ≥0ˣ ↪o ℝ := OrderEmbedding.ofStrictMono (Subtype.val ∘ e) (fun _ _ h => h)
  have hi : IsInducing f := (IsInducing.subtypeVal (t := Set.Ioi (0 : ℝ))).comp e.isInducing
  have hr : Set.range f = Set.Ioi 0 := by
    change Set.range ((Subtype.val : Set.Ioi (0 : ℝ) → ℝ) ∘ e) = _
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ (e y).property,
      fun hx => ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩⟩
  have ho : Set.OrdConnected (Set.range f) := hr.symm ▸ Set.ordConnected_Ioi
  refine ⟨⟨hi.eq_induced.trans (f.strictMono.induced_topology_eq_preorder ho)⟩, ⟨?_⟩⟩
  intro a b
  apply hi.isCompact_iff.mpr
  rw [f.image_Icc ho]
  exact isCompact_Icc

/-- Paper: §3.1.1, p. 119. Near each quasi-character the complex exponent is a coordinate
centered at zero. Its inverse sends z to the character twisted by the z-th power of the module. -/
def HasNormTwistCharts : Prop :=
  ∀ c : QuasiCharacter G, ∃ e : OpenPartialHomeomorph (QuasiCharacter G) ℂ,
    c ∈ e.source ∧ e c = 0 ∧
      ∀ z ∈ e.target, ∀ g, e.symm z g = c g * (modℝ g : ℂ) ^ z

/-- A quasi-character trivial at an element of module greater than one is trivial
if its values stay in the open unit ball about one on the corresponding norm interval. -/
private theorem quasiCharacter_eq_one_of_normInterval {g : G}
    (hK : IsCompact (m ⁻¹' Set.Icc 1 (m g)))
    (hg : 1 < m g) (q : QuasiCharacter G) (hqg : q g = 1)
    (hq : Set.MapsTo q (m ⁻¹' Set.Icc 1 (m g)) (Metric.ball 1 1)) : q = 1 := by
  let K := m ⁻¹' Set.Icc 1 (m g)
  -- Multiplying by powers of g moves any element into K without changing its value.
  have himage : Set.range (q : G → ℂ) = q '' K := by
    refine Set.Subset.antisymm (Set.range_subset_iff.mpr fun y => ?_) (Set.image_subset_range _ _)
    obtain ⟨n, hn, -⟩ := existsUnique_zpow_near_of_one_lt' hg (m y)
    refine ⟨y / g ^ n, ?_, by rw [map_div, map_zpow, hqg, one_zpow, div_one]⟩
    simpa only [K, Set.mem_preimage, map_div, map_zpow, Set.mem_Icc] using ⟨hn.1, hn.2.le⟩
  have heq := monoidHom_eq_one_of_compact_range_subset_ball q.toMonoidHom
    (himage ▸ hK.image q.continuous) (himage ▸ hq.image_subset)
  exact ContinuousMonoidHom.ext fun x => DFunLike.congr_fun heq x

/-- Paper: §3.1.1, p. 119. Every modulated group admits local norm-twist coordinates,
including when the complex exponent is defined globally only modulo a period. -/
theorem hasNormTwistCharts_of_proper [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) : HasNormTwistCharts m := by
  intro c
  obtain ⟨g, hg⟩ : ∃ g, 1 < m g := by
    obtain ⟨g, hg⟩ := hne
    rcases lt_or_gt_of_ne hg with h | h
    · exact ⟨g⁻¹, by simpa only [map_inv, one_lt_inv'] using h⟩
    · exact ⟨g, h⟩
  have hpos (x : G) : 0 < modℝ x :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m x).ne_zero)
  let L (x : G) : ℂ := Real.log (modℝ x)
  have hLg : L g ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one (hpos g) fun h =>
      hg.ne (Units.val_inj.mp (NNReal.coe_inj.mp h)).symm)
  have hL : Continuous L := Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp hm.continuous)).log
      fun x => (hpos x).ne')
  let twist (z : ℂ) : QuasiCharacter G :=
    c * { toFun := fun x => Complex.exp (L x * z)
          map_one' := by simp [L]
          map_mul' := by
            intro x y
            simp only [L, map_mul, Units.val_mul, NNReal.coe_mul,
              Real.log_mul (hpos x).ne' (hpos y).ne', Complex.ofReal_add, add_mul, Complex.exp_add]
          continuous_toFun := (hL.mul continuous_const).cexp }
  have htwist (z : ℂ) (x : G) : twist z x = c x * Complex.exp (L x * z) := rfl
  have htwist_cont : Continuous twist := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (c.continuous.comp continuous_snd).mul
      (((hL.comp continuous_snd).mul continuous_fst).cexp)
  have hneval (d : QuasiCharacter G) (x : G) : d x ≠ 0 := ((Group.isUnit x).map d).ne_zero
  -- Evaluation at g recovers the exponent using the principal logarithm.
  let ratio (d : QuasiCharacter G) : ℂ := d g / c g
  let expChart := Complex.expOpenPartialHomeomorph
  let coord (d : QuasiCharacter G) : ℂ := expChart.symm (ratio d) / L g
  let U := ratio ⁻¹' expChart.target
  let T := (L g * ·) ⁻¹' expChart.source
  have hratio : Continuous ratio := (continuous_eval_const g).div_const (c g)
  have hU : IsOpen U := expChart.open_target.preimage hratio
  have hcoord : ContinuousOn coord U :=
    (expChart.continuousOn_invFun.comp hratio.continuousOn (fun _ h => h)).div_const _
  have hscale (d : QuasiCharacter G) : L g * coord d = expChart.symm (ratio d) := by
    change L g * (expChart.symm (ratio d) / L g) = _
    rw [mul_comm, div_mul_cancel₀ _ hLg]
  let residual (d : QuasiCharacter G) :=
    d * (twist (coord d)).comp (ContinuousMonoidHom.inv G)
  have hresidual (d : QuasiCharacter G) (x : G) : residual d x = d x / twist (coord d) x := by
    change d x * twist (coord d) x⁻¹ = _
    rw [map_inv, div_eq_mul_inv]
  have hresidual_cont : ContinuousOn (fun d => (residual d).toContinuousMap) U := by
    have hforget : Continuous (ContinuousMonoidHom.toContinuousMap : QuasiCharacter G → C(G, ℂ)) :=
      (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous
    have hinv := (ContinuousMonoidHom.inv G).continuous_comp_left (C := ℂ)
    exact hforget.continuousOn.mul
      ((hforget.comp hinv).comp_continuousOn' (htwist_cont.comp_continuousOn' hcoord))
  -- On the chart source the residual stays close to one on a compact norm interval.
  let K := m ⁻¹' Set.Icc 1 (m g)
  let V : Set C(G, ℂ) := {f | Set.MapsTo f K (Metric.ball 1 1)}
  let S := U ∩ (fun d => (residual d).toContinuousMap) ⁻¹' V
  have := nonnegRealUnits_orderTopology_and_compactIccSpace.2
  have hK : IsCompact K := hm.isCompact_preimage isCompact_Icc
  have hS : IsOpen S := hresidual_cont.isOpen_inter_preimage hU
    (ContinuousMap.isOpen_setOfPred_mapsTo hK Metric.isOpen_ball)
  have hratio_twist (z : ℂ) : ratio (twist z) = expChart (L g * z) := by
    change twist z g / c g = Complex.exp (L g * z)
    rw [htwist, mul_div_cancel_left₀ _ (hneval c g)]
  have hright (z : ℂ) (hz : z ∈ T) : coord (twist z) = z := by
    change expChart.symm (ratio (twist z)) / L g = z
    rw [hratio_twist, expChart.left_inv hz, mul_div_cancel_left₀ _ hLg]
  have hleft (d : QuasiCharacter G) (hd : d ∈ S) : twist (coord d) = d := by
    have hrg : residual d g = 1 := by
      have hval : twist (coord d) g = d g := by
        rw [htwist, hscale]
        change c g * expChart (expChart.symm (ratio d)) = d g
        rw [expChart.right_inv hd.1, mul_comm]
        exact div_mul_cancel₀ _ (hneval c g)
      rw [hresidual, hval, div_self (hneval d g)]
    have h := quasiCharacter_eq_one_of_normInterval m hK hg (residual d) hrg hd.2
    ext1 x
    have hx : residual d x = 1 := DFunLike.congr_fun h x
    exact ((div_eq_one_iff_eq (hneval _ x)).mp (hresidual d x ▸ hx)).symm
  let e : OpenPartialHomeomorph (QuasiCharacter G) ℂ := {
    toFun := coord
    invFun := twist
    source := S
    target := T
    map_source' d hd := by
      change L g * coord d ∈ expChart.source
      rw [hscale]
      exact expChart.map_target hd.1
    map_target' z hz := by
      refine ⟨?_, ?_⟩
      · change ratio (twist z) ∈ expChart.target
        rw [hratio_twist]
        exact expChart.map_source hz
      · intro x _
        change residual (twist z) x ∈ Metric.ball 1 1
        rw [hresidual, hright z hz, div_self (hneval _ x)]
        exact Metric.mem_ball_self zero_lt_one
    left_inv' := hleft
    right_inv' := hright
    open_source := hS
    open_target := expChart.open_source.preimage (continuous_const.mul continuous_id)
    continuousOn_toFun := hcoord.mono Set.inter_subset_left
    continuousOn_invFun := htwist_cont.continuousOn }
  have hzero : (0 : ℂ) ∈ T := by
    change L g * 0 ∈ expChart.source
    simp [expChart, Complex.expOpenPartialHomeomorph, Real.pi_pos]
  have htwist_zero : twist 0 = c := by
    ext1 x
    simp [htwist]
  refine ⟨e, htwist_zero ▸ e.map_target hzero, ?_, fun z _ x => ?_⟩
  · change coord c = 0
    rw [← htwist_zero, hright 0 hzero]
  · change twist z x = _
    rw [htwist, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hpos x).ne'),
      ← Complex.ofReal_log (hpos x).le]

/-- Paper: §3.1.1, p. 119. Choose one norm-twist chart around each point. These charts form
an atlas on the existing compact-open space. -/
@[instance_reducible] def quasiCharacterChartedSpace (h : HasNormTwistCharts m) :
    ChartedSpace ℂ (QuasiCharacter G) where
  atlas := Set.range fun c => (h c).choose
  chartAt c := (h c).choose
  mem_chart_source c := (h c).choose_spec.1
  chart_mem_atlas c := ⟨c, rfl⟩

/-- Paper: §3.1.1, p. 119. The atlas of complex norm-twist coordinates is analytic. -/
theorem quasiCharacter_isManifold (h : HasNormTwistCharts m) :
    letI := quasiCharacterChartedSpace m h
    IsManifold 𝓘(ℂ) ω (QuasiCharacter G) := by
  let := quasiCharacterChartedSpace m h
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range (fun c => (h c).choose) at he
  change e' ∈ Set.range (fun c => (h c).choose) at he'
  obtain ⟨c, rfl⟩ := he
  obtain ⟨d, rfl⟩ := he'
  let e := (h c).choose
  let e' := (h d).choose
  have hc := (h c).choose_spec.2.2
  have hd := (h d).choose_spec.2.2
  change ContDiffOn ℂ ω (e.symm.trans e') ((e.symm.trans e').source ∩ Set.range id)
  rw [Set.range_id, Set.inter_univ]
  intro z hz
  have hz' : z ∈ e.target ∧ e.symm z ∈ e'.source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] using hz
  let w := e' (e.symm z)
  have hw : w ∈ e'.target := e'.map_source hz'.2
  have hbase (g : G) : c g * (modℝ g : ℂ) ^ z = d g * (modℝ g : ℂ) ^ w := by
    rw [← hc z hz'.1 g, ← hd w hw g]
    exact congrArg (fun q : QuasiCharacter G => q g) (e'.left_inv hz'.2).symm
  -- Adding the same increment to both coordinates twists both characters by the same power.
  let translate (y : ℂ) := w + (y - z)
  have hsmooth : ContDiff ℂ ω translate := contDiff_const.add (contDiff_id.sub contDiff_const)
  have hnear : translate ⁻¹' e'.target ∈ 𝓝 z :=
    (e'.open_target.preimage hsmooth.continuous).mem_nhds (by simpa [translate] using hw)
  refine hsmooth.contDiffWithinAt.congr_of_eventuallyEq_of_mem ?_ hz
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hnear]
    with y hy htranslate
  have hy' : y ∈ e.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy
    exact hy.1
  have heq : e.symm y = e'.symm (translate y) := by
    ext1 g
    have hmod : (modℝ g : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m g).ne_zero)
    rw [hc y hy' g, hd (translate y) htranslate g]
    change c g * (modℝ g : ℂ) ^ y = d g * (modℝ g : ℂ) ^ (w + (y - z))
    rw [Complex.cpow_add _ _ hmod, ← mul_assoc, ← hbase g, mul_assoc,
      ← Complex.cpow_add _ _ hmod, show z + (y - z) = y by abel]
  change e' (e.symm y) = translate y
  rw [heq, e'.right_inv htranslate]

/-- Pullback along a modulus-preserving homomorphism is a local analytic isomorphism
in the norm-twist atlases. In coordinates at a character and its pullback it is the identity. -/
theorem quasiCharacter_comp_isLocalDiffeomorph {H : Type*} [CommGroup H] [TopologicalSpace H]
    (n : H →* ℝ≥0ˣ) (i : H →ₜ* G) (hi : ∀ x, m (i x) = n x)
    (hG : HasNormTwistCharts m) (hH : HasNormTwistCharts n) :
    letI := quasiCharacterChartedSpace m hG
    letI := quasiCharacterChartedSpace n hH
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (fun c : QuasiCharacter G ↦ c.comp i) := by
  let := quasiCharacterChartedSpace m hG
  let := quasiCharacterChartedSpace n hH
  let := quasiCharacter_isManifold m hG
  let := quasiCharacter_isManifold n hH
  apply isLocalDiffeomorph_of_chartAt 𝓘(ℂ) ω
  · intro c
    let d := c.comp i
    let a := (hG c).choose
    let b := (hH d).choose
    change a c ∈ b.target
    rw [show a c = b d from (hG c).choose_spec.2.1.trans (hH d).choose_spec.2.1.symm]
    exact b.map_source (hH d).choose_spec.1
  · intro c y hy hz
    let d := c.comp i
    let a := (hG c).choose
    let b := (hH d).choose
    ext1 x
    change y (i x) = b.symm (a y) x
    rw [(hH d).choose_spec.2.2 (a y) hz x]
    change y (i x) = c (i x) * (((n x : ℝ≥0) : ℝ) : ℂ) ^ (a y)
    rw [← hi x]
    exact (congrArg (fun q : QuasiCharacter G ↦ q (i x)) (a.left_inv hy)).symm.trans
      ((hG c).choose_spec.2.2 _ (a.map_source hy) (i x))

end Generalities

/-- On the units of a proper normed field, every positive natural power of the norm is proper. -/
theorem isProperMap_units_nnnorm_pow {K : Type*} [NormedField K] [ProperSpace K]
    (n : ℕ) (hn : n ≠ 0) :
    IsProperMap ((Units.map nnnormHom.toMonoidHom) ^ n : Kˣ →* ℝ≥0ˣ) := by
  let f (x : K) := ‖x‖₊ ^ n
  have hnorm : IsProperMap (fun x : K ↦ ‖x‖₊) := by
    simpa only [show (nndist (0 : K)) = (fun x ↦ ‖x‖₊) from funext nndist_zero_left] using
      isProperMap_nndist (0 : K)
  have hf : IsProperMap f := (NNReal.powOrderIso n hn).toHomeomorph.isProperMap.comp hnorm
  let s := {t : ℝ≥0 | t ≠ 0}
  have hpre : {x : K | x ≠ 0} = f ⁻¹' s := by
    ext x
    simp [f, s, hn]
  let e := (unitsHomeomorphNeZero (G₀ := K)).trans (Homeomorph.setCongr hpre)
  let u : Kˣ →* ℝ≥0ˣ := (Units.map nnnormHom.toMonoidHom) ^ n
  have hu : Continuous u := (continuous_nnnorm.units_map nnnormHom.toMonoidHom).pow n
  apply isProperMap_of_comp_of_inj hu (unitsHomeomorphNeZero (G₀ := ℝ≥0)).continuous _
    (unitsHomeomorphNeZero (G₀ := ℝ≥0)).injective
  exact (hf.restrictPreimage s).comp e.isProperMap


section LocalCharts

variable (F : Type*) [Field F] [NumberField F]

def globalNormUnits : IdeleClass F →* ℝ≥0ˣ where
  toFun g := Units.mk0 ⟨ideleClassNorm F g, (ideleClassNorm_pos F g).le⟩
    (fun h => (ideleClassNorm_pos F g).ne' (congrArg NNReal.toReal h))
  map_one' := Units.ext (NNReal.eq (map_one (ideleClassNorm F)))
  map_mul' x y := Units.ext (NNReal.eq (map_mul (ideleClassNorm F) x y))

theorem globalNormUnits_proper : IsProperMap (globalNormUnits F) := by
  letI := normOneIdeleClass_compact F
  let h := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let a : Multiplicative ℝ ≃ₜ ℝ :=
    ⟨Multiplicative.toAdd, continuous_toAdd, continuous_ofAdd⟩
  have hp : IsProperMap (Prod.snd ∘ ideleClassSplitHomeomorph F) :=
    isProperMap_snd_of_compactSpace.comp (ideleClassSplitHomeomorph F).isProperMap
  have he : (globalNormUnits F : IdeleClass F → ℝ≥0ˣ) =
      (h : ℝ → ℝ≥0ˣ) ∘ Multiplicative.toAdd ∘ Prod.snd ∘ ideleClassSplitHomeomorph F := by
    funext x
    apply Units.ext
    apply NNReal.eq
    change ideleClassNorm F x = Real.exp (Real.log (ideleClassNorm F x))
    exact (Real.exp_log (ideleClassNorm_pos F x)).symm
  rw [he]
  exact h.isProperMap.comp (a.isProperMap.comp hp)

theorem globalNorm_hasNormTwistCharts :
    HasNormTwistCharts (G := IdeleClass F) (globalNormUnits F) := by
  letI := ideleClasses_locallyCompact (F := F)
  letI := ideleClasses_hausdorff (F := F)
  apply hasNormTwistCharts_of_proper _ (globalNormUnits_proper F)
  refine ⟨ideleClassExpSection F (Multiplicative.ofAdd 1), fun h => ?_⟩
  have he := congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) h
  change ideleClassNorm F (ideleClassExpSection F (Multiplicative.ofAdd 1)) = 1 at he
  rw [ideleClassNorm_expSection] at he
  exact (Real.one_lt_exp_iff.mpr zero_lt_one).ne' he

private def finiteLocalNormUnits (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →* ℝ≥0ˣ :=
  Units.map nnnormHom.toMonoidHom

private def infiniteLocalNormUnits (v : InfinitePlace F) : v.Completionˣ →* ℝ≥0ˣ :=
  (Units.map nnnormHom.toMonoidHom) ^ v.mult

private theorem finiteLocalNorm_hasNormTwistCharts (v : HeightOneSpectrum (𝓞 F)) :
    HasNormTwistCharts (finiteLocalNormUnits F v) := by
  letI := finitePlace_locallyCompact F v
  let π := chosenFiniteUniformizer F v
  have hπ := norm_finiteUniformizer F v _ (chosenFiniteUniformizer_spec F v)
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    ⟨⟨((π : v.adicCompletion F)⁻¹), by rw [norm_inv, hπ, inv_inv]; exact hq⟩⟩
  letI : ProperSpace (v.adicCompletion F) :=
    .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  letI : LocallyCompactSpace ((v.adicCompletion F)ˣ) :=
    ((isClosed_singleton (x := (0 : v.adicCompletion F))).isOpen_compl.isOpenEmbedding_subtypeVal.comp
      (unitsHomeomorphNeZero (G₀ := v.adicCompletion F)).isOpenEmbedding).locallyCompactSpace
  apply hasNormTwistCharts_of_proper
  · let b := finiteLocalNormUnits F v
    have he : (b ^ (1 : ℕ)) = b := pow_one b
    have hp : IsProperMap (b ^ (1 : ℕ)) :=
      isProperMap_units_nnnorm_pow (K := v.adicCompletion F) 1 one_ne_zero
    rw [he] at hp
    exact hp
  · refine ⟨π, fun h => ?_⟩
    have hc := congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) h
    change ‖(π : v.adicCompletion F)‖ = 1 at hc
    rw [hπ] at hc
    exact (inv_lt_one_of_one_lt₀ hq).ne hc

private theorem infiniteLocalNorm_hasNormTwistCharts (v : InfinitePlace F) :
    HasNormTwistCharts (infiniteLocalNormUnits F v) := by
  have htwo : 1 < ‖(2 : v.Completion)‖ := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _) (2 : v.Completion), map_ofNat]
    norm_num
  letI : NontriviallyNormedField v.Completion := ⟨⟨2, htwo⟩⟩
  letI : ProperSpace v.Completion :=
    .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace v.Completion
  letI : LocallyCompactSpace (v.Completionˣ) :=
    ((isClosed_singleton (x := (0 : v.Completion))).isOpen_compl.isOpenEmbedding_subtypeVal.comp
      (unitsHomeomorphNeZero (G₀ := v.Completion)).isOpenEmbedding).locallyCompactSpace
  apply hasNormTwistCharts_of_proper _ (isProperMap_units_nnnorm_pow v.mult v.mult_ne_zero)
  let u := Units.mk0 (2 : v.Completion) (by rintro h; rw [h, norm_zero] at htwo; linarith)
  refine ⟨u, fun he ↦ ?_⟩
  have hv := congrArg (fun y : ℝ≥0ˣ ↦ ((y : ℝ≥0) : ℝ)) he
  change ‖(2 : v.Completion)‖ ^ v.mult = 1 at hv
  exact (one_lt_pow₀ htwo v.mult_ne_zero).ne' hv

def finitePlaceInsertion (v : HeightOneSpectrum (𝓞 F)) :
    (v.adicCompletion F)ˣ →ₜ* IdeleClass F := by
  classical
  let P := HeightOneSpectrum (𝓞 F)
  let R (w : P) := w.adicCompletion F
  let O (w : P) := w.adicCompletionIntegers F
  let S : Set P := {v}ᶜ
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr (eventually_cofinite_ne v)
  let a (x : R v) : Πʳ w, [R w, O w]_[𝓟 S] :=
    ⟨Function.update (fun w : P => (1 : R w)) v x, by
      apply eventually_principal.mpr
      intro w hw
      rw [Function.update_of_ne (show w ≠ v from hw)]
      exact (O w).one_mem⟩
  have ha : Continuous a := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro w
    change Continuous (fun x : R v => Function.update (fun i : P => (1 : R i)) v x w)
    by_cases hw : w = v
    · subst w
      exact continuous_id.congr fun x => (Function.update_self v x _).symm
    · exact (continuous_const (y := (1 : R w))).congr
        fun x => (Function.update_of_ne hw x (fun i : P => (1 : R i))).symm
  let b : R v → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.inclusion R (fun w => (O w : Set (R w))) hS ∘ a
  have hb : Continuous b := (RestrictedProduct.continuous_inclusion hS).comp ha
  have hcoord (x : R v) (w : P) :
      b x w = Function.update (fun i : P => (1 : R i)) v x w := rfl
  let f : R v →* AdeleRing (𝓞 F) F :=
    { toFun := fun x => (1, b x)
      map_one' := by
        change (1, b 1) = ((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
        refine Prod.ext ?_ ?_
        · rfl
        · apply DFunLike.ext
          intro w
          change b 1 w = (1 : R w)
          rw [hcoord]
          by_cases hw : w = v
          · subst w; simp
          · simp [Function.update_of_ne hw]
      map_mul' x y := by
        apply Prod.ext (by change (1 : InfiniteAdeleRing F) = 1 * 1; simp)
        apply DFunLike.ext
        intro w
        change b (x * y) w = b x w * b y w
        simp only [hcoord]
        by_cases hw : w = v
        · subst w; simp
        · simp [Function.update_of_ne hw] }
  have hf : Continuous f := continuous_const.prodMk hb
  let q : Idele F →ₜ* IdeleClass F := ⟨ideleClassMap F, ideleClassMap_continuous F⟩
  exact q.comp ⟨Units.map f, hf.units_map f⟩

theorem finitePlaceInsertion_apply (v : HeightOneSpectrum (𝓞 F))
    (u : (v.adicCompletion F)ˣ) :
    finitePlaceInsertion F v u = ideleClassMap F (singleFiniteIdele F v u) := by
  classical
  unfold finitePlaceInsertion
  apply congrArg (ideleClassMap F)
  apply Units.ext
  apply Prod.ext rfl
  apply DFunLike.ext
  intro w
  rfl

/-- Insert a unit at one infinite place and pass to its idele class. -/
def infinitePlaceInsertion (v : InfinitePlace F) :
    v.Completionˣ →ₜ* IdeleClass F :=
  (show Idele F →ₜ* IdeleClass F from ⟨ideleClassMap F, ideleClassMap_continuous F⟩).comp
    (singleInfiniteIdele F v)

theorem infinitePlaceInsertion_norm (v : InfinitePlace F) (u : v.Completionˣ) :
    ideleClassNorm F (infinitePlaceInsertion F v u) = ‖(u : v.Completion)‖ ^ v.mult := by
  classical
  let d := singleInfiniteIdele F v u
  change ideleClassNorm F (ideleClassMap F d) = _
  rw [ideleClassNorm_mk]
  change (∏ w : InfinitePlace F, ‖d.val.1 w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖d.val.2 w‖) = _
  have hfinite (w : HeightOneSpectrum (𝓞 F)) : d.val.2 w = 1 := rfl
  have hinfinite (w : InfinitePlace F) :
      d.val.1 w = Function.update (fun j : InfinitePlace F => (1 : j.Completion)) v
        (u : v.Completion) w := rfl
  simp only [hfinite, norm_one, finprod_one, mul_one, hinfinite]
  rw [Fintype.prod_eq_single v]
  · rw [Function.update_self]
  · intro w hw
    rw [Function.update_of_ne hw, norm_one, one_pow]

/-- Insertion at an infinite place is proper because the class norm records
the positive power of the local norm. -/
theorem infinitePlaceInsertion_isProper (v : InfinitePlace F) :
    IsProperMap (infinitePlaceInsertion F v) := by
  letI : T2Space (IdeleClass F) := ideleClasses_hausdorff
  letI : LocallyCompactSpace (IdeleClass F) := ideleClasses_locallyCompact
  have htwo : 1 < ‖(2 : v.Completion)‖ := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _) (2 : v.Completion), map_ofNat]
    norm_num
  letI : NontriviallyNormedField v.Completion := ⟨⟨2, htwo⟩⟩
  letI : ProperSpace v.Completion :=
    .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace v.Completion
  let i := infinitePlaceInsertion F v
  let m := globalNormUnits F
  let d := infiniteLocalNormUnits F v
  have hD : IsProperMap d := isProperMap_units_nnnorm_pow v.mult v.mult_ne_zero
  have he (u : v.Completionˣ) : d u = m (i u) := by
    apply Units.ext
    apply NNReal.eq
    change ‖u.val‖ ^ v.mult = ideleClassNorm F (infinitePlaceInsertion F v u)
    exact (infinitePlaceInsertion_norm F v u).symm
  refine isProperMap_iff_isCompact_preimage.mpr ⟨i.continuous, fun C hC ↦ ?_⟩
  refine (hD.isCompact_preimage (hC.image (globalNormUnits_proper F).continuous)).of_isClosed_subset
    (hC.isClosed.preimage i.continuous) ?_
  intro u hu
  exact ⟨i u, hu, (he u).symm⟩

set_option maxHeartbeats 2000000 in
/-- Lemma 3.1.2.1 at every finite place, with the normalized local absolute value. -/
theorem finitePlaceRestriction_isLocalDiffeomorph (v : HeightOneSpectrum (𝓞 F)) :
    letI := quasiCharacterChartedSpace _ (globalNorm_hasNormTwistCharts F)
    letI := quasiCharacterChartedSpace _ (finiteLocalNorm_hasNormTwistCharts F v)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω
      (fun c : QuasiCharacter (IdeleClass F) => c.comp (finitePlaceInsertion F v)) := by
  refine quasiCharacter_comp_isLocalDiffeomorph (G := IdeleClass F)
    (H := (v.adicCompletion F)ˣ) (globalNormUnits F) (finiteLocalNormUnits F v)
    (finitePlaceInsertion F v) ?_ (globalNorm_hasNormTwistCharts F) (finiteLocalNorm_hasNormTwistCharts F v)
  intro u
  apply Units.ext
  apply NNReal.eq
  change ideleClassNorm F (finitePlaceInsertion F v u) = ‖(u : v.adicCompletion F)‖
  rw [finitePlaceInsertion_apply, ideleClassNorm_mk, singleFiniteIdele_norm]

set_option maxHeartbeats 2000000 in
/-- Lemma 3.1.2.1 at every infinite place, with its real or complex multiplicity. -/
theorem infinitePlaceRestriction_isLocalDiffeomorph (v : InfinitePlace F) :
    letI := quasiCharacterChartedSpace _ (globalNorm_hasNormTwistCharts F)
    letI := quasiCharacterChartedSpace _ (infiniteLocalNorm_hasNormTwistCharts F v)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω
      (fun c : QuasiCharacter (IdeleClass F) => c.comp (infinitePlaceInsertion F v)) := by
  refine quasiCharacter_comp_isLocalDiffeomorph (G := IdeleClass F)
    (H := v.Completionˣ) (globalNormUnits F) (infiniteLocalNormUnits F v)
    (infinitePlaceInsertion F v) ?_ (globalNorm_hasNormTwistCharts F) (infiniteLocalNorm_hasNormTwistCharts F v)
  intro u
  apply Units.ext
  apply NNReal.eq
  change ideleClassNorm F (infinitePlaceInsertion F v u) = ‖(u : v.Completion)‖ ^ v.mult
  exact infinitePlaceInsertion_norm F v u

end LocalCharts

end
end Masullo
