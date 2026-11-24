import BruhatCompactSupport
import BruhatDistributionSupport
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.BumpFunction.Basic

open Filter Function Set Topology
open scoped ContDiff

namespace Masullo

noncomputable section
set_option maxHeartbeats 1400000

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F]
  [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "R" => EuclideanSpace ℝ (Fin m)
local notation "Torus" => Fin n → AddCircle (1 : ℝ)
local notation "D" => (Fin r → ℤ) × F

/-- Elementary Schwartz tests admit compactly supported local units
inside every prescribed open neighborhood. -/
theorem exists_elementarySchwartz_local_unit {x : A} {U : Set A}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ f : ElementarySchwartz m n r F,
      HasCompactSupport f.val ∧ tsupport f.val ⊆ U ∧ (f.val =ᶠ[𝓝 x] fun _ ↦ 1) ∧
      (∀ y, 0 ≤ (f.val y).re ∧ (f.val y).im = 0) := by
  classical
  let c : R × Torus := (x.1, x.2.1)
  let d : D := x.2.2
  let E := R × (Fin n → ℂ)
  let j (t : Torus) (i : Fin n) : ℂ := (fourier (T := 1) 1) (t i)
  have hjc : Continuous j := continuous_pi fun i ↦ (fourier (T := 1) 1).continuous.comp
    (continuous_apply i)
  have hj : IsEmbedding j := (hjc.isClosedEmbedding (by
    intro a b he
    funext i
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa only [j, fourier_one] using congrFun he i)).isEmbedding
  let φ : R × Torus → E := Prod.map id j
  have hφ : IsEmbedding φ := IsEmbedding.id.prodMap hj
  let p : A → R × Torus := fun y ↦ (y.1, y.2.1)
  have hp : Continuous p := continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  let s : R × Torus → A := fun y ↦ (y.1, y.2, d)
  have hs : Continuous s :=
    continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have hsc : s c = x := rfl
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have hV : s ⁻¹' (U ∩ interior K) ∈ 𝓝 c :=
    hs.continuousAt.preimage_mem_nhds (show U ∩ interior K ∈ 𝓝 (s c) from hsc.symm ▸
      inter_mem (hU.mem_nhds hx) (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hxK)))
  rw [hφ.isInducing.nhds_eq_comap c] at hV
  obtain ⟨W, hW, hWV⟩ := mem_comap.mp hV
  obtain ⟨ρ, hρ, hρW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hW
  let bump : ContDiffBump (φ c) := ⟨ρ/2, ρ, by positivity, by linarith⟩
  let f (y : A) : ℂ := if y.2.2 = d then (bump (φ (p y)) : ℂ) else 0
  let B : Set A := {y | y.2.2 = d} ∩ (φ ∘ p) ⁻¹' Metric.closedBall (φ c) ρ
  have hD : Continuous (fun y : A ↦ y.2.2) := continuous_snd.comp continuous_snd
  have hB : IsClosed B := (isClosed_eq hD continuous_const).inter
    (Metric.isClosed_closedBall.preimage (hφ.continuous.comp hp))
  have hsup : tsupport f ⊆ B := by
    apply closure_minimal _ hB
    intro y hy
    have he : y.2.2 = d := by
      by_contra hn
      exact hy (ite_eq_right hn)
    refine ⟨he, ?_⟩
    by_contra hball
    apply hy
    have hρle : ρ ≤ dist (φ (p y)) (φ c) :=
      le_of_lt (lt_of_not_ge (show ¬ dist (φ (p y)) (φ c) ≤ ρ from hball))
    simp only [f, ite_eq_left he, bump.zero_of_le_dist hρle, Complex.ofReal_zero]
  have hBU : B ⊆ U ∩ K := by
    intro y hy
    have hys : s (p y) = y := by
      rcases y with ⟨yR, yT, yD⟩
      exact congrArg (fun a ↦ (yR, yT, a)) hy.1.symm
    have hb : φ (p y) ∈ Metric.closedBall (φ c) ρ := hy.2
    have hyW : p y ∈ φ ⁻¹' W := hρW hb
    have h : s (p y) ∈ U ∩ interior K := hWV hyW
    rw [hys] at h
    exact ⟨h.1, interior_subset h.2⟩
  have hcomp : HasCompactSupport f :=
    hK.of_isClosed_subset isClosed_closure (hsup.trans (hBU.trans inter_subset_right))
  have hSmooth : ∀ a b, ContDiff ℝ ∞ (fun w ↦ f (elementaryCover w a b)) := by
    intro a b
    by_cases hab : (a,b) = d
    · have hφ' : ContDiff ℝ ∞ (fun w : R × EuclideanSpace ℝ (Fin n) ↦
          φ (w.1, fun i ↦ ((w.2 i : ℝ) : AddCircle (1 : ℝ)))) := by
        apply contDiff_fst.prodMk
        apply contDiff_pi.mpr
        intro i
        change ContDiff ℝ ∞ (fun w : R × EuclideanSpace ℝ (Fin n) ↦
          fourier (T := 1) 1 ((w.2 i : ℝ) : AddCircle (1 : ℝ)))
        simp only [fourier_coe_apply]
        have hCoord : ContDiff ℝ ∞ (fun w : R × EuclideanSpace ℝ (Fin n) ↦
            ((w.2 i : ℝ) : ℂ)) :=
          Complex.ofRealCLM.contDiff.comp ((contDiff_piLp_apply 2 (i := i)).comp contDiff_snd)
        fun_prop
      change ContDiff ℝ ∞ (fun w : R × EuclideanSpace ℝ (Fin n) ↦
        if (a,b) = d then (bump (φ (w.1, fun i ↦ ((w.2 i : ℝ) : AddCircle (1 : ℝ)))) : ℂ)
        else 0)
      simp only [ite_eq_left hab]
      exact Complex.ofRealCLM.contDiff.comp (bump.contDiff.comp hφ')
    · change ContDiff ℝ ∞ (fun w : R × EuclideanSpace ℝ (Fin n) ↦
        if (a,b) = d then (bump (φ (w.1, fun i ↦ ((w.2 i : ℝ) : AddCircle (1 : ℝ)))) : ℂ)
        else 0)
      simp only [ite_eq_right hab]
      exact contDiff_const
  refine ⟨⟨f, elementarySchwartz_mem_of_compactSupport f hcomp hSmooth⟩, hcomp,
    hsup.trans (hBU.trans inter_subset_left), ?_, ?_⟩
  swap
  · intro y
    change 0 ≤ (f y).re ∧ (f y).im = 0
    by_cases hy : y.2.2 = d
    · simp [f, hy, bump.nonneg]
    · simp [f, hy]
  have hnear : ∀ᶠ y in 𝓝 x, y.2.2 = d :=
    (hD.continuousAt.preimage_mem_nhds (isOpen_discrete ({d} : Set D) |>.mem_nhds rfl))
  have hbump := (hφ.continuous.comp hp).continuousAt.eventually bump.eventuallyEq_one
  filter_upwards [hnear, hbump] with y hy hby
  change bump (φ (p y)) = 1 at hby
  simp only [f, ite_eq_left hy, hby, Complex.ofReal_one]

section Bruhat

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- A compactly supported Schwartz–Bruhat local unit exists inside every
prescribed open neighborhood. -/
theorem exists_bruhatSchwartz_local_unit {x : G} {U : Set G} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ u : BruhatSchwartz G, HasCompactSupport u.val ∧ tsupport u.val ⊆ U ∧
      (u.val =ᶠ[𝓝 x] fun _ ↦ 1) ∧ (∀ y, 0 ≤ (u.val y).re ∧ (u.val y).im = 0) := by
  obtain ⟨P, y, V, hy, hV, hyV, hsub⟩ :=
    exists_structuralQuotient_neighborhood (hU.mem_nhds hx)
  obtain ⟨e⟩ := P.quotient_elementary
  let p : BruhatSchwartzStage G := ⟨P, e⟩
  let q : P.upper.val →ₜ* P.StageQuotient := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let i (u : P.StageQuotient) := (e.equiv u).toAdd
  have hi := e.equiv.toHomeomorph.isProperMap
  have hic : Continuous i := continuous_toAdd.comp e.equiv.continuous
  let W := i '' V
  have hW : IsOpen W := (isOpenMap_toAdd.comp e.equiv.toHomeomorph.isOpenMap) V hV
  obtain ⟨f, hfc, hfW, hf1, hfpos⟩ := exists_elementarySchwartz_local_unit
    (x := i (q y)) hW ⟨q y, hyV, rfl⟩
  let u := p.inclusionCLM f
  have hlocal : tsupport (p.quotientTest f) ⊆ i ⁻¹' tsupport f.val :=
    tsupport_comp_subset_preimage f.val hic
  have hlocalC : HasCompactSupport (p.quotientTest f) := by
    exact (hi.isCompact_preimage hfc).of_isClosed_subset isClosed_closure hlocal
  have hK : IsCompact (P.kernel : Set G) := by
    rw [← lcaDualAnnihilator_annihilator P.kernel P.kernel_closed]
    exact isCompact_lcaDualAnnihilator_of_isOpen _ P.annihilator_open
  have hKq : q.toMonoidHom.ker = P.kernel.comap P.upper.val.subtype :=
    QuotientGroup.ker_mk' _
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have hqP : IsProperMap q := LCAStructuralPair.proper_of_open_surjective_compact_kernel
    q hq.surjective hq.isOpenMap (by
      rw [hKq]
      exact (P.upper.val.isClosed_of_isOpen P.upper.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
  have hSup := p.realize_tsupport_subset f
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · exact ((hqP.isCompact_preimage hlocalC).image continuous_subtype_val).of_isClosed_subset
      isClosed_closure hSup
  · apply hSup.trans
    apply subset_trans (image_mono (preimage_mono _)) hsub
    intro x hx
    have h := hfW (hlocal hx)
    obtain ⟨z, hz, he⟩ := h
    have hinj : Injective i := Multiplicative.toAdd.injective.comp e.equiv.injective
    exact (hinj he) ▸ hz
  · have he : (fun v : P.upper.val ↦ f (i (q v))) =ᶠ[𝓝 y] 1 :=
      (hic.comp q.continuous).continuousAt.eventually hf1
    obtain ⟨B, hB, hBo, hyB⟩ := mem_nhds_iff.mp he
    have hB' := (P.upper.property.1.isOpenEmbedding_subtypeVal.isOpenMap B hBo).mem_nhds
      (show x ∈ (Subtype.val : P.upper.val → G) '' B from ⟨y, hyB, hy⟩)
    filter_upwards [hB'] with x' hx'
    obtain ⟨z, hz, rfl⟩ := hx'
    exact (P.realizeSchwartz_apply_of_mem e f z).trans (hB hz)
  · intro z
    change 0 ≤ (P.realizeSchwartz e f z).re ∧ (P.realizeSchwartz e f z).im = 0
    by_cases hz : z ∈ P.upper.val
    · rw [← show (⟨z, hz⟩ : P.upper.val).val = z from rfl,
        P.realizeSchwartz_apply_of_mem e f ⟨z, hz⟩]
      exact hfpos _
    · rw [P.realizeSchwartz_apply_of_not_mem e f z hz]
      simp

end Bruhat

end

end Masullo
