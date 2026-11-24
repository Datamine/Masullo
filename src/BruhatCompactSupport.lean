import BruhatSchwartz

open Filter Function Set Topology
open scoped ContDiff ENNReal

namespace Masullo

noncomputable section

section Elementary

variable {m n r : ℕ} {F : Type*}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

local notation "A" => ElementaryLCAModel m n r F
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

/-- The weighted partial derivatives of a smooth compactly supported function
descend through the torus cover and are bounded on the original compact set.
Adapted from mccorvie/riemann-masullo at f0d7b7e. -/
theorem elementarySchwartz_mem_of_compactSupport (f : A → ℂ) (hc : HasCompactSupport f)
    (hf : ∀ a b, ContDiff ℝ ∞ (fun u => f (elementaryCover u a b))) :
    f ∈ elementarySchwartzSubmodule m n r F := by
  classical
  refine ⟨hf, fun ⟨α, β, γ, δ⟩ => ?_⟩
  let weight (x : EuclideanSpace ℝ (Fin m)) (a : Fin r → ℤ) :=
    (∏ i, (x i : ℂ) ^ α i) * ∏ i, (a i : ℂ) ^ δ i
  let lift (y : A) := (elementaryCover_surjective y.2.2.1 y.2.2.2 y.1 y.2.1).choose
  let W (y : A) := weight y.1 y.2.2.1 * elementaryPartial f β γ (y.1, lift y) y.2.2.1 y.2.2.2
  have hW (u : X) (a : Fin r → ℤ) (b : F) :
      W (elementaryCover u a b) = weight u.1 a * elementaryPartial f β γ u a b := by
    apply congrArg (fun z : ℂ => weight u.1 a * z)
    apply (elementaryPartial_descends f β γ a b (hf a b)).2
    exact (elementaryCover_surjective a b u.1 (fun i => (u.2 i : AddCircle (1 : ℝ)))).choose_spec
  have hcont : Continuous W := by
    apply elementary_continuous_of_fibres
    intro a b
    apply Continuous.congr _ (fun u => (hW u a b).symm)
    have hw : Continuous (fun u : X => weight u.1 a) :=
      (continuous_finsetProd _ fun i _ => ((Complex.continuous_ofReal.comp
        ((PiLp.continuous_apply 2 _ i).comp continuous_fst)).pow _)).mul continuous_const
    exact hw.mul (elementaryPartial_descends f β γ a b (hf a b)).1.continuous
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn hcont.continuousOn
  apply lt_of_le_of_lt (b := (R.toNNReal : ℝ≥0∞)) _ ENNReal.coe_lt_top
  refine iSup_le fun u => iSup_le fun a => iSup_le fun b => ENNReal.coe_le_coe.mpr ?_
  change ‖weight u.1 a * elementaryPartial f β γ u a b‖₊ ≤ R.toNNReal
  rw [← hW]
  by_cases hx : elementaryCover u a b ∈ tsupport f
  · exact_mod_cast (hR _ hx).trans (Real.le_coe_toNNReal R)
  · have hcq : Continuous (fun v : X => elementaryCover v a b) :=
      elementaryCover_openQuotientMap.continuous.comp (continuous_id.prodMk (continuous_const (y := (a,b))))
    have hu : u ∉ tsupport (fun v : X => f (elementaryCover v a b)) :=
      fun h => hx (tsupport_comp_subset_preimage f hcq h)
    have h0 (j : ℕ) : iteratedFDeriv ℝ j (fun v : X => f (elementaryCover v a b)) u = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hu (tsupport_iteratedFDeriv_subset j h))
    have hz : elementaryPartial f β γ u a b = 0 := by
      rw [elementaryPartial_eq_basis, h0]
      rfl
    rw [hW, hz, mul_zero, nnnorm_zero]
    exact zero_le

end Elementary

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

set_option maxHeartbeats 800000 in
/-- A fixed structural quotient inherits all derivative orders from a
Bruhat-smooth function, even when the witnesses use different kernels. -/
theorem bruhatContDiff_fixed_stage {f : G → ℂ} (hf : f ∈ bruhatSmoothSubmodule (G := G))
    (P : BruhatSchwartzStage G)
    (φ : ElementaryLCAModel P.2.realDim P.2.torusDim P.2.latticeRank P.2.finiteFactor → ℂ)
    (hφ : ∀ x : P.1.upper.val, φ (P.1.stageCoordinates P.2 x).toAdd = f x.val) :
    ∀ a b, ContDiff ℝ ∞ (fun u => φ (elementaryCover u a b)) := by
  intro a b
  apply contDiff_infty.mpr
  intro s
  obtain ⟨Q, _, hQ⟩ := hf s
  letI := (lcaStructuralPairs_filtered (G := G)).2
  obtain ⟨U, hPU, hQU⟩ := exists_ge_ge P.1 Q
  have hpk : U.kernel ≤ P.1.kernel := hPU.2
  have hqk : U.kernel ≤ Q.kernel := hQU.2
  let R := P.1.refinementMiddle U hpk
  let S : LCAStructuralPair G :=
    ⟨U.upper, Q.kernel, Q.kernel_closed, Q.annihilator_open, Q.annihilator_compactlyGenerated,
      Q.kernel_le.trans hQU.1⟩
  obtain ⟨r⟩ := R.quotient_elementary
  obtain ⟨q⟩ := S.quotient_elementary
  obtain ⟨g, hg, hgs⟩ := hQ S rfl q
  have hu : R.upper.val ≤ S.upper.val := hPU.1
  have hRP : R.upper.val ≤ P.1.upper.val := le_rfl
  let α := R.stageCoordinateMap P.1 hRP hpk r P.2
  let β := R.stageCoordinateMap S hu hqk r q
  have hao : IsOpenMap α := P.2.equiv.toHomeomorph.isOpenMap.comp
    ((R.stageMap_isOpenMap P.1 hRP hpk).comp r.equiv.symm.toHomeomorph.isOpenMap)
  have has : Surjective α := P.2.equiv.surjective.comp
    ((R.stageMap_surjective_of_upper_eq P.1 hRP hpk rfl).comp r.equiv.symm.surjective)
  have hrs : Surjective (R.stageCoordinates r) := r.equiv.surjective.comp QuotientGroup.mk_surjective
  let α₀ := α.toMonoidHom.toAdditive
  let β₀ := β.toMonoidHom.toAdditive
  have he : φ ∘ α₀ = g ∘ β₀ := by
    funext y
    obtain ⟨x, hx⟩ := hrs (Multiplicative.ofAdd y)
    change φ (α (Multiplicative.ofAdd y)).toAdd = g (β (Multiplicative.ofAdd y)).toAdd
    have hα : α (Multiplicative.ofAdd y) = P.1.stageCoordinates P.2 (Subgroup.inclusion hRP x) :=
      (congrArg α hx.symm).trans (R.stageCoordinateMap_stageCoordinates P.1 hRP hpk r P.2 x)
    have hβ : β (Multiplicative.ofAdd y) = S.stageCoordinates q (Subgroup.inclusion hu x) :=
      (congrArg β hx.symm).trans (R.stageCoordinateMap_stageCoordinates S hu hqk r q x)
    rw [hα, hβ]
    exact (hφ (Subgroup.inclusion hRP x)).trans (hg (Subgroup.inclusion hu x)).symm
  apply elementaryContDiff_of_open α₀ α.continuous hao (g ∘ β₀) φ _ he _ a b
  · exact elementaryContDiff_hom β₀ β.continuous g hgs
  · intro y hy
    exact (hy (has (Multiplicative.ofAdd y))).elim

set_option maxHeartbeats 800000 in
/-- A compactly supported smooth function that descends to structural
coordinates has a Schwartz representative in those coordinates. -/
theorem exists_bruhatSchwartzStage_realization_of_compactSupport {f : G → ℂ}
    (hf : f ∈ bruhatSmoothSubmodule (G := G)) (hc : HasCompactSupport f)
    (P : BruhatSchwartzStage G)
    (φ : ElementaryLCAModel P.2.realDim P.2.torusDim P.2.latticeRank P.2.finiteFactor → ℂ)
    (hφ : ∀ x : P.1.upper.val, φ (P.1.stageCoordinates P.2 x).toAdd = f x.val)
    (hz : ∀ x ∉ P.1.upper.val, f x = 0) :
    ∃ z : P.Space, P.realize z = f := by
  have hp : HasCompactSupport φ := by
    let q := fun x : P.1.upper.val => (P.1.stageCoordinates P.2 x).toAdd
    have hq : Continuous q := continuous_toAdd.comp (P.1.stageCoordinates P.2).continuous
    have hs : Surjective q := Multiplicative.toAdd.surjective.comp
      (P.2.equiv.surjective.comp QuotientGroup.mk_surjective)
    have hc' := (P.1.upper.val.isClosed_of_isOpen P.1.upper.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage hc
    apply HasCompactSupport.intro (hc'.image hq)
    intro y hy
    obtain ⟨x, rfl⟩ := hs y
    exact (hφ x).trans (image_eq_zero_of_notMem_tsupport fun hx => hy ⟨x, hx, rfl⟩)
  let z : P.Space :=
    ⟨φ, elementarySchwartz_mem_of_compactSupport φ hp (bruhatContDiff_fixed_stage hf P φ hφ)⟩
  refine ⟨z, funext fun x => ?_⟩
  by_cases hx : x ∈ P.1.upper.val
  · exact (P.1.realizeSchwartz_apply_of_mem P.2 z ⟨x, hx⟩).trans (hφ ⟨x, hx⟩)
  · exact (P.1.realizeSchwartz_apply_of_not_mem P.2 z x hx).trans (hz x hx).symm

set_option maxHeartbeats 800000 in
/-- Every compactly supported Bruhat-smooth function belongs to the actual
Schwartz–Bruhat space. -/
theorem bruhatSchwartz_mem_of_smooth_compactSupport {f : G → ℂ}
    (hf : f ∈ bruhatSmoothSubmodule (G := G)) (hc : HasCompactSupport f) :
    f ∈ bruhatSchwartzSubmodule (G := G) := by
  obtain ⟨Q, _, hQ⟩ := hf 0
  obtain ⟨J, hJ⟩ := exists_openCompactlyGeneratedSubgroup_contains hc
  letI := (openCompactlyGeneratedSubgroups_colimit (G := G)).1
  obtain ⟨U, hQU, hJU⟩ := exists_ge_ge Q.upper J
  let P : LCAStructuralPair G :=
    ⟨U, Q.kernel, Q.kernel_closed, Q.annihilator_open, Q.annihilator_compactlyGenerated,
      Q.kernel_le.trans hQU⟩
  obtain ⟨p⟩ := P.quotient_elementary
  obtain ⟨φ, hφ, _⟩ := hQ P rfl p
  obtain ⟨z, hz⟩ := exists_bruhatSchwartzStage_realization_of_compactSupport hf hc ⟨P, p⟩ φ hφ
    (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hJU (hJ h)))
  exact ⟨⟨P, p⟩, z, hz⟩

end

end Masullo
