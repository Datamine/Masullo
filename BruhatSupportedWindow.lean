import BruhatCyclicFactorization
import StrictQuotientStages

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 8

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ)

local notation "E" => ModulatedExponentialInductive m univ

/-- The actual supported invariant tests in the entire-decay space. -/
def bruhatSupportedInvariant (K : Subgroup G) (C : Set G) : Submodule ℂ E where
  carrier := {f | support f.val ⊆ C ∧ ∀ (k : K) x, f.val (k.val⁻¹ * x) = f.val x}
  zero_mem' := by simp
  add_mem' {f g} hf hg := by
    refine ⟨(support_add f.val g.val).trans (union_subset hf.1 hg.1), fun k x ↦ ?_⟩
    change f.val (k.val⁻¹ * x) + g.val (k.val⁻¹ * x) = f.val x + g.val x
    rw [hf.2, hg.2]
  smul_mem' c f hf := by
    constructor
    · intro x hx
      by_contra hn
      exact hx (show c • f.val x = 0 by rw [notMem_support.mp (fun h ↦ hn (hf.1 h)), smul_zero])
    · intro k x
      change c • f.val (k.val⁻¹ * x) = c • f.val x
      rw [hf.2]

section Stage

variable (P : WholeBruhatStage G) (C : Set G)

private theorem supportedInvariant_realizes (f : BruhatSchwartz G)
    (hf : HasCompactSupport f.val)
    (hK : ∀ (k : P.val.1.kernel) x, f.val (k.val⁻¹ * x) = f.val x) :
    ∃ u : P.val.Space, P.val.realize u = f.val := by
  obtain ⟨s, hs⟩ := P.coordinates_surjective.hasRightInverse
  let φ := fun z ↦ f.val (s (Multiplicative.ofAdd z))
  have hφ (x : G) : φ (P.coordinates x).toAdd = f.val x := by
    let k := s (P.coordinates x) / x
    have hk : k ∈ P.val.1.kernel := by
      rw [← P.coordinates_ker]
      change P.coordinates.toMonoidHom (s (P.coordinates x) / x) = 1
      rw [map_div]
      exact (congrArg (· / P.coordinates x) (hs (P.coordinates x))).trans (div_self' _)
    have hh := hK ((⟨k, hk⟩ : P.val.1.kernel)⁻¹) x
    rw [Subgroup.coe_inv, inv_inv] at hh
    change f.val (s (P.coordinates x)) = _
    exact (congrArg f.val (div_mul_cancel _ _)).symm.trans hh
  exact exists_bruhatSchwartzStage_realization_of_compactSupport
    (bruhatSchwartz_le_smooth f.property) hf P.val φ
    (fun x ↦ by change φ (P.coordinates x.val).toAdd = f.val x.val; exact hφ x.val)
    (fun x hx ↦ (hx (P.property.symm ▸ Subgroup.mem_top x)).elim)

/-- Supported invariant tests have the intrinsic topology of their fixed
structural stage. The equivalence realizes the elementary function on G. -/
theorem bruhatSupportedInvariant_stageEquiv [SecondCountableTopology G]
    (hm : IsProperMap m) (hms : Surjective m) (hC : IsCompact C) :
    ∃ e : P.val.compactTests C ≃L[ℂ] bruhatSupportedInvariant m P.val.1.kernel C,
      ∀ u, (e u).val.val = P.val.realize u.val := by
  let i : BruhatCompactTestIndex G := ⟨P.val, ⟨C, hC⟩⟩
  let L := bruhatCompactTest_toModulatedExponentialInductive m univ
  let j : P.val.compactTests C →L[ℂ] E :=
    (⟨L, bruhatCompactTest_continuous_inductiveDecay m univ hm hms⟩ :
      BruhatCompactTest G →L[ℂ] E).comp i.inclusionCLM
  have hj (u : P.val.compactTests C) : (j u).val = P.val.realize u.val := rfl
  let V := bruhatSupportedInvariant m P.val.1.kernel C
  have hV (u : P.val.compactTests C) : j u ∈ V := by
    refine ⟨fun x hx ↦ ?_, fun k x ↦ ?_⟩
    · by_contra hx'
      rw [hj u] at hx
      exact hx (u.property x hx')
    · have hk : k.val ∈ P.coordinates.toMonoidHom.ker := by
        rw [P.coordinates_ker]
        exact k.property
      have hc : P.coordinates (k.val⁻¹ * x) = P.coordinates x := by
        change P.coordinates.toMonoidHom (k.val⁻¹ * x) = P.coordinates.toMonoidHom x
        rw [map_mul, map_inv, show P.coordinates.toMonoidHom k.val = 1 from hk,
          inv_one, one_mul]
      calc
        (j u).val (k.val⁻¹ * x) = u.val.val (P.coordinates (k.val⁻¹ * x)).toAdd :=
          (congrFun (hj u) _).trans (P.realize_eq_coordinates u.val _)
        _ = u.val.val (P.coordinates x).toAdd := congrArg (fun z ↦ u.val.val z.toAdd) hc
        _ = (j u).val x := ((congrFun (hj u) x).trans (P.realize_eq_coordinates u.val x)).symm
  let A := j.codRestrict V hV
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  have hcomp : (J ∘ j : P.val.compactTests C → BruhatSchwartz G) =
      P.val.inclusionCLM ∘ Subtype.val := by
    funext u
    exact Subtype.ext (hj u)
  have hemb : IsEmbedding j := IsEmbedding.of_comp j.continuous J.continuous
    (hcomp.symm ▸
      ((bruhatSchwartz_strict (G := G)).2.1 P.val).comp IsEmbedding.subtypeVal)
  have hA : IsEmbedding A := (IsEmbedding.of_comp_iff (g := Subtype.val) IsEmbedding.subtypeVal).mp hemb
  have hs : Surjective A := by
    intro f
    let F : BruhatSchwartz G := J f.val
    have hF : F.val = f.val.val := rfl
    have hprop : support f.val.val ⊆ C ∧
        ∀ (k : P.val.1.kernel) x, f.val.val (k.val⁻¹ * x) = f.val.val x := f.property
    have hf : HasCompactSupport F.val := by
      rw [hF]
      exact HasCompactSupport.intro hC fun x hx ↦ notMem_support.mp (fun hx' ↦ hx (hprop.1 hx'))
    have hInv (k : P.val.1.kernel) (x : G) : F.val (k.val⁻¹ * x) = F.val x := by
      rw [hF]
      exact hprop.2 k x
    have hExists : ∃ u : P.val.Space, P.val.realize u = F.val :=
      supportedInvariant_realizes P F hf hInv
    obtain ⟨u, hu⟩ := hExists
    have hreal := hu.trans hF
    refine ⟨⟨u, fun x hx ↦ ?_⟩, ?_⟩
    · rw [hreal]
      exact notMem_support.mp (fun h ↦ hx (hprop.1 h))
    · exact Subtype.ext (Subtype.ext ((hj _).trans hreal))
  let e := LinearEquiv.ofBijective A.toLinearMap ⟨hA.injective, hs⟩
  let H : P.val.compactTests C ≃ₜ V :=
    { toEquiv := e.toEquiv
      continuous_toFun := A.continuous
      continuous_invFun := hA.isInducing.continuous_iff.mpr (by
        change Continuous (A ∘ e.symm)
        rw [show A ∘ e.symm = id from funext e.apply_symm_apply]
        exact continuous_id) }
  exact ⟨⟨e, H.continuous, H.symm.continuous⟩, hj⟩

end Stage

/-- A compact subgroup with compactly generated annihilator determines a
whole-group structural stage of a properly modulated group. -/
theorem exists_wholeBruhatStage_kernel (hm : IsProperMap m) (hms : Surjective m)
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hgen : IsCompactlyGeneratedGroup (lcaAnnihilator K)) :
    ∃ P : WholeBruhatStage G, P.val.1.kernel = K := by
  obtain ⟨J, hJ⟩ := exists_modulatedBruhat_upper_eq_top m hm hms
  let S : LCAStructuralPair G :=
    ⟨J, K, hK.isClosed, isOpen_lcaAnnihilator K hK, hgen, hJ ▸ le_top⟩
  obtain ⟨p⟩ := S.quotient_elementary
  exact ⟨⟨⟨S, p⟩, hJ⟩, rfl⟩

/-- The stage of tests supported in a fixed set is Fréchet. -/
theorem BruhatSchwartzStage.compactTests_isFrechet (p : BruhatSchwartzStage G)
    (C : Set G) : IsFrechetTVS (p.compactTests C) := by
  obtain ⟨_, hpoly, hmetric, hcomplete⟩ := @elementarySchwartz_isFrechet
    p.2.realDim p.2.torusDim p.2.latticeRank p.2.finiteFactor
    p.2.finiteGroup p.2.finiteTopology p.2.finiteDiscrete (Finite.of_fintype _)
  have h : IsFrechetTVS p.Space := by
    refine ⟨inferInstance, hpoly, hmetric, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact hcomplete
  exact isFrechetTVS_closedSubmodule h (p.compactTests C) (p.isClosed_compactTests C)

/-- A whole-group stage with trivial kernel realizes the full Schwartz–Bruhat
space of a compact group, with its intrinsic topology. -/
theorem WholeBruhatStage.exists_equiv_schwartz_of_compact_bottom
    [CompactSpace G] [SecondCountableTopology G] (P : WholeBruhatStage G)
    (hP : P.val.1.kernel = ⊥) :
    ∃ e : P.val.Space ≃L[ℂ] BruhatSchwartz G, ∀ u, (e u).val = P.val.realize u := by
  have hs : Surjective P.val.inclusionCLM := by
    intro f
    have hi (k : P.val.1.kernel) (x : G) : f.val (k.val⁻¹ * x) = f.val x := by
      have hk : k.val = 1 := Subgroup.mem_bot.mp (hP ▸ k.property)
      rw [hk, inv_one, one_mul]
    obtain ⟨u, hu⟩ := supportedInvariant_realizes P f (HasCompactSupport.of_compactSpace _) hi
    exact ⟨u, Subtype.ext hu⟩
  have hEmb := (bruhatSchwartz_strict (G := G)).2.1 P.val
  let e := LinearEquiv.ofBijective P.val.inclusion ⟨hEmb.injective, hs⟩
  have hi : Continuous e.symm := hEmb.isInducing.continuous_iff.mpr (by
    change Continuous (e ∘ e.symm)
    rw [show e ∘ e.symm = id from funext e.apply_symm_apply]
    exact continuous_id)
  exact ⟨⟨e, P.val.inclusionCLM.continuous, hi⟩, fun _ ↦ rfl⟩

end

end Masullo
