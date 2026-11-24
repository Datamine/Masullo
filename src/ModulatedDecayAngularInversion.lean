import ModulatedDecayAngularCoefficients
import ModulatedDecaySplitCoordinates
import CompactBruhatFourierSynthesis

open Function MeasureTheory Set Topology

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

variable [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
  (ν : Measure m.toMonoidHom.ker) [ν.IsHaarMeasure] [IsProbabilityMeasure ν]

include hτ in
set_option maxHeartbeats 9000000 in
/-- The Fourier coefficients in the radial decay space recover each angular
slice of a coupled test on the fixed quotient. -/
theorem hasSum_splitStage_angularFourier (hm : IsProperMap m) [LocallyCompactSpace K]
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype)
    (I : Set ℝ) (b : I) (f : WholeBruhatDecayStage m I q) (x : ℝ) (u : K) :
    HasSum (fun ω : PontryaginDual K =>
      (modulatedDecayAngularCoefficient m τ hτ ν ω I ⟨b, b.property⟩ hm
        (ModulatedExponentialInductive.stageMap q f)).val x * ((ω⁻¹) u : ℂ))
      (f.val (τ (Multiplicative.ofAdd x) * u.val)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  let i := modulatedKernelInclusion m
  have hker : p.val.1.kernel ≤ q.val.1.kernel.comap i.toMonoidHom := by
    intro k hk
    change (k : G) ∈ q.val.1.kernel
    rw [hq]
    exact ⟨k, hk, rfl⟩
  obtain ⟨L, hL⟩ := exists_splitStage_angularSlice m i (fun k => k.property) p q hker I b
    (τ (Multiplicative.ofAdd x))
  let F := p.val.inclusion (L f)
  let eval : BruhatSchwartz K →L[ℂ] ℂ :=
    ⟨(LinearMap.proj u).comp (bruhatSchwartzSubmodule (G := K)).subtype,
      bruhatSchwartz_continuous_eval u⟩
  have he : eval F = f.val (τ (Multiplicative.ofAdd x) * u.val) := hL f u
  rw [← he]
  apply ((hasSum_compactBruhatFourierSeries ν F).mapL eval).congr_fun
  intro ω
  have hcoef : compactBruhatFourierCoeff ν ω F =
      (modulatedDecayAngularCoefficient m τ hτ ν ω I ⟨b, b.property⟩ hm
        (ModulatedExponentialInductive.stageMap q f)).val x := by
    have hν : (ν.real univ : ℂ)⁻¹ = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one, Complex.ofReal_one, inv_one]
    rw [compactBruhatFourierCoeff_apply, hν, one_mul]
    refine Eq.trans ?_ (modulatedDecayAngularCoefficient_apply m τ hτ ν ω I
      ⟨b, b.property⟩ hm (ModulatedExponentialInductive.stageMap q f) x).symm
    exact integral_congr_ae (.of_forall fun u => congrArg (fun z : ℂ => z * (ω u : ℂ)) (hL f u))

  rw [map_smul, hcoef]
  rfl

set_option maxHeartbeats 2500000 in
private theorem decayStage_val_mul_kernel
    (q : WholeBruhatStage G) (I : Set ℝ) (b : I) (f : WholeBruhatDecayStage m I q)
    (k g : G) (hk : k ∈ q.val.1.kernel) : f.val (k * g) = f.val g := by
  have hk' : q.coordinates k = 1 := show k ∈ q.coordinates.toMonoidHom.ker from
    q.coordinates_ker.symm ▸ hk
  have hkg : q.coordinates (k * g) = q.coordinates g := by
    rw [map_mul q.coordinates, hk', one_mul]
  let v := WholeBruhatDecayStage.twist q b f
  have hEq : q.val.realize v (k * g) = q.val.realize v g := calc
    _ = v (q.coordinates (k * g)).toAdd := q.realize_eq_coordinates v _
    _ = v (q.coordinates g).toAdd := congrArg (fun t => v t.toAdd) hkg
    _ = _ := (q.realize_eq_coordinates v g).symm
  change q.val.realize (WholeBruhatDecayStage.twist q b f) (k * g) = _ at hEq
  rw [congrFun (WholeBruhatDecayStage.realize_twist q b f) (k * g),
    congrFun (WholeBruhatDecayStage.realize_twist q b f) g] at hEq
  have hm : m k = 1 := q.val.1.modulation_eq_one_on_kernel m ⟨k,hk⟩
  rw [modulatedExponentialWeight_apply, modulatedExponentialWeight_apply,
    map_mul m, hm, one_mul, Complex.real_smul, Complex.real_smul] at hEq
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hEq

include hτ in
set_option maxHeartbeats 9000000 in
/-- In a fixed stage the pointwise reconstruction uses only the elementary
characters of the angular quotient. -/
theorem hasSum_splitStage_elementaryAngularFourier (hm : IsProperMap m) [LocallyCompactSpace K]
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype)
    (I : Set ℝ) (b : I) (f : WholeBruhatDecayStage m I q) (x : ℝ) (u : K) :
    HasSum (fun θ : PontryaginDual (Multiplicative p.CoordinateModel) =>
      (modulatedDecayAngularCoefficient m τ hτ ν (θ.comp p.coordinates) I ⟨b, b.property⟩ hm
        (ModulatedExponentialInductive.stageMap q f)).val x * ((θ⁻¹) (p.coordinates u) : ℂ))
      (f.val (τ (Multiplicative.ofAdd x) * u.val)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.isCompact_preimage (isCompact_singleton (x := (1 : Multiplicative ℝ))))
  let t (θ : PontryaginDual (Multiplicative p.CoordinateModel)) : PontryaginDual K :=
    θ.comp p.coordinates
  have ht : Injective t := by
    intro θ η he
    ext z
    obtain ⟨k, rfl⟩ := p.coordinates_surjective z
    exact congrArg (fun χ : PontryaginDual K => (χ k : ℂ)) he
  let c (ω : PontryaginDual K) := modulatedDecayAngularCoefficient m τ hτ ν ω I
    ⟨b, b.property⟩ hm (ModulatedExponentialInductive.stageMap q f)
  have hzero (ω : PontryaginDual K) (hω : ω ∉ range t) : (c ω).val x * ((ω⁻¹) u : ℂ) = 0 := by
    have h : ∃ a ∈ p.val.1.kernel, ω a ≠ 1 := by
      by_contra! hh
      obtain ⟨θ, hθ, _⟩ := wholeBruhatStage_character_descends p ω hh
      exact hω ⟨θ, hθ⟩
    obtain ⟨a, ha, haω⟩ := h
    have hker : a.val ∈ q.val.1.kernel := hq.symm ▸ ⟨a, ha, rfl⟩
    let F (k : K) := f.val (τ (Multiplicative.ofAdd x) * k.val)
    have hInv (k : K) : F (a * k) = F k := by
      change f.val (τ (Multiplicative.ofAdd x) * (a.val * k.val)) = F k
      rw [← mul_left_comm a.val]
      exact decayStage_val_mul_kernel m q I b f a.val _ hker
    have hz : (c ω).val x = 0 :=
      (modulatedDecayAngularCoefficient_apply m τ hτ ν ω I ⟨b,b.property⟩ hm
        (ModulatedExponentialInductive.stageMap q f) x).trans
        (integral_character_eq_zero_of_invariant ν ω F a hInv haω)
    rw [hz, zero_mul]
  exact (ht.hasSum_iff hzero).mpr (hasSum_splitStage_angularFourier m τ hτ ν hm p q hq I b f x u)

end

end Masullo
