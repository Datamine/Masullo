import BruhatWholeQuotientStages
import ElementaryCyclicPeriodization
import BruhatCyclicOrbitSums
import ModulatedCyclicFourier

open Function Set Topology

namespace Masullo

noncomputable section

set_option maxHeartbeats 2200000

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
  (γ : G) (hγ : 0 < (m γ).toAdd)

local notation "Γ" => Subgroup.zpowers γ
local notation "H" => G ⧸ Γ

variable [hT : T2Space (G ⧸ Subgroup.zpowers γ)]
  [hLC : LocallyCompactSpace (G ⧸ Subgroup.zpowers γ)]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem cyclic_image_kernel {A B : Type*} [CommGroup A] [CommGroup B]
    (γ : G) (K : Subgroup G) (N : Subgroup G) (hN : N = K ⊔ Subgroup.zpowers γ)
    (a : G →* A) (b : (G ⧸ N) →* B) (ψ : A →* B)
    (ha : Surjective a) (hK : K ≤ a.ker) (hb : b.ker = a.ker.map (QuotientGroup.mk' N))
    (hψ : ∀ x, ψ (a x) = b (QuotientGroup.mk x)) :
    ∀ z, ψ z = 1 ↔ ∃ j : ℤ, (a γ) ^ j = z := by
  intro z
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := ha z
    have hx : QuotientGroup.mk x ∈ b.ker := (hψ x).symm.trans hz
    rw [hb] at hx
    obtain ⟨k, hk, hq⟩ := hx
    have hd : x / k ∈ N := QuotientGroup.eq_iff_div_mem.1 hq.symm
    rw [hN, Subgroup.mem_sup] at hd
    obtain ⟨z, hz, w, hw, heq⟩ := hd
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have he : z * γ ^ j * k = x := by rw [heq, div_mul_cancel]
    refine ⟨j, ?_⟩
    simpa only [map_mul, map_zpow, show a z = 1 from hK hz, show a k = 1 from hk,
      one_mul, mul_one] using congrArg a he
  · rintro ⟨j, rfl⟩
    have hγq : (QuotientGroup.mk γ : G ⧸ N) = 1 := by
      apply (QuotientGroup.eq_one_iff _).2
      rw [hN]
      exact (show Subgroup.zpowers γ ≤ K ⊔ Subgroup.zpowers γ from le_sup_right)
        (Subgroup.mem_zpowers γ)
    rw [map_zpow, hψ, hγq, map_one, one_zpow]

omit hT hLC in
include hm in
/-- Orbit sums of one whole-group stage descend to the compact quotient
by the period and any subgroup of the structural kernel. -/
theorem exists_bruhatCyclicPeriodization_quotient_stage (P : WholeBruhatStage G)
    (K : Subgroup G) (hK : K ≤ P.val.1.kernel)
    (N : Subgroup G) (hN : N = K ⊔ Γ) (hNc : IsClosed (N : Set G))
    [T2Space (G ⧸ N)] [LocallyCompactSpace (G ⧸ N)] [CompactSpace (G ⧸ N)] :
    ∃ Q : WholeBruhatStage (G ⧸ N),
      Q.val.1.kernel = P.val.1.kernel.map (QuotientGroup.mk' N) ∧
      ∀ f : P.val.Space, ∃ g : Q.val.Space,
      ∀ x : G, Q.val.realize g (QuotientGroup.mk x) =
        bruhatSchwartz_cyclicOrbitSum m γ hγ x (P.val.inclusion f) := by
  obtain ⟨Q, hQ⟩ := exists_wholeBruhatStage_quotient_image N hNc P
  let q : G →ₜ* G ⧸ N := ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
  have hpq : P.val.1.kernel ≤ Q.val.1.kernel.comap q.toMonoidHom := by
    intro x hx
    change q x ∈ Q.val.1.kernel
    rw [hQ]
    exact ⟨x, hx, rfl⟩
  let ψ := P.coordinateMap Q q hpq
  let X := ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank P.val.2.finiteFactor
  let Y := ElementaryLCAModel Q.val.2.realDim Q.val.2.torusDim Q.val.2.latticeRank Q.val.2.finiteFactor
  let φ : X →+ Y := ψ.toMonoidHom.toAdditive
  have hφ : Continuous φ := ψ.continuous
  have hS : Surjective φ := P.coordinateMap_surjective Q q hpq QuotientGroup.mk_surjective
  have ho : IsOpenMap φ := P.coordinateMap_isOpenMap Q q hpq QuotientGroup.isOpenMap_coe
  let s : X := (P.coordinates γ).toAdd
  have hb : Q.coordinates.toMonoidHom.ker = P.coordinates.toMonoidHom.ker.map (QuotientGroup.mk' N) := by
    rw [P.coordinates_ker, Q.coordinates_ker]
    exact hQ
  have hker (z : X) : φ z = 0 ↔ ∃ j : ℤ, j • s = z := by
    have h := cyclic_image_kernel γ K N hN P.coordinates.toMonoidHom Q.coordinates.toMonoidHom
      ψ.toMonoidHom P.coordinates_surjective (P.coordinates_ker.symm ▸ hK) hb
      (P.coordinateMap_coordinates Q q hpq)
      (Multiplicative.ofAdd z)
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := h.1 (congrArg Multiplicative.ofAdd hz)
      exact ⟨j, (toAdd_zpow _ _).symm.trans (congrArg Multiplicative.toAdd hj)⟩
    · rintro ⟨j, hj⟩
      exact congrArg Multiplicative.toAdd (h.2 ⟨j,
        (congrArg Multiplicative.ofAdd ((toAdd_zpow _ _).trans hj))⟩)
  let l := P.logCoordinate m
  have hl := (P.logCoordinate_isProperMap m hm).continuous
  have hs : 0 < l s := by simp only [l, s, P.logCoordinate_coordinates, hγ]
  have hc : IsCompact (univ : Set Y) := by
    let w (x : G ⧸ N) : Y := (Q.coordinates x).toAdd
    have hw : Surjective w := by
      intro y
      obtain ⟨x, hx⟩ := Q.coordinates_surjective (Multiplicative.ofAdd y)
      exact ⟨x, congrArg Multiplicative.toAdd hx⟩
    rw [← image_univ_of_surjective hw]
    exact isCompact_univ.image (continuous_toAdd.comp Q.coordinates.continuous)
  refine ⟨Q, hQ, fun f ↦ ?_⟩
  have hElem : ∃ g : Q.val.Space, ∀ z : X, g.val (φ z) = ∑' j : ℤ, f.val (z + j • s) := by
    exact @exists_elementaryCyclicPeriodization
      P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank
      Q.val.2.realDim Q.val.2.torusDim Q.val.2.latticeRank P.val.2.finiteFactor Q.val.2.finiteFactor
      P.val.2.finiteGroup P.val.2.finiteTopology P.val.2.finiteDiscrete (Finite.of_fintype _)
      Q.val.2.finiteGroup Q.val.2.finiteTopology Q.val.2.finiteDiscrete (Finite.of_fintype _)
      l hl s hs φ hφ ho hS hker hc f
  let g := hElem.choose
  have hg (z : X) := hElem.choose_spec z
  refine ⟨g, fun x ↦ ?_⟩
  have hco : (Q.coordinates (q x)).toAdd = φ (P.coordinates x).toAdd :=
    congrArg Multiplicative.toAdd (P.coordinateMap_coordinates Q q hpq x).symm
  have hshift (n : ℤ) : (P.coordinates x).toAdd + n • s =
      (P.coordinates (γ ^ n * x)).toAdd := by
    have hmul : P.coordinates (γ ^ n * x) = P.coordinates (γ ^ n) * P.coordinates x :=
      map_mul P.coordinates _ _
    have hpow : P.coordinates (γ ^ n) = P.coordinates γ ^ n := map_zpow P.coordinates _ _
    have hs' : (P.coordinates (γ ^ n)).toAdd = n • s :=
      (congrArg Multiplicative.toAdd hpow).trans (toAdd_zpow _ _)
    have heq : (P.coordinates (γ ^ n * x)).toAdd =
        (P.coordinates (γ ^ n)).toAdd + (P.coordinates x).toAdd := congrArg Multiplicative.toAdd hmul
    exact (add_comm _ _).trans ((congrArg (· + (P.coordinates x).toAdd) hs'.symm).trans heq.symm)
  calc
    Q.val.realize g (QuotientGroup.mk x) = g.val (Q.coordinates (q x)).toAdd :=
      Q.realize_eq_coordinates g (q x)
    _ = g.val (φ (P.coordinates x).toAdd) := congrArg g.val hco
    _ = ∑' j : ℤ, f.val ((P.coordinates x).toAdd + j • s) := hg _
    _ = ∑' j : ℤ, (P.val.inclusion f).val (γ ^ j * x) := by
      apply tsum_congr
      intro j
      exact (congrArg f.val (hshift j)).trans (P.realize_eq_coordinates f (γ ^ j * x)).symm
    _ = _ := (bruhatSchwartz_cyclicOrbitSum_apply m γ hγ x (P.val.inclusion f)).symm

include hm hT hLC in
/-- All orbit sums of tests on one whole-group stage are realized on a single
elementary stage of the actual compact cyclic quotient. -/
theorem exists_bruhatCyclicPeriodization_stage (P : WholeBruhatStage G) :
    ∃ Q : WholeBruhatStage H, ∀ f : P.val.Space, ∃ g : Q.val.Space,
      ∀ x : G, Q.val.realize g (QuotientGroup.mk x) =
        bruhatSchwartz_cyclicOrbitSum m γ hγ x (P.val.inclusion f) := by
  letI : CompactSpace H := modulatedCyclicQuotient_compact m hm γ hγ
  have hΓ : IsClosed (Γ : Set G) := by
    rw [← QuotientGroup.preimage_mk_one Γ]
    exact isClosed_singleton.preimage QuotientGroup.continuous_mk
  obtain ⟨Q, _, hQ⟩ := exists_bruhatCyclicPeriodization_quotient_stage m hm γ hγ P
    ⊥ bot_le Γ (by rw [bot_sup_eq]) hΓ
  exact ⟨Q, hQ⟩

end

end Masullo
