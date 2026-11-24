import ModulatedDecaySplitProducts
import ModulatedJumpPoisson

open Function Set Topology

namespace Masullo

noncomputable section

namespace WholeBruhatStage

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- The elementary additive model selected for the quotient. -/
abbrev CoordinateModel (p : WholeBruhatStage G) :=
  ElementaryLCAModel p.val.2.realDim p.val.2.torusDim p.val.2.latticeRank p.val.2.finiteFactor

end WholeBruhatStage

private theorem exists_continuousMulEquiv_of_factorization
    {G A B : Type*} [Group G] [Group A] [Group B]
    [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B]
    (d : G →ₜ* A) (F : G →ₜ* B) (φ : A →ₜ* B)
    (hd : Surjective d) (hF : Surjective F) (ho : IsOpenMap F)
    (hφ : ∀ g, φ (d g) = F g) (hker : ∀ g, F g = 1 ↔ d g = 1) :
    ∃ e : A ≃ₜ* B, ∀ g, e (d g) = F g := by
  have hinj : Injective φ := by
    intro a b hab
    obtain ⟨g, rfl⟩ := hd a
    obtain ⟨g', rfl⟩ := hd b
    have hfg : F g = F g' := (hφ g).symm.trans (hab.trans (hφ g'))
    have hf : F (g / g') = 1 := by rw [map_div F, hfg, div_self']
    exact div_eq_one.mp ((map_div d g g').symm.trans ((hker _).mp hf))
  have hsurj : Surjective φ := fun z => by
    obtain ⟨g, hg⟩ := hF z
    exact ⟨d g, (hφ g).trans hg⟩
  have hOpen : IsOpenMap φ := by
    intro U hU
    have he : φ '' U = F '' (d ⁻¹' U) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨g, rfl⟩ := hd a
        exact ⟨g, ha, (hφ g).symm⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨d g, hg, hφ g⟩
    rw [he]
    exact ho _ (hU.preimage d.continuous)
  let e := MulEquiv.ofBijective φ.toMonoidHom ⟨hinj, hsurj⟩
  exact ⟨⟨e, φ.continuous, e.toEquiv.continuous_symm_iff.mpr hOpen⟩, hφ⟩

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (m : G →ₜ* Multiplicative ℝ) (τ : Multiplicative ℝ →ₜ* G) (hτ : RightInverse τ m)

local notation "K" => m.toMonoidHom.ker

include hτ in
set_option maxHeartbeats 4000000 in
/-- For a stage whose only identifications come from the angular kernel,
its elementary coordinate group splits into the log and angular quotients. -/
theorem exists_splitStage_coordinateEquiv [LocallyCompactSpace K]
    (p : WholeBruhatStage K) (q : WholeBruhatStage G)
    (hq : q.val.1.kernel = p.val.1.kernel.map m.toMonoidHom.ker.subtype) :
    ∃ e : Multiplicative q.CoordinateModel ≃ₜ* (Multiplicative ℝ × Multiplicative p.CoordinateModel),
      ∀ g, e (q.coordinates g) = (m g, p.coordinates (modulatedKernelProjection m τ hτ g)) := by
  let α := modulatedKernelProjection m τ hτ
  let F : G →ₜ* (Multiplicative ℝ × Multiplicative p.CoordinateModel) :=
    m.prod (p.coordinates.comp α)
  have hker (g : G) : F g = 1 ↔ g ∈ q.val.1.kernel := by
    constructor
    · intro hg
      have hm : m g = 1 := congrArg Prod.fst hg
      have hp : p.coordinates (α g) = 1 := congrArg Prod.snd hg
      have hmem : α g ∈ p.val.1.kernel := p.coordinates_ker ▸
        (show α g ∈ p.coordinates.toMonoidHom.ker from hp)
      have hgval : (α g).val = g := by
        change g / τ (m g) = g
        rw [hm, map_one, div_one]
      rw [hq]
      exact ⟨α g, hmem, hgval⟩
    · intro hg
      rw [hq] at hg
      obtain ⟨u, hu, rfl⟩ := hg
      have hα : α u.val = u := by
        apply Subtype.ext
        change u.val / τ (m u.val) = u.val
        rw [show m u.val = 1 from u.property, map_one, div_one]
      apply Prod.ext
      · exact u.property
      · change p.coordinates (α u.val) = 1
        rw [hα]
        exact (show u ∈ p.coordinates.toMonoidHom.ker from p.coordinates_ker.symm ▸ hu)
  let s := modulatedLogSplit m τ hτ
  have hFs : (fun z : ℝ × K => F (s z)) = Prod.map Multiplicative.ofAdd p.coordinates := by
    funext z
    apply Prod.ext
    · change m (τ (Multiplicative.ofAdd z.1) * z.2.val) = Multiplicative.ofAdd z.1
      rw [map_mul, hτ, show m z.2.val = 1 from z.2.property, mul_one]
    · change p.coordinates (α (τ (Multiplicative.ofAdd z.1) * z.2.val)) = p.coordinates z.2
      exact congrArg (fun u : K => p.coordinates u) (modulatedKernelProjection_split m τ hτ z.2 z.1)
  have hF : Surjective F := by
    have hs : Surjective (fun z : ℝ × K => F (s z)) := by
      rw [hFs]
      exact Multiplicative.ofAdd.surjective.prodMap p.coordinates_surjective
    exact hs.of_comp
  have hFo : IsOpenMap F := by
    have hOfAdd : IsOpenMap (@Multiplicative.ofAdd ℝ) := isOpenMap_ofAdd
    have ho : IsOpenMap (fun z : ℝ × K => F (s z)) := by
      rw [hFs]
      exact hOfAdd.prodMap p.coordinates_isOpenMap
    have hEq : (fun g => F (s (s.symm g))) = F := funext fun g => congrArg F (s.apply_symm_apply g)
    rw [← hEq]
    exact ho.comp s.symm.isOpenMap
  let D := q.val.1.descendHom F (fun k => (hker k.val).mpr k.property)
  let φ : Multiplicative q.CoordinateModel →ₜ* (Multiplicative ℝ × Multiplicative p.CoordinateModel) :=
    D.comp q.val.2.equiv.symm
  have hφ (g : G) : φ (q.coordinates g) = F g := by
    let g' : q.val.1.upper.val := ⟨g, q.property.symm ▸ Subgroup.mem_top g⟩
    change D (q.val.2.equiv.symm (q.val.2.equiv (QuotientGroup.mk g'))) = F g
    rw [q.val.2.equiv.symm_apply_apply]
    exact q.val.1.descendHom_mk F _ g'
  refine exists_continuousMulEquiv_of_factorization q.coordinates F φ
    q.coordinates_surjective hF hFo hφ (fun g => ?_)
  exact (hker g).trans (Iff.of_eq (congrArg (fun U : Subgroup G => g ∈ U)
    q.coordinates_ker.symm))

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H] [CompactSpace H]

set_option maxHeartbeats 2500000 in
/-- A translated restriction of a decay test to a compact norm-one factor
is an angular Schwartz test in the prescribed quotient. -/
theorem exists_splitStage_angularSlice (i : H →ₜ* G)
    (hi : ∀ u, m (i u) = 1) (p : WholeBruhatStage H) (q : WholeBruhatStage G)
    (hker : p.val.1.kernel ≤ q.val.1.kernel.comap i.toMonoidHom)
    (I : Set ℝ) (b : I) (g : G) :
    ∃ L : WholeBruhatDecayStage m I q →L[ℂ] p.val.Space,
      ∀ f u, p.val.realize (L f) u = f.val (g * i u) := by
  let C := p.coordinateMap q i hker
  let c : p.CoordinateModel →+ q.CoordinateModel := C.toMonoidHom.toAdditive
  letI : CompactSpace (Multiplicative p.CoordinateModel) :=
    p.coordinates_surjective.compactSpace p.coordinates.continuous
  letI : CompactSpace p.CoordinateModel :=
    Multiplicative.toAdd.surjective.compactSpace continuous_toAdd
  have hc : Continuous c := continuous_toAdd.comp (C.continuous.comp continuous_ofAdd)
  let A : q.val.Space →L[ℂ] p.val.Space := elementarySchwartz_properPullback c hc.isProperMap
  let U (f : WholeBruhatDecayStage m I q) := WholeBruhatDecayStage.translate m I q g⁻¹ f
  let V (f : WholeBruhatDecayStage m I q) := A (WholeBruhatDecayStage.twist q b (U f))
  have hU : Continuous U := (WholeBruhatDecayStage.continuous_translate m I q).comp
    (continuous_const.prodMk continuous_id)
  have htw : Continuous (WholeBruhatDecayStage.twist q b :
      WholeBruhatDecayStage m I q → q.val.Space) :=
    (WholeBruhatDecayStage.continuous_iff id).mp continuous_id b
  have hV : Continuous V := A.continuous.comp (htw.comp hU)
  have hvalue (f : WholeBruhatDecayStage m I q) (u : H) :
      p.val.realize (V f) u = f.val (g * i u) := by
    have hc' : c (p.coordinates u).toAdd = (q.coordinates (i u)).toAdd :=
      congrArg Multiplicative.toAdd (p.coordinateMap_coordinates q i hker u)
    calc
      p.val.realize (V f) u = (V f) (p.coordinates u).toAdd := p.realize_eq_coordinates _ _
      _ = (WholeBruhatDecayStage.twist q b (U f)) (c (p.coordinates u).toAdd) := rfl
      _ = q.val.realize (WholeBruhatDecayStage.twist q b (U f)) (i u) :=
        (congrArg (fun x : q.CoordinateModel => (WholeBruhatDecayStage.twist q b (U f)) x) hc').trans
          (q.realize_eq_coordinates _ _).symm
      _ = f.val (g * i u) := by
        rw [congrFun (WholeBruhatDecayStage.realize_twist q b (U f)) (i u)]
        rw [modulatedExponentialWeight_apply, hi u, toAdd_one, mul_zero, Real.exp_zero, one_smul]
        change f.val ((g⁻¹)⁻¹ * i u) = f.val (g * i u)
        rw [inv_inv]
  let L : WholeBruhatDecayStage m I q →ₗ[ℂ] p.val.Space :=
    { toFun := V
      map_add' := fun f f' => p.val.1.realizeSchwartz_injective p.val.2 (funext fun u => by
        rw [hvalue, map_add, Pi.add_apply, hvalue, hvalue]
        rfl)
      map_smul' := fun a f => p.val.1.realizeSchwartz_injective p.val.2 (funext fun u => by
        rw [hvalue, map_smul, Pi.smul_apply, hvalue]
        rfl) }
  exact ⟨⟨L, hV⟩, hvalue⟩

end

end Masullo
