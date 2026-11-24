import IdelicDoubling
import SUnitLogFullLattice
import SLocalFundamentalDomain

open Function IsDedekindDomain Module NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem Set Topology
open scoped Classical NumberField Pointwise

namespace Masullo

noncomputable section

section

variable {V I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]

/-- A half-open lattice parallelotope centered at zero in basis coordinates. -/
def centeredLogCell (b : Basis I ℝ V) : Set V :=
  {x | ∀ i, b.repr x i ∈ Ico (-(1 / 2 : ℝ)) (1 / 2)}

private theorem centered_eq_shifted (b : Basis I ℝ V) (x : V) :
    x ∈ centeredLogCell b ↔
      x + b.equivFun.symm (fun _ => (1 / 2 : ℝ)) ∈ ZSpan.fundamentalDomain b := by
  rw [ZSpan.mem_fundamentalDomain]
  change (∀ i, b.repr x i ∈ Ico _ _) ↔ _
  have hs (i : I) : b.repr (b.equivFun.symm (fun _ => (1 / 2 : ℝ))) i = (1 / 2 : ℝ) :=
    congrFun (b.equivFun.apply_symm_apply _) i
  simp only [map_add, Finsupp.add_apply, hs]
  exact forall_congr' fun i => ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
    fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩

theorem centeredLogCell_unique (b : Basis I ℝ V) (x : V) :
    ∃! v : Submodule.span ℤ (range b), v.val + x ∈ centeredLogCell b := by
  let z := b.equivFun.symm (fun _ => (1 / 2 : ℝ))
  obtain ⟨w, hw, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (x + z)
  refine ⟨w, (centered_eq_shifted b _).mpr ?_, fun v hv => huniq v ?_⟩
  · change w.val + (x + z) ∈ ZSpan.fundamentalDomain b at hw
    change (w.val + x) + z ∈ ZSpan.fundamentalDomain b
    rwa [add_assoc]
  · have hh := (centered_eq_shifted b _).mp hv
    change (v.val + x) + z ∈ ZSpan.fundamentalDomain b at hh
    change v.val + (x + z) ∈ ZSpan.fundamentalDomain b
    rwa [← add_assoc]

variable {U G : Type*} [CommGroup U] [CommGroup G]

/-- Translate once by log-lattice units and then uniquely by a torsion unit. -/
theorem centeredLogPhase_unique (b : Basis I ℝ V) (A : U →* G)
    (L : G →* Multiplicative V) (P : G →* Circle) (n : ℕ) [NeZero n]
    (liftPhase : rootsOfUnity n Circle → U)
    (hlog : ∀ u : U, (L (A u)).toAdd ∈ Submodule.span ℤ (range b))
    (hsurj : ∀ z : Submodule.span ℤ (range b), ∃ u : U, (L (A u)).toAdd = z.val)
    (hker : ∀ u : U, (L (A u)).toAdd = 0 ↔ ∃ r, liftPhase r = u)
    (hphase : ∀ r, P (A (liftPhase r)) = (r.val : Circle)) (a : G) :
    ∃! u : U, (L (A u * a)).toAdd ∈ centeredLogCell b ∧
      P (A u * a) ∈ centeredPhaseHalfOpen (Real.pi / n) := by
  let x := (L a).toAdd
  let l := L.comp A
  obtain ⟨v, hv, huniq⟩ := centeredLogCell_unique b x
  obtain ⟨u₀, hu₀⟩ := hsurj v
  let y := A u₀ * a
  have hl : (L y).toAdd ∈ centeredLogCell b := by
    change (L (A u₀ * a)).toAdd ∈ _
    rw [map_mul]
    change (L (A u₀)).toAdd + x ∈ _
    rw [hu₀]
    exact hv
  obtain ⟨s, hs, hsuniq⟩ := centeredPhaseHalfOpen_unique_rotation n (P y)
  have hsl := (hker (liftPhase s)).mpr ⟨s, rfl⟩
  refine ⟨liftPhase s * u₀, ?_, ?_⟩
  · change (L (A (liftPhase s * u₀) * a)).toAdd ∈ centeredLogCell b ∧
      P (A (liftPhase s * u₀) * a) ∈ centeredPhaseHalfOpen (Real.pi / n)
    rw [map_mul A, mul_assoc]
    constructor
    · rw [map_mul L]
      change (L (A (liftPhase s))).toAdd + (L y).toAdd ∈ _
      rw [hsl, zero_add]
      exact hl
    · rw [map_mul P, hphase]
      exact hs
  · rintro u ⟨hu, hpu⟩
    have eq : (l u).toAdd = v.val := by
      let w : Submodule.span ℤ (range b) := ⟨(l u).toAdd, hlog u⟩
      have hw : w.val + x ∈ centeredLogCell b := by
        rw [map_mul L] at hu
        exact hu
      exact congrArg Subtype.val (huniq w hw)
    have hzero : (l (u / u₀)).toAdd = 0 := by
      rw [map_div]
      change (l u).toAdd - (l u₀).toAdd = 0
      rw [eq]
      change v.val - (L (A u₀)).toAdd = 0
      rw [hu₀, sub_self]
    obtain ⟨t, ht⟩ := (hker (u / u₀)).mp hzero
    have htu : liftPhase t * u₀ = u := by rw [ht, div_mul_cancel]
    have htPhase : (t.val : Circle) * P y ∈ centeredPhaseHalfOpen (Real.pi / n) := by
      rw [← hphase, ← map_mul P, ← mul_assoc, ← map_mul A, htu]
      exact hpu
    rw [← hsuniq t htPhase, htu]

end


variable (F : Type*) [Field F] [NumberField F]

theorem archBalancedCell_uniq (v : InfinitePlace F) (a : archNormOne F) :
    ∃! u : (𝓞 F)ˣ, globalUnitArch F u * a ∈ archBalancedCell F v := by
  let b := regulatorBasis F
  let e := torsionPhaseEquiv F v
  let lift (r : rootsOfUnity (torsionOrder F) Circle) : (𝓞 F)ˣ := (e.symm r).val
  have hlog (u : (𝓞 F)ˣ) : (archRegulatorLog F (globalUnitArch F u)).toAdd ∈
      Submodule.span ℤ (range b) := by
    rw [show b = regulatorBasis F from rfl, regulatorBasis_span, archRegulatorLog_globalUnit]
    exact Submodule.mem_map.mpr ⟨Additive.ofMul u, Submodule.mem_top, rfl⟩
  have hsurj (x : Submodule.span ℤ (range b)) :
      ∃ u : (𝓞 F)ˣ, (archRegulatorLog F (globalUnitArch F u)).toAdd = x.val := by
    have hx : x.val ∈ unitLattice F := regulatorBasis_span F ▸ x.property
    obtain ⟨u, _, h⟩ := Submodule.mem_map.mp hx
    exact ⟨u.toMul, by rw [archRegulatorLog_globalUnit]; exact h⟩
  have hker (u : (𝓞 F)ˣ) :
      (archRegulatorLog F (globalUnitArch F u)).toAdd = 0 ↔ ∃ r, lift r = u := by
    rw [archRegulatorLog_globalUnit]
    change logEmbedding F (Additive.ofMul u) = 0 ↔ _
    rw [logEmbedding_eq_zero_iff]
    exact ⟨fun hu => ⟨e ⟨u, hu⟩, congrArg Subtype.val (e.symm_apply_apply ⟨u, hu⟩)⟩,
      fun ⟨r, hr⟩ => hr ▸ (e.symm r).property⟩
  have hphase (r : rootsOfUnity (torsionOrder F) Circle) :
      normOnePhase F v (globalUnitArch F (lift r)) = (r.val : Circle) := by
    change infiniteIdelePhase F v (globalUnitArch F (e.symm r).val).val = _
    rw [← torsionPhaseEquiv_apply]
    exact congrArg (fun q : rootsOfUnity (torsionOrder F) Circle => (q.val : Circle)) (e.apply_symm_apply r)
  have h := centeredLogPhase_unique b (globalUnitArch F) (archRegulatorLog F)
    (normOnePhase F v) (torsionOrder F) lift hlog hsurj hker hphase a
  apply (existsUnique_congr (fun u => ?_)).mp h
  constructor
  · rintro ⟨hl, hp⟩
    exact ⟨mem_iInter.mpr hl, hp⟩
  · rintro ⟨hl, hp⟩
    exact ⟨mem_iInter.mp hl, hp⟩

/-- The global norm-one fundamental domain built from the balanced cell. -/
def ideleBalancedDomain (v : InfinitePlace F) (g : ClassGroup (𝓞 F) → NormOneIdeles F) :
    Set (NormOneIdeles F) :=
  ideleDomainFromArchCell F (archBalancedCell F v) g

theorem ideleBalancedDomain_unique (v : InfinitePlace F)
    (g : ClassGroup (𝓞 F) → NormOneIdeles F) (hg : ∀ c, normOneIdealClass F (g c) = c)
    (a : NormOneIdeles F) :
    ∃! t : Fˣ, principalNormOne F t * a ∈ ideleBalancedDomain F v g :=
  ideleDomainFromArchCell_unique F _ (archBalancedCell_uniq F v) g hg a

private abbrev Place := HeightOneSpectrum (𝓞 F)

private def sLocalArch (S : Finset (Place F)) : (SAdeles F S)ˣ →* InfiniteIdeles F :=
  (MonoidHom.fst _ _).comp MulEquiv.prodUnits.toMonoidHom

private theorem sLocalArch_principal (S : Finset (Place F)) (u : (sIntegerRing F S)ˣ) :
    sLocalArch F S (sPrincipalLocalNormOne F S u).val = fieldToArch F (sUnitToField F S u) :=
  Units.ext (sPrincipalLocalNormOne_arch F S u)

private def sLocalReducedLog (S : Finset (Place F)) :
    SLocalNormOne F S →* Multiplicative (ReducedSLogIndex F S → ℝ) where
  toFun a := Multiplicative.ofAdd (fun i =>
    sLogVector F S (sLocalEmbed F S a.val).val (reducedLogIndexEmbed F S i))
  map_one' := by
    change Multiplicative.ofAdd (fun i => sLogVector F S (sLocalEmbed F S (1 : (SAdeles F S)ˣ)).val
      (reducedLogIndexEmbed F S i)) = 1
    rw [show (sLocalEmbed F S (1 : (SAdeles F S)ˣ)).val = 1 from congrArg Subtype.val (map_one _)]
    have h : sLogVector F S (1 : Idele F) = 0 := by
      funext i
      cases i with
      | inl v => change (v.mult : ℝ) * Real.log ‖(1 : v.Completion)‖ = 0; simp
      | inr v => change Real.log ‖(1 : v.val.adicCompletion F)‖ = 0; simp
    rw [h]
    rfl
  map_mul' a b := by
    change Multiplicative.ofAdd (fun i => sLogVector F S
      (sLocalEmbed F S (a.val * b.val)).val _) = _
    rw [map_mul (sLocalEmbed F S)]
    change Multiplicative.ofAdd (fun i => sLogVector F S
      ((sLocalEmbed F S a.val).val * (sLocalEmbed F S b.val).val) _) = _
    rw [sLogVector_mul]
    rfl

private theorem sLocalReducedLog_principal (S : Finset (Place F)) (u : (sIntegerRing F S)ˣ) :
    (sLocalReducedLog F S (sPrincipalLocalNormOne F S u)).toAdd =
      sUnitReducedLog F S (Additive.ofMul u) := by
  funext i
  cases i with
  | inl i =>
    change (i.val.mult : ℝ) * Real.log ‖(sLocalEmbed F S (sPrincipalLocalNormOne F S u).val).val.val.1 i.val‖ =
      (i.val.mult : ℝ) * Real.log ‖(principalIdele F (sUnitToField F S u)).val.1 i.val‖
    rw [sLocalEmbed_arch, sPrincipalLocalNormOne_arch]
  | inr i =>
    change Real.log ‖(sLocalEmbed F S (sPrincipalLocalNormOne F S u).val).val.val.2 i.val‖ =
      Real.log ‖(principalIdele F (sUnitToField F S u)).val.2 i.val‖
    rw [sLocalEmbed_finite F S _ i, sPrincipalLocalNormOne_finite F S _ i]

private def sLocalNormOnePhase (S : Finset (Place F)) (v : InfinitePlace F) :
    SLocalNormOne F S →* Circle :=
  (infiniteIdelePhase F v).comp ((sLocalArch F S).comp (sLocalIdeleNorm F S).ker.subtype)

instance (S : Finset (Place F)) : IsZLattice ℝ (LinearMap.range (sUnitReducedLog F S)) :=
  sUnitReducedLog_isZLattice F S

private def sLocalRealLogBasis (S : Finset (Place F)) :=
  (Module.Free.chooseBasis ℤ (LinearMap.range (sUnitReducedLog F S))).ofZLatticeBasis ℝ _

/-- The centered log cell, in the pure S-local norm-one group. -/
def sLocalBalancedCell (S : Finset (Place F)) (v : InfinitePlace F) : Set (SLocalNormOne F S) :=
  {a | (sLocalReducedLog F S a).toAdd ∈ centeredLogCell (sLocalRealLogBasis F S) ∧
    sLocalNormOnePhase F S v a ∈ centeredPhaseHalfOpen (archBalancedAngleRadius F)}

theorem sLocalBalancedCell_unique (S : Finset (Place F)) (v : InfinitePlace F)
    (a : SLocalNormOne F S) :
    ∃! u : (sIntegerRing F S)ˣ, sPrincipalLocalNormOne F S u * a ∈ sLocalBalancedCell F S v := by
  let b := sLocalRealLogBasis F S
  let e := torsionPhaseEquiv F v
  let lift (r : rootsOfUnity (torsionOrder F) Circle) := integralUnitToS F S (e.symm r).val
  have hb : Submodule.span ℤ (range b) = LinearMap.range (sUnitReducedLog F S) :=
    Module.Basis.ofZLatticeBasis_span _ _ _
  have hlog (u : (sIntegerRing F S)ˣ) :
      (sLocalReducedLog F S (sPrincipalLocalNormOne F S u)).toAdd ∈ Submodule.span ℤ (range b) := by
    rw [hb, sLocalReducedLog_principal]
    exact LinearMap.mem_range_self _ _
  have hsurj (x : Submodule.span ℤ (range b)) :
      ∃ u : (sIntegerRing F S)ˣ, (sLocalReducedLog F S (sPrincipalLocalNormOne F S u)).toAdd = x.val := by
    have hmem (y : ReducedSLogIndex F S → ℝ) (hy : y ∈ Submodule.span ℤ (range b)) :
        y ∈ LinearMap.range (sUnitReducedLog F S) := by
      rwa [hb] at hy
    obtain ⟨u, hu⟩ := hmem x.val x.property
    exact ⟨u.toMul, by rw [sLocalReducedLog_principal]; exact hu⟩
  have hker (u : (sIntegerRing F S)ˣ) :
      (sLocalReducedLog F S (sPrincipalLocalNormOne F S u)).toAdd = 0 ↔ ∃ r, lift r = u := by
    rw [sLocalReducedLog_principal, sUnitReducedLog_zero_iff]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨e t, congrArg (fun w : torsion F => integralUnitToS F S w.val) (e.symm_apply_apply t)⟩
    · rintro ⟨r, rfl⟩
      exact ⟨e.symm r, rfl⟩
  have hphase (r : rootsOfUnity (torsionOrder F) Circle) :
      sLocalNormOnePhase F S v (sPrincipalLocalNormOne F S (lift r)) = (r.val : Circle) := by
    change infiniteIdelePhase F v (sLocalArch F S (sPrincipalLocalNormOne F S (lift r)).val) = _
    rw [sLocalArch_principal]
    change infiniteIdelePhase F v (globalUnitArch F (e.symm r).val).val = _
    rw [← torsionPhaseEquiv_apply]
    exact congrArg (fun z : rootsOfUnity (torsionOrder F) Circle => (z.val : Circle)) (e.apply_symm_apply r)
  exact centeredLogPhase_unique b (sPrincipalLocalNormOne F S) (sLocalReducedLog F S)
    (sLocalNormOnePhase F S v) (torsionOrder F) lift hlog hsurj hker hphase a

/-- The same centered cell times the entire integral tail gives the
balanced domain in the extended S-block. -/
def sBlockBalancedCell (S : Finset (Place F)) (v : InfinitePlace F) :
    Set (sBlockInNormOne F S) :=
  (sNormOneBlockProduct F S) ⁻¹' (sLocalBalancedCell F S v ×ˢ Set.univ)

theorem sBlockBalancedCell_unique (S : Finset (Place F)) (v : InfinitePlace F)
    (a : sBlockInNormOne F S) :
    ∃! u : (sIntegerRing F S)ˣ, sPrincipalInBlock F S u * a ∈ sBlockBalancedCell F S v := by
  have h := sLocalBalancedCell_unique F S v ((sNormOneBlockProduct F S a).1)
  apply (existsUnique_congr (fun u => ?_)).mp h
  change (sPrincipalLocalNormOne F S u * (sNormOneBlockProduct F S a).1 ∈ sLocalBalancedCell F S v) ↔
    (sNormOneBlockProduct F S (sPrincipalInBlock F S u * a) ∈
      sLocalBalancedCell F S v ×ˢ (Set.univ : Set (SIntegralTail F S)ˣ))
  rw [map_mul]
  exact ⟨fun hp => ⟨hp, mem_univ _⟩, fun hp => hp.1⟩


end

end Masullo
