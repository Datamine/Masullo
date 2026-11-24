import IdelicMellinSummation
import HeckeConductorReflection

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NumberField Topology

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]
private abbrev Place := HeightOneSpectrum (𝓞 F)

/-- A compactly generated family of unitary characters has uniformly bounded
finite conductor exponents, with a common finite support. -/
theorem heckeConductorExponent_bounded_of_compactlyGenerated
    (J : Subgroup (PontryaginDual (IdeleClass F))) (hJ : IsCompactlyGeneratedGroup J) :
    ∃ b : Place F → ℕ, (Function.support b).Finite ∧
      ∀ χ : J, ∀ v : Place F, heckeConductorExponent F χ.val v ≤ b v := by
  obtain ⟨A, _, hA, hgen⟩ := hJ
  let tail := classOfTail F (∅ : Finset (Place F))
  letI : CompactSpace (SIntegralTail F (∅ : Finset (Place F)))ˣ := tailUnits_compact F ∅
  let restr (χ : J) := PontryaginDual.map tail χ.val
  have hc : Continuous restr := (PontryaginDual.map tail).continuous.comp continuous_subtype_val
  let B := restr '' A
  have hB : B.Finite := (hA.image hc).finite_of_discrete
  letI : Fintype B := hB.fintype
  have hrep (i : B) : ∃ χ : J, χ ∈ A ∧ restr χ = i.val := i.property
  choose rep hrepA hrepEq using hrep
  let a (i : B) (v : Place F) := heckeConductorExponent F (rep i).val v
  let b (v : Place F) := ∑ i : B, a i v
  have hb (i : B) (v : Place F) : a i v ≤ b v :=
    Finset.single_le_sum (f := fun i => a i v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  refine ⟨b, ?_, fun χ v => ?_⟩
  · refine (Set.finite_iUnion (fun i : B => heckeConductorExponent_finiteSupport F (rep i).val)).subset ?_
    intro v hv
    by_contra h
    apply hv
    apply Finset.sum_eq_zero
    intro i _
    by_contra hi
    exact h (mem_iUnion.mpr ⟨i, hi⟩)
  · apply (heckeConductorExponent_isLeast F χ.val v).2
    intro u hunit hdist
    have hu := (integralUnits_iff_norm F v u).2 hunit
    let w : {v : Place F // v ∉ (∅ : Finset (Place F))} := ⟨v, Finset.notMem_empty _⟩
    let s : (v.adicCompletionIntegers F)ˣ :=
      ⟨⟨u.val, hu.1⟩, ⟨u.inv, hu.2⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
    have hsu : Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom s = u := by
      exact Units.ext rfl
    let z : (SIntegralTail F (∅ : Finset (Place F)))ˣ :=
      ContinuousMulEquiv.piUnits.symm (Pi.mulSingle w s :
        ∀ j : {v : Place F // v ∉ (∅ : Finset (Place F))}, (j.val.adicCompletionIntegers F)ˣ)
    have hz : tail z = ideleClassMap F (singleFiniteIdele F v u) := by
      dsimp only [tail, z]
      rw [classOfTail_mulSingle, hsu]
    let ev : J →* Circle :=
      { toFun := fun ψ => ψ.val (tail z)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hAker : A ⊆ ev.ker := by
      intro ψ hψ
      let i : B := ⟨restr ψ, ⟨ψ, hψ, rfl⟩⟩
      have h := congrArg (fun γ : PontryaginDual (SIntegralTail F (∅ : Finset (Place F)))ˣ => γ z)
        (hrepEq i)
      change (rep i).val (tail z) = ψ.val (tail z) at h
      change ψ.val (tail z) = 1
      rw [← h, hz]
      have hlevel := finiteConductorLevels_mono F v _
        (heckeConductorExponent_isLeast F (rep i).val v).1 (hb i v)
      exact hlevel u hunit hdist
    have hAll : (⊤ : Subgroup J) ≤ ev.ker := hgen ▸ (Subgroup.closure_le _).2 hAker
    have hχ := hAll (show χ ∈ (⊤ : Subgroup J) from trivial)
    change χ.val (tail z) = 1 at hχ
    rwa [hz] at hχ

/-- A bound on the conductor exponents with finite support gives a
uniform bound on the norms of the conductor ideals. -/
theorem heckeConductorIdeal_absNorm_bounded_of_exponents
    (b : Place F → ℕ) (hb : (Function.support b).Finite) :
    ∃ B : ℕ, ∀ χ : PontryaginDual (IdeleClass F),
      (∀ v, heckeConductorExponent F χ v ≤ b v) →
      (heckeConductorIdeal F χ).absNorm ≤ B := by
  let T := hb.toFinset
  refine ⟨∏ v ∈ T, v.asIdeal.absNorm ^ b v, fun χ hχ => ?_⟩
  have hZero (v : Place F) (hv : v ∉ T) : heckeConductorExponent F χ v = 0 := by
    have h : b v = 0 := by simpa only [T, Set.Finite.mem_toFinset, Function.mem_support,
      not_not] using hv
    exact Nat.eq_zero_of_le_zero (h ▸ hχ v)
  have hProduct : heckeConductorIdeal F χ = ∏ v ∈ T, v.asIdeal ^ heckeConductorExponent F χ v := by
    rw [heckeConductorIdeal, finprod_eq_finsetProd_of_mulSupport_subset (s := T)]
    intro v hv
    by_contra h
    exact hv (by simp [hZero v h])
  rw [hProduct, map_prod]
  simp only [map_pow]
  exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun v _ =>
    Nat.pow_le_pow_right (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)) (hχ v))

local instance idelicConductorClassMeasurable : MeasurableSpace (IdeleClass F) := borel _
local instance idelicConductorClassBorel : BorelSpace (IdeleClass F) := ⟨rfl⟩
local instance idelicConductorClassLocallyCompact : LocallyCompactSpace (IdeleClass F) :=
  ideleClasses_locallyCompact
local instance idelicConductorClassT2 : T2Space (IdeleClass F) := ideleClasses_hausdorff
local instance idelicConductorClassSecondCountable : SecondCountableTopology (IdeleClass F) :=
  ideleClass_secondCountable F

/-- For a compact Bruhat test there is one conductor bound and one finite
ramification set for the entire annihilator of its chosen invariance subgroup. -/
theorem ideleClassMellin_conductor_bounded (f : BruhatCompactTest (IdeleClass F)) :
    ∃ (H : Subgroup (normOneIdeleClass F)) (B : ℕ) (S : Finset (Place F)),
      IsCompact (H : Set (normOneIdeleClass F)) ∧
      (∀ k : H, ∀ x, f.val.val (k.val.val * x) = f.val.val x) ∧
      ∀ χ : lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype),
        (heckeConductorIdeal F χ.val).absNorm ≤ B ∧
          ∀ v : Place F, v ∉ S → unramifiedFiniteCharacter F χ.val v := by
  obtain ⟨H, hH, _, hgen, hInv⟩ := ideleClassMellin_exists_compact_invariance F f
  let J := lcaAnnihilator (G := IdeleClass F) (H.map (normOneIdeleClass F).subtype)
  obtain ⟨b, hb, hBound⟩ := heckeConductorExponent_bounded_of_compactlyGenerated F J hgen
  obtain ⟨B, hB⟩ := heckeConductorIdeal_absNorm_bounded_of_exponents F b hb
  refine ⟨H, B, hb.toFinset, hH, hInv, fun χ => ?_⟩
  have hχb := hBound χ
  refine ⟨hB χ.val hχb, fun v hv => ?_⟩
  have h0 : b v = 0 := by
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hv
  exact unramifiedFiniteCharacter_of_heckeConductorExponent_eq_zero F χ.val v
    (Nat.eq_zero_of_le_zero (h0 ▸ hχb v))

end

end Masullo
