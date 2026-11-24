/-
The divisible-group retraction argument is adapted from the Apache-2.0
RiemannMasullo project, f0d7b7e0651744766be9d44e80d6e277c732a332,
AppD_SchwartzBruhat/Sec2a.lean. See External/RiemannMasullo.LICENSE.
-/
import ModulatedCharacters
import PontryaginAnnihilators
import PontryaginDuality
import Mathlib.Algebra.Category.Grp.Injective

open Filter Function Set Topology

namespace Masullo

noncomputable section

private def realSlope : PontryaginDual (Multiplicative ℝ) →* Multiplicative ℝ :=
  characterSlope (ContinuousMonoidHom.id _)

private def realFrequency : Multiplicative ℝ →* PontryaginDual (Multiplicative ℝ) where
  toFun t := modulusCharacter (ContinuousMonoidHom.id _) t.toAdd
  map_one' := PontryaginDual.ext fun t => by
    change Circle.exp (0 * t.toAdd) = 1
    rw [zero_mul, Circle.exp_zero]
  map_mul' a b := PontryaginDual.ext fun t => by
    change Circle.exp ((a.toAdd + b.toAdd) * t.toAdd) =
      Circle.exp (a.toAdd * t.toAdd) * Circle.exp (b.toAdd * t.toAdd)
    rw [add_mul, Circle.exp_add]

private theorem realFrequency_slope (χ : PontryaginDual (Multiplicative ℝ)) :
    realFrequency (realSlope χ) = χ :=
  PontryaginDual.ext fun t => (characterSlope_eq_exp (ContinuousMonoidHom.id _) χ t.toAdd).symm

/-- The norm-one subgroup is compact for a proper modulation. -/
theorem compactSpace_realModulation_ker {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) : CompactSpace m.toMonoidHom.ker :=
  isCompact_iff_compactSpace.mp (hm.isCompact_preimage (K := {1}) isCompact_singleton)

/-- A real one-parameter subgroup on a quotient by a compact subgroup lifts
to the original group. On the dual side its slope extends from the open
annihilator by injectivity of the divisible additive group of the reals. -/
theorem exists_oneParameter_lift_compact_quotient {G : Type u} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (K : Subgroup G) (hK : IsCompact (K : Set G))
    (c : Multiplicative ℝ →ₜ* G ⧸ K) :
    ∃ a : Multiplicative ℝ →ₜ* G,
      ∀ t, (QuotientGroup.mk (a t) : G ⧸ K) = c t := by
  let X := PontryaginDual G
  let A := lcaAnnihilator K
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let k : K →ₜ* G := ⟨K.subtype, continuous_subtype_val⟩
  have hA : IsOpen (A : Set X) := by
    change IsOpen ((PontryaginDual.map k) ⁻¹' ({1} : Set (PontryaginDual K)))
    exact (isOpen_discrete _).preimage (PontryaginDual.map k).continuous
  obtain ⟨e, he⟩ := lcaQuotientDual_equiv_annihilator K hK.isClosed
  let b := (PontryaginDual.map c).comp (e.symm : A →ₜ* PontryaginDual (G ⧸ K))
  let R := ULift.{u} ℝ
  let down : R ≃ₗ[ℤ] ℝ := ULift.moduleEquiv
  haveI : DivisibleBy R ℤ := divisibleByOfSMulRightSurj _ ℤ fun {n} hn y => by
    obtain ⟨x, hx⟩ := DivisibleBy.surjective_smul ℝ ℤ hn (down y)
    refine ⟨down.symm x, down.injective ?_⟩
    rw [map_smul, down.apply_symm_apply]
    exact hx
  haveI := (Module.Baer.of_divisible R).injective
  let j : Additive A →ₗ[ℤ] Additive X := A.subtype.toAdditive.toIntLinearMap
  let l : Additive A →ₗ[ℤ] R := down.symm.toLinearMap.comp
    ((realSlope.comp b.toMonoidHom).toAdditive.toIntLinearMap)
  have hj : Injective j := Subtype.val_injective
  obtain ⟨L, hL⟩ := Module.Injective.out j hj l
  let r := realFrequency.comp
    (AddMonoidHom.toMultiplicativeRight (down.toLinearMap.comp L).toAddMonoidHom)
  have hrA : (fun a : A => r a.val) = b := by
    funext a
    change realFrequency (Multiplicative.ofAdd (down (L (j (Additive.ofMul a))))) = b a
    rw [hL]
    have hl : down (l (Additive.ofMul a)) = (realSlope (b a)).toAdd :=
      down.apply_symm_apply _
    rw [hl]
    exact realFrequency_slope (b a)
  have hrcont : Continuous r := by
    apply continuous_of_continuousAt_one
    have hc : ContinuousWithinAt r (A : Set X) 1 := by
      apply (continuousWithinAt_iff_continuousAt_domRestrict r A.one_mem).mpr
      change ContinuousAt (fun a : A => r a.val) (1 : A)
      rw [hrA]
      exact b.continuous.continuousAt
    exact hc.continuousAt (hA.mem_nhds A.one_mem)
  let rcont : X →ₜ* PontryaginDual (Multiplicative ℝ) := ⟨r, hrcont⟩
  obtain ⟨d, hd⟩ := oneParameterSubgroups_dual (G := G)
  let a := d.symm rcont
  have ha : PontryaginDual.map a = rcont := (hd a).symm.trans (d.apply_symm_apply rcont)
  have hpre : QuotientGroup.mk ⁻¹' ({1} : Set (G ⧸ K)) = (K : Set G) := by
    simpa [QuotientGroup.mk_one] using QuotientGroup.preimage_mk_one K
  letI : T2Space (G ⧸ K) := IsTopologicalGroup.t2Space_iff_one_closed.mpr <| by
    rw [← (QuotientGroup.isQuotientMap_mk K).isCoinducing.isClosed_preimage, hpre]
    exact hK.isClosed
  refine ⟨a, fun t => ?_⟩
  apply (pontryaginBidualEval_isClosedEmbedding (G := G ⧸ K)).injective
  apply PontryaginDual.ext
  intro χ
  have h₁ : (PontryaginDual.map a (e χ).val) t = χ (QuotientGroup.mk (a t)) := he χ (a t)
  have h₂ : r (e χ).val = PontryaginDual.map c χ := by
    rw [show r (e χ).val = b (e χ) from congrFun hrA (e χ)]
    change PontryaginDual.map c (e.symm (e χ)) = _
    rw [e.symm_apply_apply]
  change χ (QuotientGroup.mk (a t)) = χ (c t)
  rw [← h₁, ha]
  exact congrArg (fun ψ : PontryaginDual (Multiplicative ℝ) => ψ t) h₂

/-- Every real one-parameter subgroup lifts through a proper surjective
homomorphism of locally compact Hausdorff abelian groups. -/
theorem exists_oneParameter_lift_proper {G H : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (q : G →ₜ* H) (hq : IsProperMap q) (hs : Surjective q)
    (c : Multiplicative ℝ →ₜ* H) :
    ∃ a : Multiplicative ℝ →ₜ* G, q.comp a = c := by
  let K := q.toMonoidHom.ker
  have hK : IsCompact (K : Set G) := hq.isCompact_preimage (K := {1}) isCompact_singleton
  let E := QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hs
  have hE (g : G) : E (QuotientGroup.mk g) = q g := rfl
  let Einv : H →ₜ* G ⧸ K := ⟨E.symm.toMonoidHom,
    (hq.isClosedMap.isQuotientMap q.continuous hs).continuous_iff.mpr (by
      have he : (E.symm : H → G ⧸ K) ∘ q = QuotientGroup.mk := funext fun g =>
        E.symm_apply_eq.mpr (hE g).symm
      change Continuous ((E.symm : H → G ⧸ K) ∘ q)
      rw [he]
      exact QuotientGroup.continuous_mk)⟩
  obtain ⟨a, ha⟩ := exists_oneParameter_lift_compact_quotient K hK (Einv.comp c)
  refine ⟨a, ContinuousMonoidHom.ext fun t => ?_⟩
  change q (a t) = c t
  rw [← hE, ha]
  exact E.apply_symm_apply _

/-- Every surjective proper real modulation has a continuous homomorphic section. -/
theorem exists_realModulation_section {G : Type u} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hs : Surjective m) :
    ∃ τ : Multiplicative ℝ →ₜ* G, RightInverse τ m := by
  obtain ⟨τ, hτ⟩ := exists_oneParameter_lift_proper m hm hs (ContinuousMonoidHom.id _)
  exact ⟨τ, fun t => DFunLike.congr_fun hτ t⟩

end

end Masullo
