import BruhatCyclicProductSections
import BruhatCyclicResidual
import BruhatSupportedWindow
import ModulatedDecayIsotypes

open Function Set Topology
open scoped Pointwise

namespace Masullo

noncomputable section

set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 8

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) (hms : Surjective m)

local notation "E" => ModulatedExponentialInductive m univ
local notation "logModulus" => (fun x : G ↦ Multiplicative.toAdd (m x))

include hm hms in
/-- A finite difference product admits a continuous choice of
representative with a common compact window below norm one. -/
theorem exists_bruhatCyclicProduct_negativeSupport_representative (gs : List G)
    (hgs : ∀ γ ∈ gs, 0 < (m γ).toAdd) :
    ∃ (W : Set ℝ) (R : BruhatSchwartz G →L[ℂ] E),
      IsCompact W ∧ W ⊆ Iio 0 ∧
      (∀ f, support (R f).val ⊆ logModulus ⁻¹' W) ∧
      (∀ f, f - modulatedDecay_zeroInclusion m univ (mem_univ 0) (R f) ∈
        (bruhatSchwartzDifferenceProduct gs).range) ∧
      ∀ w f, CyclicNormOneIsotypic m w f.val → CyclicNormOneIsotypic m w (R f).val := by
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  letI : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  induction gs with
  | nil =>
    refine ⟨∅, 0, isCompact_empty, empty_subset _, ?_, fun f ↦ ⟨f - J 0, rfl⟩,
      fun w f _ a x ↦ (mul_zero (w a : ℂ)).symm⟩
    intro f x hx
    exact (hx rfl).elim
  | cons g gs ih =>
    let d := (m g).toAdd
    have hd : 0 < d := hgs g List.mem_cons_self
    let C := Icc (-2 * d - 1) (-1)
    have hC : IsCompact C := isCompact_Icc
    have hcov (x : ℝ) : ∃ n : ℤ, x + d * (n : ℝ) ∈ interior C := by
      change ∃ n : ℤ, x + d * (n : ℝ) ∈ interior (Icc (-2 * d - 1) (-1))
      rw [interior_Icc]
      exact openInterval_covers_integerTranslations hd (by linarith) x
    obtain ⟨S, D, hSD, hS, hIso⟩ :=
      exists_bruhatCyclic_split_of_cover m hm hms g hd C hC hcov univ (mem_univ 0)
    obtain ⟨W, R, hW, hWneg, hRs, hR, hRiso⟩ := ih
      (fun a ha ↦ hgs a (List.mem_cons_of_mem _ ha))
    let C' : Set ℝ := (Homeomorph.addRight d) ⁻¹' W
    have hC' : IsCompact C' := (Homeomorph.addRight d).isCompact_preimage.mpr hW
    have hneg : C ∪ (W ∪ C') ⊆ Iio 0 := by
      refine union_subset (fun x hx ↦ ?_) (union_subset hWneg fun x hx ↦ ?_)
      · exact (show x ≤ -1 from hx.2).trans_lt (by norm_num)
      · have hx' : x + d < 0 := hWneg hx
        change x < 0
        linarith
    let A := bruhatSchwartzDifference g
    let B := modulatedDecay_cyclicDifference m hm hms g univ (mem_univ 0)
    let P := S + B.comp (R.comp D)
    have hJ (u : E) : J (B u) = A (J u) :=
      modulatedDecay_zeroInclusion_cyclicDifferenceProduct m hm hms univ (mem_univ 0) [g] u
    have hB (u : E) (x : G) : (B u).val x = u.val x - u.val (g * x) :=
      modulatedDecay_cyclicDifference_apply m hm hms g univ (mem_univ 0) u x
    refine ⟨C ∪ (W ∪ C'), P, hC.union (hW.union hC'), hneg, ?_, ?_,
      fun w f hf a x ↦ ?_⟩
    · intro f x hx
      by_contra h
      let u := R (D f)
      have hs : (S f).val x = 0 := notMem_support.mp fun z ↦ h (Or.inl (hS f z))
      have hu : u.val x = 0 := notMem_support.mp fun z ↦ h (Or.inr (Or.inl (hRs (D f) z)))
      have hgu : u.val (g * x) = 0 := notMem_support.mp fun z ↦ by
        apply h
        refine Or.inr (Or.inr ?_)
        change (m x).toAdd + d ∈ W
        have hlog : (m (g * x)).toAdd = (m x).toAdd + d := by rw [map_mul, toAdd_mul, add_comm]
        exact hlog ▸ hRs (D f) z
      apply hx
      change (S f).val x + (B u).val x = 0
      rw [hB, hs, hu, hgu, sub_self, add_zero]
    · intro f
      obtain ⟨v, hv⟩ := hR (D f)
      refine ⟨v, ?_⟩
      change A (bruhatSchwartzDifferenceProduct gs v) = f - J (S f + B (R (D f)))
      change bruhatSchwartzDifferenceProduct gs v = D f - J (R (D f)) at hv
      rw [hv, map_sub, hSD, map_add, hJ, sub_sub]
    · let u := R (D f)
      have hu := hRiso w (D f) (hIso w f hf).2
      have hi : CyclicNormOneIsotypic m w (B u).val := by
        intro k y
        rw [hB, hB, mul_left_comm g, hu, hu, mul_sub]
      change (S f).val (a.val⁻¹ * x) + (B u).val (a.val⁻¹ * x) =
        (w a : ℂ) * ((S f).val x + (B u).val x)
      exact (congrArg₂ (· + ·) ((hIso w f hf).1 a x) (hi a x)).trans (mul_add _ _ _).symm

private theorem bruhatDifferenceProduct_translate (gs : List G) (z : G) (f : BruhatSchwartz G) :
    bruhatSchwartzDifferenceProduct gs (bruhatSchwartz_translate z f) =
      bruhatSchwartz_translate z (bruhatSchwartzDifferenceProduct gs f) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change bruhatSchwartzDifference g (bruhatSchwartzDifferenceProduct gs (bruhatSchwartz_translate z f)) =
      bruhatSchwartz_translate z (bruhatSchwartzDifference g (bruhatSchwartzDifferenceProduct gs f))
    rw [ih]
    apply Subtype.ext
    funext x
    simp only [bruhatSchwartzDifference_apply, bruhatSchwartz_translate_apply, mul_left_comm]

private theorem bruhatDifferenceProduct_preimage_isotypic
    (gs : List G) (hgs : ∀ g ∈ gs, 0 < (m g).toAdd) (w : PontryaginDual m.toMonoidHom.ker)
    (v : BruhatSchwartz G)
    (h : CyclicNormOneIsotypic m w (bruhatSchwartzDifferenceProduct gs v).val) :
    CyclicNormOneIsotypic m w v.val := by
  intro a x
  let D := bruhatSchwartzDifferenceProduct gs
  have hi : Injective D := bruhatSchwartzDifferenceProduct_injective m gs hgs
  have he : bruhatSchwartz_translate a.val (D v) = (w a : ℂ) • D v :=
    Subtype.ext (funext fun y ↦ (bruhatSchwartz_translate_apply a.val (D v) y).trans (h a y))
  have hv : bruhatSchwartz_translate a.val v = (w a : ℂ) • v := hi
    ((bruhatDifferenceProduct_translate gs a.val v).trans (he.trans (D.map_smul _ _).symm))
  exact (bruhatSchwartz_translate_apply a.val v x).symm.trans
    (congrArg (fun f : BruhatSchwartz G ↦ f.val x) hv)

include hm hms in
private theorem decayDifferenceProduct_preserves_isotype
    (w : PontryaginDual m.toMonoidHom.ker) (gs : List G)
    (f : E) (hf : f ∈ modulatedDecayIsotype m w univ) :
    modulatedDecay_cyclicDifferenceProduct m hm hms univ (mem_univ 0) gs f ∈
      modulatedDecayIsotype m w univ := by
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  have hJ := modulatedDecay_zeroInclusion_cyclicDifferenceProduct m hm hms univ
    (mem_univ 0) gs f
  intro k x
  have he := bruhatSchwartzDifferenceProduct_preserves_isotype w gs (J f) hf k x
  exact (congrArg (fun z : BruhatSchwartz G ↦ z.val (k.val⁻¹ * x)) hJ).trans
    (he.trans (congrArg ((w k : ℂ) * ·) (congrArg (fun z : BruhatSchwartz G ↦ z.val x) hJ.symm)))

include hm hms in
/-- Finite differences restricted to the norm-one character isotype. -/
def bruhatEntireIsotypeDifferenceProduct
    (w : PontryaginDual m.toMonoidHom.ker) (gs : List G) :
    modulatedDecayIsotype m w univ →L[ℂ] modulatedDecayIsotype m w univ :=
  (modulatedDecay_cyclicDifferenceProduct m hm hms univ (mem_univ 0) gs).restrict
    (decayDifferenceProduct_preserves_isotype m hm hms w gs)

private theorem quotients_equiv_of_representatives {X U : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U]
    (j : U →L[ℂ] X) (P : Submodule ℂ X) (S : X →L[ℂ] U)
    (hS : ∀ x, P.mkQ (j (S x)) = P.mkQ x) :
    let T := P.mkQL.comp j
    Surjective T ∧ ∃ e : (U ⧸ T.ker) ≃L[ℂ] (X ⧸ P),
      ∀ u, e (T.ker.mkQ u) = T u := by
  dsimp only
  let T := P.mkQL.comp j
  let F := T.ker.liftQL T le_rfl
  have hF (u : U) : F (T.ker.mkQ u) = T u := rfl
  have hInject : Injective F := by
    intro x y h
    obtain ⟨u, rfl⟩ := T.ker.mkQ_surjective x
    obtain ⟨v, rfl⟩ := T.ker.mkQ_surjective y
    exact (Submodule.Quotient.eq T.ker).2 (show T (u - v) = 0 by
      rw [map_sub, ← hF u, ← hF v, h, sub_self])
  let L := T.ker.mkQL.comp S
  have hL : P ≤ L.ker := by
    intro x hx
    apply hInject
    change F (T.ker.mkQ (S x)) = F 0
    rw [hF, map_zero]
    exact (hS x).trans ((Submodule.Quotient.mk_eq_zero P).2 hx)
  let R := P.liftQL L hL
  have hright : RightInverse R F := by
    intro y
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    exact hS x
  have hleft : LeftInverse R F := fun y ↦ hInject (hright (F y))
  refine ⟨fun y ↦ ?_, ⟨⟨LinearEquiv.ofLinear F.toLinearMap R.toLinearMap
    (LinearMap.ext hright) (LinearMap.ext hleft), F.continuous, R.continuous⟩, hF⟩⟩
  obtain ⟨x, rfl⟩ := P.mkQ_surjective y
  exact ⟨S x, hS x⟩

include hm hms in
/-- Theorem 4.6.2.1. A common compact support below norm one works
for all representatives of the finite-product quotient of an isotype. -/
theorem bruhatCyclicProduct_supportedIsotypeQuotient
    (w : PontryaginDual m.toMonoidHom.ker) (gs : List G)
    (hgs : ∀ g ∈ gs, 0 < (m g).toAdd) :
    let H := modulatedDecayIsotype m w univ
    let P := (bruhatEntireIsotypeDifferenceProduct m hm hms w gs).range
    ∃ C : Set G, IsCompact C ∧
      (m.toMonoidHom.ker : Set G) * C = C ∧
      (∀ x ∈ C, Real.exp (m x).toAdd ∈ Ioo 0 1) ∧
      let U := (bruhatSupportedInvariant m ⊥ C).comap H.subtype
      let T := P.mkQL.comp U.subtypeL
      Surjective T ∧ ∃ e : (U ⧸ T.ker) ≃L[ℂ] (H ⧸ P),
        ∀ u, e (T.ker.mkQ u) = T u := by
  dsimp only
  let H := modulatedDecayIsotype m w univ
  let A := bruhatEntireIsotypeDifferenceProduct m hm hms w gs
  let J := modulatedDecay_zeroInclusion m univ (mem_univ 0)
  obtain ⟨W, R, hW, hneg, hSup, hR, hRIso⟩ :=
    exists_bruhatCyclicProduct_negativeSupport_representative m hm hms gs hgs
  let C := logModulus ⁻¹' W
  have hC : IsCompact C := hm.isCompact_preimage
    (show IsCompact (Multiplicative.toAdd ⁻¹' W) from hW)
  have hInv (k : m.toMonoidHom.ker) (x : G) : k.val * x ∈ C ↔ x ∈ C := by
    change (m (k.val * x)).toAdd ∈ W ↔ (m x).toAdd ∈ W
    rw [map_mul, show m k.val = 1 from k.property, one_mul]
  have hStable : (m.toMonoidHom.ker : Set G) * C = C := by
    ext x
    constructor
    · rintro ⟨k, hk, y, hy, rfl⟩
      exact (hInv ⟨k, hk⟩ y).2 hy
    · intro hx
      exact ⟨1, m.toMonoidHom.ker.one_mem, x, hx, one_mul x⟩
  let U := (bruhatSupportedInvariant m ⊥ C).comap H.subtype
  let L := R.comp (J.comp H.subtypeL)
  have hL (f : H) : L f ∈ H := hRIso w (J f.val) f.property
  let R₀ := L.codRestrict H hL
  have hR₀ (f : H) : R₀ f ∈ U := by
    change L f ∈ bruhatSupportedInvariant m ⊥ C
    refine ⟨hSup (J f.val), fun k x ↦ ?_⟩
    have hk : k.val = 1 := Subgroup.mem_bot.mp k.property
    rw [hk, inv_one, one_mul]
  let S := R₀.codRestrict U hR₀
  have hS (f : H) : A.range.mkQ (S f).val = A.range.mkQ f := by
    let g : H := f - R₀ f
    have hJg : J g.val = J f.val - J (R (J f.val)) := J.map_sub _ _
    have hg : J g.val ∈ (bruhatSchwartzDifferenceProduct gs).range :=
      hJg.symm ▸ hR (J f.val)
    obtain ⟨u, hu⟩ := (modulatedDecay_cyclicDifferenceProduct_range_preimage m hm hms
      univ (mem_univ 0) gs hgs g.val).1 hg
    let B := modulatedDecay_cyclicDifferenceProduct m hm hms univ (mem_univ 0) gs
    have hBu : B u = g.val := hu
    have hJu : bruhatSchwartzDifferenceProduct gs (J u) = J g.val :=
      (modulatedDecay_zeroInclusion_cyclicDifferenceProduct m hm hms univ
        (mem_univ 0) gs u).symm.trans (congrArg J hBu)
    have hIso : CyclicNormOneIsotypic m w (bruhatSchwartzDifferenceProduct gs (J u)).val := by
      rw [hJu]
      exact g.property
    have huIso : u ∈ H := bruhatDifferenceProduct_preimage_isotypic m gs hgs w (J u) hIso
    apply (Submodule.Quotient.eq A.range).2
    change R₀ f - f ∈ A.range
    simpa only [g, neg_sub] using (A.range.neg_mem ⟨⟨u, huIso⟩, Subtype.ext hBu⟩)
  refine ⟨C, hC, hStable, fun x hx ↦ ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (hneg hx)⟩, ?_⟩
  exact quotients_equiv_of_representatives U.subtypeL A.range S hS

end

end Masullo
