/-
The splitting argument adapts RiemannMasullo AppD_SchwartzBruhat/Sec1c.lean at
a1d61084d11ef14e3119178113488c654be4da80 (Apache-2.0).
See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import ElementarySchwartzGraph
import BruhatCompactSupport
import ClassicalSchwartzNuclear
import SchwartzGaussian

open Function Topology

namespace Masullo

noncomputable section

variable {m n r m' n' r' : ℕ} {F F' : Type*}
  [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [AddCommGroup F'] [TopologicalSpace F'] [DiscreteTopology F'] [Finite F']

local notation "A" => ElementaryLCAModel m n r F
local notation "B" => ElementaryLCAModel m' n' r' F'
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m') × EuclideanSpace ℝ (Fin n')

/-- An open surjection of elementary groups admits a continuous additive section
on the target's real and free lattice factors. -/
theorem elementary_split_noncompact (p : A →+ B) (hp : Continuous p) (ho : IsOpenMap p)
    (hs : Surjective p) :
    ∃ τ : B →+ A, Continuous τ ∧ ∀ z, p (τ z) = (z.1, 0, z.2.2.1, 0) := by
  classical
  obtain ⟨L, hL, hcover⟩ := elementaryCoverHom_lift_of_open p hp ho
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hL)
  let R₁ : Y →L[ℝ] X := ⟨R, R.continuous_of_finiteDimensional⟩
  let v : EuclideanSpace ℝ (Fin m') →+ A :=
    elementaryCoverHom.comp
      ((R₁.comp (ContinuousLinearMap.inl ℝ _ _)).toLinearMap.toAddMonoidHom)
  have hv : Continuous v := elementaryCoverHom_continuous.comp
    (R₁.continuous.comp (ContinuousLinearMap.inl ℝ _ _).continuous)
  let j : (Fin r' → ℤ) →+ B :=
    (AddMonoidHom.inr _ _).comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _))
  let b := Pi.basisFun ℤ (Fin r')
  choose w hw using fun i ↦ hs (j (b i))
  let k := (b.constr ℤ w).toAddMonoidHom
  have hk : p.comp k = j := by
    have he : (p.comp k).toIntLinearMap = j.toIntLinearMap := by
      apply b.ext
      intro i
      change p (b.constr ℤ w (b i)) = _
      rw [b.constr_basis]
      exact hw i
    exact DFunLike.ext _ _ fun z ↦ DFunLike.congr_fun he z
  let T : B →+ A := v.comp (AddMonoidHom.fst _ _) +
    k.comp ((AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _)))
  refine ⟨T, (hv.comp continuous_fst).add
    ((continuous_of_discreteTopology (f := k)).comp continuous_snd.snd.fst), fun z ↦ ?_⟩
  have hvz : p (v z.1) = elementaryCoverHom (z.1, 0) := by
    change p (elementaryCoverHom (R₁ (z.1, 0))) = _
    rw [hcover, show L (R₁ (z.1, 0)) = (z.1, 0) from DFunLike.congr_fun hR _]
  change p (v z.1 + k z.2.2.1) = _
  rw [map_add, hvz, show p (k z.2.2.1) = j z.2.2.1 from DFunLike.congr_fun hk _]
  simp [j, elementaryCoverHom, elementaryCover, Pi.zero_def]

open scoped ContDiff
open MeasureTheory Set

private theorem elementary_positive_test :
    ∃ s : ElementarySchwartz m n r F, ∀ x, 0 < (s x).re := by
  let E (l : ℕ) := ElementaryLCAModel l 0 0 PUnit
  let p : A →+ E m := (AddMonoidHom.inl _ _).comp (AddMonoidHom.fst _ _)
  let lattice : A →+ EuclideanSpace ℝ (Fin r) :=
    { toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ (x.2.2.1 i : ℝ))
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by ext i; exact Int.cast_add .. }
  let q : A →+ E r := (AddMonoidHom.inl _ _).comp lattice
  have hp : Continuous p := continuous_fst.prodMk continuous_const
  have hq : Continuous q :=
    ((continuous_of_discreteTopology (f := fun z : Fin r → ℤ ↦ WithLp.toLp 2 (fun i ↦ (z i : ℝ)))).comp
      continuous_snd.snd.fst).prodMk continuous_const
  have hcoord (j : Fin m ⊕ Fin r) : ∃ (a : E m →+ ℝ) (b : E r →+ ℝ), Continuous a ∧ Continuous b ∧
      ∀ x, elementaryGrowthCoordinate j x = a (p x) + b (q x) := by
    cases j with
    | inl i => exact ⟨elementaryGrowthCoordinate (.inl i), 0,
        elementaryGrowthCoordinate_continuous _, continuous_zero, fun x ↦ (add_zero _).symm⟩
    | inr i => exact ⟨0, elementaryGrowthCoordinate (.inl i), continuous_zero,
        elementaryGrowthCoordinate_continuous _, fun x ↦ (zero_add _).symm⟩
  have hr (l : ℕ) : ∃ s : ElementarySchwartz l 0 0 PUnit,
      ∀ x, s x = (Real.exp (-‖x.1‖ ^ 2) : ℝ) := by
    obtain ⟨g, hg⟩ := exists_gaussian_schwartz (E := EuclideanSpace ℝ (Fin l)) 1 one_pos
    refine ⟨⟨_, (elementarySchwartzSubmodule_real_iff (g : _ → ℂ)).mpr ⟨g, rfl⟩⟩, fun x ↦ ?_⟩
    simpa using hg x.1
  obtain ⟨s, hs⟩ := hr m
  obtain ⟨t, ht⟩ := hr r
  refine ⟨⟨_, elementarySchwartz_graph_mem p q hp hq hcoord s t⟩, fun x ↦ ?_⟩
  change 0 < (s (p x) * t (q x)).re
  rw [hs, ht, ← Complex.ofReal_mul, Complex.ofReal_re]
  positivity

section Average

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [CommGroup H] [TopologicalSpace H] [T2Space H]

set_option maxHeartbeats 1800000 in
/-- Haar averaging along an open surjective elementary homomorphism lifts each
target test. Normalize a positive source test over the compact remainder after
splitting off the real and free lattice coordinates. -/
theorem elementarySchwartz_exists_fibreLift (e : ElementaryLCAPresentation G)
    (d : ElementaryLCAPresentation H) (p : G →ₜ* H) (hpo : IsOpenMap p)
    (hps : Surjective p) (ν : Measure p.toMonoidHom.ker) [ν.IsHaarMeasure]
    (s : ElementarySchwartz d.realDim d.torusDim d.latticeRank d.finiteFactor) :
    ∃ t : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor,
      ∀ y : G, (∫ k : p.toMonoidHom.ker, t (e.equiv (y * k.val)).toAdd ∂ν) =
        s (d.equiv (p y)).toAdd := by
  classical
  let E := ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor
  let Target := ElementaryLCAModel d.realDim d.torusDim d.latticeRank d.finiteFactor
  let C := ElementaryLCAModel 0 d.torusDim 0 d.finiteFactor
  let π : E →+ Target :=
    (d.equiv.toMonoidHom.comp (p.toMonoidHom.comp e.equiv.symm.toMonoidHom)).toAdditive
  have hc : Continuous π := d.equiv.continuous.comp (p.continuous.comp e.equiv.symm.continuous)
  have hπ (y : G) : π (e.equiv y).toAdd = (d.equiv (p y)).toAdd :=
    congrArg (fun x ↦ (d.equiv (p x)).toAdd) (e.equiv.symm_apply_apply y)
  obtain ⟨τ, hτ, hsec⟩ := elementary_split_noncompact π hc
    (d.equiv.isOpenMap.comp (hpo.comp e.equiv.symm.isOpenMap))
    (d.equiv.surjective.comp (hps.comp e.equiv.symm.surjective))
  let r := AddMonoidHom.id E - τ.comp π
  have hr : Continuous r := continuous_id.sub (hτ.comp hc)
  let c : Target →+ C := {
    toFun z := (0, z.2.1, 0, z.2.2.2)
    map_zero' := rfl
    map_add' _ _ := Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl)) }
  let j : C →+ Target := {
    toFun z := (0, z.2.1, 0, z.2.2.2)
    map_zero' := rfl
    map_add' _ _ := Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl)) }
  have hc' : Continuous c := continuous_const.prodMk
    (continuous_snd.fst.prodMk (continuous_const.prodMk continuous_snd.snd.snd))
  have hj : Continuous j := continuous_const.prodMk
    (continuous_snd.fst.prodMk (continuous_const.prodMk continuous_snd.snd.snd))
  have hrπ (z : E) : π (r z) = j (c (π z)) := by
    change π (z - τ (π z)) = _
    rw [map_sub, hsec]
    exact Prod.ext (sub_self _) (Prod.ext (sub_zero _) (Prod.ext (sub_self _) (sub_zero _)))
  obtain ⟨θ, hθ⟩ := elementary_positive_test
    (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
  obtain ⟨η, hη⟩ := elementarySchwartz_exists_fibreAverage e d p hpo hps ν θ
  have hne (z : Target) : η z ≠ 0 := by
    obtain ⟨y, hy⟩ := hps (d.equiv.symm (Multiplicative.ofAdd z))
    have hy' : (d.equiv (p y)).toAdd = z := by rw [hy, d.equiv.apply_symm_apply]; rfl
    rw [← hy', hη]
    let f (k : p.toMonoidHom.ker) := θ (e.equiv (y * k.val)).toAdd
    have hint : Integrable f ν :=
      (elementarySchwartz_fibre_integrable_dominated e p.toMonoidHom.ker
        (isClosed_singleton.preimage p.continuous) ν θ).1 y
    have hpos : 0 < ∫ k, (f k).re ∂ν := by
      apply (integral_pos_iff_support_of_nonneg (fun k ↦ (hθ _).le) hint.re).mpr
      rw [show support (fun k ↦ (f k).re) = univ from eq_univ_of_forall fun k ↦ (hθ _).ne']
      exact isOpen_univ.measure_pos ν univ_nonempty
    intro hz
    change 0 < ∫ k, RCLike.re (f k) ∂ν at hpos
    rw [integral_re hint] at hpos
    exact (ne_of_gt hpos) (congrArg Complex.re hz)
  let g (z : C) := (η (j z))⁻¹
  have hg : g ∈ elementarySchwartzSubmodule 0 d.torusDim 0 d.finiteFactor := by
    apply elementarySchwartz_mem_of_compactSupport _ (HasCompactSupport.of_compactSpace _)
    exact fun a b ↦ (elementaryContDiff_hom j hj η η.property.1 a b).inv fun u ↦ hne _
  let g' : ElementarySchwartz 0 d.torusDim 0 d.finiteFactor := ⟨g, hg⟩
  have hs' : (fun z ↦ s z * g' (c z)) ∈
      elementarySchwartzSubmodule d.realDim d.torusDim d.latticeRank d.finiteFactor :=
    elementarySchwartz_graph_mem (AddMonoidHom.id Target) c continuous_id hc'
      (fun i ↦ ⟨elementaryGrowthCoordinate i, 0, elementaryGrowthCoordinate_continuous _,
        continuous_zero, fun z ↦ (add_zero _).symm⟩) s g'
  let s' : ElementarySchwartz d.realDim d.torusDim d.latticeRank d.finiteFactor := ⟨_, hs'⟩
  have hcoord (i) : ∃ (a : Target →+ ℝ) (b : E →+ ℝ), Continuous a ∧ Continuous b ∧
      ∀ x, elementaryGrowthCoordinate i x = a (π x) + b (r x) := by
    let b : E →+ ℝ := elementaryGrowthCoordinate i
    refine ⟨b.comp τ, b, (elementaryGrowthCoordinate_continuous _).comp hτ,
      elementaryGrowthCoordinate_continuous _, fun x ↦ ?_⟩
    change b x = b (τ (π x)) + b (x - τ (π x))
    rw [map_sub]
    abel
  refine ⟨⟨_, elementarySchwartz_graph_mem π r hc hr hcoord s' θ⟩, fun y ↦ ?_⟩
  let z := (e.equiv y).toAdd
  let z' := π z
  let y' := e.equiv.symm (Multiplicative.ofAdd (r z))
  have hkπ (k : p.toMonoidHom.ker) : π (e.equiv k.val).toAdd = 0 := by
    rw [hπ, show p k.val = 1 from k.property, map_one]
    rfl
  have hy' : (e.equiv y').toAdd = r z :=
    congrArg Multiplicative.toAdd (e.equiv.apply_symm_apply _)
  have hpr : (d.equiv (p y')).toAdd = j (c z') :=
    (hπ y').symm.trans (hy' ▸ hrπ z)
  have hfun (k : p.toMonoidHom.ker) :
      s' (π (e.equiv (y * k.val)).toAdd) * θ (r (e.equiv (y * k.val)).toAdd) =
      s' z' * θ (e.equiv (y' * k.val)).toAdd := by
    rw [map_mul e.equiv y _, map_mul e.equiv y' _]
    change s' (π (z + (e.equiv k.val).toAdd)) * θ (r (z + (e.equiv k.val).toAdd)) =
      _ * θ ((e.equiv y').toAdd + _)
    rw [map_add, hkπ, add_zero, map_add, hy']
    have hrk : r (e.equiv k.val).toAdd = (e.equiv k.val).toAdd := by
      change (e.equiv k.val).toAdd - τ (π (e.equiv k.val).toAdd) = _
      rw [hkπ, map_zero, sub_zero]
    rw [hrk]
  change (∫ k : p.toMonoidHom.ker, s' (π (e.equiv (y * k.val)).toAdd) *
    θ (r (e.equiv (y * k.val)).toAdd) ∂ν) = _
  simp_rw [hfun, integral_const_mul, ← hη y', hpr, ← hπ y]
  change (s z' * (η (j (c z')))⁻¹) * η (j (c z')) = s z'
  field_simp [hne]

end Average

end
end Masullo
