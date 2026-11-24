import BruhatFixedStages
import ElementaryLogSeminorms

open Function MeasureTheory Module Set Topology
open scoped ENNReal

namespace Masullo

noncomputable section

private theorem withSeminorms_pullback {E V J : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (q : SeminormFamily ℂ V J) (hq : WithSeminorms q) (e : E ≃L[ℂ] V) :
    WithSeminorms (fun i => (q i).comp e.toLinearMap) := by
  have h : IsInducing (e.toLinearMap : E → V) := e.toHomeomorph.isInducing
  exact h.withSeminorms (f := e.toLinearMap) hq

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

namespace WholeBruhatStage

set_option maxHeartbeats 1500000

variable (P : WholeBruhatStage G)

abbrev ElementaryCoordinates (P : WholeBruhatStage G) :=
  ElementaryLCAModel P.val.2.realDim P.val.2.torusDim P.val.2.latticeRank P.val.2.finiteFactor

theorem logCoordinate_surjective (m : G →ₜ* Multiplicative ℝ) (hms : Surjective m) :
    Surjective (P.logCoordinate m) := by
  intro t
  obtain ⟨g, hg⟩ := hms (Multiplicative.ofAdd t)
  exact ⟨(P.coordinates g).toAdd, (P.logCoordinate_coordinates m g).trans
    (congrArg Multiplicative.toAdd hg)⟩

theorem logCoordinate_dimensions (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    (hms : Surjective m) : P.val.2.realDim = 1 ∧ P.val.2.latticeRank = 0 :=
  elementary_dimensions_of_proper_surjective_log (P.logCoordinate m)
    (P.logCoordinate_isProperMap m hm) (P.logCoordinate_surjective m hms)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
private theorem coordinates_t2 : T2Space (Multiplicative P.ElementaryCoordinates) := by
  letI : T2Space P.val.2.finiteFactor := DiscreteTopology.toT2Space
  letI : T2Space P.ElementaryCoordinates := Prod.t2Space
  exact inferInstanceAs (T2Space P.ElementaryCoordinates)

theorem coordinates_proper (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) :
    IsProperMap P.coordinates := by
  letI := P.coordinates_t2
  have h := (P.logCoordinate_isProperMap m hm).continuous.comp
    (continuous_toAdd : Continuous (Multiplicative.toAdd : Multiplicative P.ElementaryCoordinates → P.ElementaryCoordinates))
  refine isProperMap_of_comp_of_t2 P.coordinates.continuous h ?_
  have he : ((fun y : Multiplicative P.ElementaryCoordinates => P.logCoordinate m y.toAdd) ∘ P.coordinates) =
      (fun x => (m x).toAdd) := funext (P.logCoordinate_coordinates m)
  change IsProperMap ((fun y : Multiplicative P.ElementaryCoordinates => P.logCoordinate m y.toAdd) ∘ P.coordinates)
  rw [he]
  exact hm

/-- Differentiation along a group orbit agrees with differentiation along
its image on the elementary quotient. -/
theorem realize_derivative (c : Multiplicative ℝ →ₜ* G) (f : P.val.Space) :
    bruhatSchwartz_derivative c (P.val.inclusionCLM f) =
      P.val.inclusionCLM (elementarySchwartz_derivative (P.coordinates.comp c) f) := by
  apply Subtype.ext
  funext x
  change bruhatOrbitDeriv c (P.val.realize f) x =
    P.val.realize (elementarySchwartz_derivative (P.coordinates.comp c) f) x
  rw [P.realize_eq_coordinates, elementarySchwartz_derivative_apply, bruhatOrbitDeriv,
    elementaryOrbitDeriv]
  congr 1
  funext t
  rw [P.realize_eq_coordinates, map_mul]
  rfl

/-- Composition of invariant derivatives on the full Schwartz–Bruhat space. -/
def bruhatDerivativeWord (cs : List (Multiplicative ℝ →ₜ* G)) :
    BruhatSchwartz G →L[ℂ] BruhatSchwartz G :=
  cs.foldr (fun c D => (bruhatSchwartz_derivative c).comp D) (ContinuousLinearMap.id ℂ _)

theorem realize_derivativeWord (cs : List (Multiplicative ℝ →ₜ* G)) (f : P.val.Space) :
    bruhatDerivativeWord cs (P.val.inclusionCLM f) =
      P.val.inclusionCLM (elementarySchwartz_derivativeWord
        (cs.map fun c => P.coordinates.comp c) f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change bruhatSchwartz_derivative c (bruhatDerivativeWord cs (P.val.inclusionCLM f)) =
      P.val.inclusionCLM (elementarySchwartz_derivative (P.coordinates.comp c)
        (elementarySchwartz_derivativeWord (cs.map fun c => P.coordinates.comp c) f))
    exact (congrArg (bruhatSchwartz_derivative c) ih).trans
      (P.realize_derivative c (elementarySchwartz_derivativeWord
        (cs.map fun c => P.coordinates.comp c) f))

section Measure

variable [MeasurableSpace G] [BorelSpace G]
variable [MeasurableSpace P.val.2.finiteFactor] [BorelSpace P.val.2.finiteFactor]

/-- An ambient Haar measure pushes forward to a Haar measure on the
elementary quotient of any whole-group stage of a proper modulation. -/
theorem coordinates_map_addHaar (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m) :
    (Measure.map (fun g => (P.coordinates g).toAdd) μ).IsAddHaarMeasure := by
  letI : BorelSpace ((Fin P.val.2.latticeRank → ℤ) × P.val.2.finiteFactor) := Prod.borelSpace
  letI : BorelSpace ((Fin P.val.2.torusDim → AddCircle (1 : ℝ)) ×
      (Fin P.val.2.latticeRank → ℤ) × P.val.2.finiteFactor) := Prod.borelSpace
  letI : BorelSpace P.ElementaryCoordinates := Prod.borelSpace
  letI : MeasurableSpace (Multiplicative P.ElementaryCoordinates) :=
    inferInstanceAs (MeasurableSpace P.ElementaryCoordinates)
  letI : BorelSpace (Multiplicative P.ElementaryCoordinates) :=
    inferInstanceAs (BorelSpace P.ElementaryCoordinates)
  letI := P.coordinates_t2
  let ν : Measure (Multiplicative P.ElementaryCoordinates) := Measure.map P.coordinates μ
  letI : ν.IsHaarMeasure := μ.isHaarMeasure_map P.coordinates.toMonoidHom
    P.coordinates.continuous P.coordinates_surjective (isProperMap_iff_tendsto_cocompact.mp (P.coordinates_proper m hm)).2
  exact
    { lt_top_of_isCompact := fun {_} h => IsCompact.measure_lt_top (μ := ν) h
      map_add_left_eq_self := fun g => map_mul_left_eq_self ν (Multiplicative.ofAdd g)
      open_pos := fun s hs hn => Measure.IsOpenPosMeasure.open_pos (μ := ν) s hs hn }

/-- Fixed-stage Lᵖ seminorms computed on the original group. The directions
are chosen on the group and their projected velocities form a chart basis. -/
theorem withSeminorms_fixed_logWeightedLp [SecondCountableTopology G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* Multiplicative ℝ) (hm : IsProperMap m)
    {d : ℕ} (B : Basis (Fin d) ℝ
      (EuclideanSpace ℝ (Fin P.val.2.realDim) × EuclideanSpace ℝ (Fin P.val.2.torusDim)))
    (γ : Fin d → Multiplicative ℝ →ₜ* G)
    (hγ : ∀ j, P.coordinates.comp (γ j) = elementaryOneParameter (B j))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ q : SeminormFamily ℂ P.fixedSubmodule ((Fin d → ℕ) × ℕ), WithSeminorms q ∧
      ∀ i f, q i f = lpNorm
        (fun g => (((|(m g).toAdd| : ℝ) : ℂ) ^ i.2) *
          (bruhatDerivativeWord ((invariantBasisWord i.1).map γ) f.val).val g) p μ := by
  let ν := Measure.map (fun g => (P.coordinates g).toAdd) μ
  letI : ν.IsAddHaarMeasure := P.coordinates_map_addHaar μ m hm
  letI : BorelSpace ((Fin P.val.2.latticeRank → ℤ) × P.val.2.finiteFactor) := Prod.borelSpace
  letI : BorelSpace ((Fin P.val.2.torusDim → AddCircle (1 : ℝ)) ×
      (Fin P.val.2.latticeRank → ℤ) × P.val.2.finiteFactor) := Prod.borelSpace
  letI : BorelSpace P.ElementaryCoordinates := Prod.borelSpace
  let l := P.logCoordinate m
  have hl := P.logCoordinate_isProperMap m hm
  obtain ⟨q, hq, hqnorm⟩ := elementarySchwartz_withSeminorms_logWeightedLp l hl B ν p
  let e := P.equivFixedSubmodule
  let q₀ : SeminormFamily ℂ P.val.Space ((Fin d → ℕ) × ℕ) := q
  have hq₀ : WithSeminorms q₀ := hq
  have hq' := @withSeminorms_pullback P.fixedSubmodule P.val.Space ((Fin d → ℕ) × ℕ)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance q₀ hq₀ e.symm
  refine ⟨_, hq', fun i f => ?_⟩
  let u := e.symm f
  change q i u = _
  rw [hqnorm]
  let w := invariantBasisWord i.1
  let derivs : List (Multiplicative ℝ →ₜ* Multiplicative P.ElementaryCoordinates) := w.map (fun j => elementaryOneParameter (B j))
  let T (g : G) := (P.coordinates g).toAdd
  let H := elementaryLogWeightedWord l derivs i.2 u
  have hT : Continuous T := continuous_toAdd.comp P.coordinates.continuous
  have hH := elementaryLogWeightedWord_continuous l hl.continuous derivs i.2 u
  have hinc : P.val.inclusionCLM u = f.val :=
    congrArg Subtype.val (e.apply_symm_apply f)
  have hc : ((w.map γ).map fun c => P.coordinates.comp c) = derivs := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    exact hγ j
  have he : (fun g => (((|(m g).toAdd| : ℝ) : ℂ) ^ i.2) *
      (bruhatDerivativeWord (w.map γ) f.val).val g) = H ∘ T := by
    funext g
    have hd := congrArg (fun z : BruhatSchwartz G => z.val g)
      (P.realize_derivativeWord (w.map γ) u)
    change _ = P.val.realize (elementarySchwartz_derivativeWord
      ((w.map γ).map fun c => P.coordinates.comp c) u) g at hd
    rw [hinc] at hd
    rw [hc, P.realize_eq_coordinates, elementarySchwartz_derivativeWord_apply] at hd
    change _ = (((|l (T g)| : ℝ) : ℂ) ^ i.2) * elementaryOrbitWord derivs u (T g)
    rw [hd, show l (T g) = (m g).toAdd from P.logCoordinate_coordinates m g]
  change lpNorm H p ν = lpNorm _ p μ
  rw [he, ← toReal_eLpNorm hH.aestronglyMeasurable,
    ← toReal_eLpNorm (hH.comp hT).aestronglyMeasurable]
  exact congrArg ENNReal.toReal (eLpNorm_map_measure hH.aestronglyMeasurable hT.measurable.aemeasurable)


end Measure


end WholeBruhatStage

end
end Masullo
