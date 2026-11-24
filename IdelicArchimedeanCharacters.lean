import ArchimedeanCharacters
import HeckeEulerProducts

open NumberField Function
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- Insert a unit at one infinite place and put one at each other place. -/
def singleInfiniteIdele (v : InfinitePlace F) : v.Completionˣ →ₜ* Idele F := by
  classical
  let a (x : v.Completion) : InfiniteAdeleRing F :=
    Function.update (fun w : InfinitePlace F => (1 : w.Completion)) v x
  let f : v.Completion →* AdeleRing (𝓞 F) F :=
    { toFun := fun x => (a x, 1)
      map_one' := by
        change (a 1, (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) = (1, 1)
        refine Prod.ext ?_ ?_
        · funext w
          change a 1 w = (1 : w.Completion)
          by_cases hw : w = v
          · subst w
            simp [a]
          · simp [a, Function.update_of_ne hw]
        · rfl
      map_mul' x y := by
        apply Prod.ext _ (by change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) = 1 * 1; simp)
        funext w
        change a (x * y) w = a x w * a y w
        by_cases hw : w = v
        · subst w
          simp [a]
        · simp [a, Function.update_of_ne hw] }
  have ha : Continuous a := by
    apply continuous_pi
    intro w
    by_cases hw : w = v
    · subst w
      have he : (fun x : v.Completion => a x v) = id := by funext x; simp [a]
      rw [he]
      exact continuous_id
    · apply (continuous_const (y := (1 : w.Completion))).congr
      intro x
      simp [a, Function.update_of_ne hw]
  have hf : Continuous f := ha.prodMk continuous_const
  exact ⟨Units.map f, hf.units_map f⟩

def infiniteLocalUnitaryCharacter (χ : PontryaginDual (IdeleClass F)) (v : InfinitePlace F) :
    v.Completionˣ →ₜ* ℂ :=
  let q : Idele F →ₜ* IdeleClass F := ⟨ideleClassMap F, ideleClassMap_continuous F⟩
  let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  (j.comp χ).comp (q.comp (singleInfiniteIdele F v))

@[simp] theorem infiniteLocalUnitaryCharacter_norm (χ : PontryaginDual (IdeleClass F))
    (v : InfinitePlace F) (x : v.Completionˣ) :
    ‖infiniteLocalUnitaryCharacter F χ v x‖ = 1 :=
  Circle.norm_coe _

def realInfiniteLocalCharacter (χ : PontryaginDual (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsReal) : ℝˣ →ₜ* ℂ :=
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
  let i : ℝˣ →ₜ* v.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.units_map _⟩
  (infiniteLocalUnitaryCharacter F χ v).comp i

def complexInfiniteLocalCharacter (χ : PontryaginDual (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsComplex) : ℂˣ →ₜ* ℂ :=
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  let i : ℂˣ →ₜ* v.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv).symm.continuous.units_map _⟩
  (infiniteLocalUnitaryCharacter F χ v).comp i

theorem realInfiniteLocalCharacter_parameters (χ : PontryaginDual (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsReal) :
    ∃! a : ℂ × Fin 2, a.1.re = 0 ∧ ∀ x : ℝˣ,
      realInfiniteLocalCharacter F χ v hv x =
        (‖(x : ℝ)‖ : ℂ) ^ a.1 * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.2.val := by
  exact existsUnique_realUnits_character_parameters _ (fun x => Circle.norm_coe _)

theorem complexInfiniteLocalCharacter_parameters (χ : PontryaginDual (IdeleClass F))
    (v : InfinitePlace F) (hv : v.IsComplex) :
    ∃! a : ℂ × ℤ, a.1.re = 0 ∧ ∀ x : ℂˣ,
      complexInfiniteLocalCharacter F χ v hv x =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a.1 * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ a.2 := by
  exact existsUnique_complexUnits_character_parameters _ (fun x => Circle.norm_coe _)

/-- Archimedean gamma parameters obtained from the actual unitary idele class character. -/
def ideleClassGammaParameters (χ : PontryaginDual (IdeleClass F)) : HeckeInfiniteParameters F := by
  classical
  let R (v : InfinitePlace F) (hv : v.IsReal) :=
    (realInfiniteLocalCharacter_parameters F χ v hv).exists.choose
  let C (v : InfinitePlace F) (hv : v.IsComplex) :=
    (complexInfiniteLocalCharacter_parameters F χ v hv).exists.choose
  exact
    { radial := fun v => if hv : v.IsReal then (R v hv).1.im
        else (C v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).1.im
      parity := fun v => if hv : v.IsReal then (R v hv).2 else 0
      angular := fun v => if hv : v.IsReal then 0
        else (C v (InfinitePlace.not_isReal_iff_isComplex.mp hv)).2 }

/-- Lemma 3.2.1.1, for actual unitary idele class characters and the
local gamma factors determined by their Archimedean parameters. -/
theorem ideleClass_completedHeckeEulerProduct_uniform
    (χ : PontryaginDual (IdeleClass F)) (K : Set ℂ) (hK : IsCompact K)
    (h : ∀ s ∈ K, 1 < s.re) :
    let c := heckeEulerCoefficient F χ (chosenFiniteUniformizer F)
    let A := heckeInfiniteGamma F (ideleClassGammaParameters F χ)
    SummableUniformlyOn (fun v s => ‖heckeEulerFactor F c v s - 1‖) K ∧
    TendstoUniformlyOn
      (fun S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) => fun s =>
        A s * ∏ v ∈ S, heckeEulerFactor F c v s)
      (fun s => A s * ∏' v, heckeEulerFactor F c v s) Filter.atTop K :=
  completedHeckeEulerProduct_uniform F χ (chosenFiniteUniformizer F)
    (ideleClassGammaParameters F χ) K hK h

end
end Masullo
