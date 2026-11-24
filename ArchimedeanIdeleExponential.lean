import ArchimedeanLogarithms
import IdeleOneParameter

open Function NumberField
open scoped NumberField

namespace Masullo

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

private abbrev Arch := mixedEmbedding.mixedSpace F

/-- Insert mixed archimedean units as ideles with finite component one. -/
def mixedArchUnitIdele : (Arch F)ˣ →* Idele F :=
  Units.map {
    toFun x := ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x, 1)
    map_one' := by
      apply Prod.ext
      · exact map_one _
      · rfl
    map_mul' x y := by
      apply Prod.ext
      · exact map_mul _ _ _
      · exact (mul_one _).symm }

def mixedExp (x : Arch F) : Arch F :=
  (fun v => Real.exp (x.1 v), fun v => Complex.exp (x.2 v))

omit [NumberField F] in
private theorem mixedExp_continuous : Continuous (mixedExp F) :=
  (continuous_pi fun v => Real.continuous_exp.comp ((continuous_apply v).comp continuous_fst)).prodMk
    (continuous_pi fun v => Complex.continuous_exp.comp ((continuous_apply v).comp continuous_snd))

omit [NumberField F] in
private theorem mixedExp_zero : mixedExp F 0 = 1 := by
  apply Prod.ext
  · funext v
    exact Real.exp_zero
  · funext v
    exact Complex.exp_zero

omit [NumberField F] in
private theorem mixedExp_add (x y : Arch F) : mixedExp F (x + y) = mixedExp F x * mixedExp F y := by
  apply Prod.ext
  · funext v
    exact Real.exp_add _ _
  · funext v
    exact Complex.exp_add _ _

def mixedExpUnits : Multiplicative (Arch F) →* (Arch F)ˣ where
  toFun x := {
    val := mixedExp F x.toAdd
    inv := mixedExp F (-x.toAdd)
    val_inv := by rw [← mixedExp_add, add_neg_cancel, mixedExp_zero]
    inv_val := by rw [← mixedExp_add, neg_add_cancel, mixedExp_zero] }
  map_one' := Units.ext (mixedExp_zero F)
  map_mul' x y := Units.ext (mixedExp_add F x.toAdd y.toAdd)

def mixedArchExpIdele : Multiplicative (Arch F) →* Idele F :=
  (mixedArchUnitIdele F).comp (mixedExpUnits F)

theorem mixedArchExpIdele_continuous : Continuous (mixedArchExpIdele F) := by
  apply Units.continuous_iff.mpr
  have he : Continuous ((infiniteAdeleMixedHomeomorph F).symm : Arch F → InfiniteAdeleRing F) :=
    (infiniteAdeleMixedHomeomorph F).symm.continuous
  have hp := he.comp (mixedExp_continuous F)
  exact ⟨(hp.comp continuous_toAdd).prodMk continuous_const,
    ((hp.comp continuous_neg).comp continuous_toAdd).prodMk continuous_const⟩

private theorem real_oneParameter_exp (c : Multiplicative ℝ →* ℝˣ)
    (hc : Continuous (fun t : ℝ => (c (Multiplicative.ofAdd t) : ℝ))) :
    ∃ v : ℝ, ∀ t : ℝ, (c (Multiplicative.ofAdd t) : ℝ) = Real.exp (t * v) := by
  let g (t : ℝ) := (c (Multiplicative.ofAdd t) : ℝ)
  have hmul (x y : ℝ) : g (x + y) = g x * g y := by
    change (c (Multiplicative.ofAdd x * Multiplicative.ofAdd y) : ℝ) = _
    rw [map_mul]
    rfl
  have hpos (t : ℝ) : 0 < g t := by
    have ht : t = t / 2 + t / 2 := by ring
    nth_rw 1 [ht]
    rw [hmul, ← sq]
    exact sq_pos_of_ne_zero (Units.ne_zero _)
  let l : ℝ →+ ℝ :=
    { toFun := fun t => Real.log (g t)
      map_zero' := by simp [g]
      map_add' := fun x y => by rw [hmul, Real.log_mul (hpos x).ne' (hpos y).ne'] }
  let L := l.toRealLinearMap (hc.log fun t => (hpos t).ne')
  refine ⟨L 1, fun t => ?_⟩
  have h : L t = t * L 1 := by simpa [smul_eq_mul] using L.map_smul t (1 : ℝ)
  change Real.log (g t) = _ at h
  rw [← h, Real.exp_log (hpos t)]

/-- Every idele direction supported at the infinite places is the exponential
of a velocity in the mixed archimedean vector space. -/
theorem exists_mixedArchExpIdele_direction
    (a : Multiplicative ℝ →ₜ* Idele F)
    (ha : ∀ t, a t ∈ infinitePlaceIdeles F) :
    ∃ v : Arch F, ∀ t : ℝ, a (Multiplicative.ofAdd t) =
      mixedArchExpIdele F (Multiplicative.ofAdd (t • v)) := by
  let A := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let j : Idele F →* (Arch F)ˣ :=
    Units.map (A.toMonoidHom.comp (MonoidHom.fst _ _))
  have hj : Continuous (fun t : ℝ => (j (a (Multiplicative.ofAdd t))).val) :=
    (infiniteAdeleMixedHomeomorph F).continuous.comp
      (continuous_fst.comp ((Units.continuous_val.comp a.continuous).comp continuous_ofAdd))
  let jR (i : {w : InfinitePlace F // InfinitePlace.IsReal w}) : Multiplicative ℝ →* ℝˣ :=
    (Units.map ((Pi.evalMonoidHom _ i).comp (MonoidHom.fst _ _))).comp (j.comp a.toMonoidHom)
  let jC (i : {w : InfinitePlace F // InfinitePlace.IsComplex w}) : Multiplicative ℝ →* ℂˣ :=
    (Units.map ((Pi.evalMonoidHom _ i).comp (MonoidHom.snd _ _))).comp (j.comp a.toMonoidHom)
  choose vR hvR using fun i => real_oneParameter_exp (jR i)
    ((continuous_apply i).comp hj.fst)
  choose vC hvC _ using fun i => complex_oneParameter_exp (jC i)
    ((continuous_apply i).comp hj.snd)
  refine ⟨(vR, vC), fun t => ?_⟩
  apply Units.ext
  apply Prod.ext
  · apply A.injective
    change (j (a (Multiplicative.ofAdd t))).val = A
      (A.symm (mixedExp F (t • (vR, vC))))
    rw [A.apply_symm_apply]
    apply Prod.ext
    · funext i
      exact hvR i t
    · funext i
      change (jC i (Multiplicative.ofAdd t) : ℂ) = Complex.exp (t • vC i)
      rw [Complex.real_smul, mul_comm (t : ℂ) (vC i)]
      exact hvC i t
  · exact finite_component_eq_one_of_mem_infinitePlaceIdeles F (ha _)

/-- A line whose exponential is identically the identity has zero mixed
archimedean velocity. -/
theorem mixedArchExpIdele_direction_eq_one {x : Arch F}
    (h : ∀ t : ℝ, mixedArchExpIdele F (Multiplicative.ofAdd (t • x)) = 1) : x = 0 := by
  let A := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have he (t : ℝ) : mixedExp F (t • x) = 1 := by
    have ht := congrArg (fun a : Idele F => A a.val.1) (h t)
    change A (A.symm (mixedExp F (t • x))) = A 1 at ht
    simpa only [A.apply_symm_apply, map_one] using ht
  apply Prod.ext
  · funext i
    have hi := congrArg (fun y : Arch F => y.1 i) (he 1)
    rw [one_smul] at hi
    exact Real.exp_injective (hi.trans Real.exp_zero.symm)
  · funext i
    let g (t : ℝ) := Complex.exp (x.2 i * (t : ℂ))
    have hg : g = fun _ => 1 := by
      funext t
      have ht := congrArg (fun y : Arch F => y.2 i) (he t)
      change Complex.exp (t • x.2 i) = 1 at ht
      rw [Complex.real_smul, mul_comm] at ht
      exact ht
    have hd : HasDerivAt g (x.2 i) 0 := by
      have hb : HasDerivAt (fun z : ℂ => Complex.exp (x.2 i * z)) (x.2 i) (0 : ℂ) := by
        simpa [mul_comm] using ((hasDerivAt_id' (0 : ℂ)).const_mul (x.2 i)).cexp
      exact hb.comp_ofReal
    change x.2 i = 0
    rw [hg] at hd
    simpa using hd.deriv.symm

end
end Masullo
