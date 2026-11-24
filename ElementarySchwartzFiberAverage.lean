/-
Averaging on elementary quotients adapts RiemannMasullo
AppD_SchwartzBruhat/Sec1c.lean at a1d61084d11ef14e3119178113488c654be4da80
(Apache-2.0). See External/PROVENANCE.md and External/RiemannMasullo.LICENSE.
-/
import BruhatFourierSmooth
import ElementarySchwartzFiberMeasure

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace Masullo

noncomputable section

section Affine

variable {m n r : ℕ} {K : Type*} [AddCommGroup K] [TopologicalSpace K] [DiscreteTopology K] [Finite K]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "E" => ElementaryLCAModel m n r K
local notation "S" => ElementarySchwartz m n r K
local notation "X" => EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)

private theorem elementaryAffine_deriv (L : V →L[ℝ] X) (s : S) (v : V) (z : E) (u : V) :
    let g (w : V) := s (z + elementaryCoverHom (L w))
    DifferentiableAt ℝ g u ∧ fderiv ℝ g u v =
      elementarySchwartz_derivative (elementaryOneParameter (L v)) s
        (z + elementaryCoverHom (L u)) := by
  intro g
  obtain ⟨t, ht⟩ := elementaryCover_surjective z.2.2.1 z.2.2.2 z.1 z.2.1
  let w₀ : X := (z.1, t)
  have ht' : elementaryCover w₀ z.2.2.1 z.2.2.2 = z := ht
  let h (w : X) := s (elementaryCover w z.2.2.1 z.2.2.2)
  have hs : ContDiff ℝ ∞ h := s.property.1 _ _
  have he (w : V) : z + elementaryCoverHom (L w) =
      elementaryCover (w₀ + L w) z.2.2.1 z.2.2.2 := by
    rw [elementaryCover_add, ht']
  have heq : g = h ∘ (fun w => w₀ + L w) := funext fun w => congrArg s.val (he w)
  have hAt := (hs.differentiable (by simp) (w₀ + L u)).hasFDerivAt.comp u
    (L.hasFDerivAt.const_add w₀)
  rw [heq]
  refine ⟨hAt.differentiableAt, ?_⟩
  rw [hAt.fderiv, ContinuousLinearMap.comp_apply, he,
    elementarySchwartz_derivative_apply]
  exact (elementaryOrbitDeriv_cover _ _ (fun _ => rfl) s _ _ _
    (hs.differentiable (by simp) _)).symm

end Affine

section Fibre

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [T2Space A] [MeasurableSpace A] [BorelSpace A]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

set_option maxHeartbeats 1200000 in
private theorem elementaryFibre_charts (e : ElementaryLCAPresentation A) (K : Subgroup A)
    (hK : IsClosed (K : Set A)) (ν : Measure K) [ν.IsHaarMeasure]
    (L : V →L[ℝ] EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
    let S := ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor
    let σ (v : V) := e.equiv.symm (Multiplicative.ofAdd (elementaryCoverHom (L v)))
    let Ψ (s : S) (y : A) (u : V) :=
      ∫ k : K, s (e.equiv (y * σ u * k.val)).toAdd ∂ν
    (∀ s y, ContDiff ℝ ∞ (Ψ s y)) ∧ ∀ (dirs : List V) (s : S), ∃ t : S, ∀ y u,
      iteratedFDeriv ℝ dirs.length (Ψ s y) u dirs.get = Ψ t y u := by
  intro S σ Ψ
  let F (y : A) (s : S) (u : V) (k : K) := s (e.equiv (y * σ u * k.val)).toAdd
  let D (s : S) (v : V) := elementarySchwartz_derivative (elementaryOneParameter (L v)) s
  have hd (y : A) (s : S) (u : V) (k : K) (v : V) :
      DifferentiableAt ℝ (fun w => F y s w k) u ∧
        fderiv ℝ (fun w => F y s w k) u v = F y (D s v) u k := by
    have he (w : V) : (e.equiv (y * σ w * k.val)).toAdd =
        (e.equiv (y * k.val)).toAdd + elementaryCoverHom (L w) := by
      rw [mul_right_comm y, map_mul]
      change (e.equiv (y * k.val) * e.equiv (e.equiv.symm _)).toAdd = _
      rw [e.equiv.apply_symm_apply]
      rfl
    simpa only [F, D, he] using elementaryAffine_deriv L s v (e.equiv (y * k.val)).toAdd u
  let hdom (s : S) := elementarySchwartz_fibre_integrable_dominated e K hK ν s
  have hcalc (y : A) : (∀ s : S, ContDiff ℝ ∞ (Ψ s y)) ∧
      ∀ s u v, fderiv ℝ (Ψ s y) u v = Ψ (D s v) y u := by
    apply integral_family_fderiv_locallyDominated ν (F y)
      (fun s u => (hdom s).1 (y * σ u))
      (fun s u k => (hd y s u k 0).1) D (fun s u k v => (hd y s u k v).2)
    intro s u
    obtain ⟨b, hb, hnear⟩ := (hdom s).2 (y * σ u)
    have hc : Continuous (fun v : V => y * σ v) :=
      continuous_const.mul (e.equiv.symm.continuous.comp (continuous_ofAdd.comp
        (elementaryCoverHom_continuous.comp L.continuous)))
    exact ⟨b, hb, (hc.tendsto u).eventually hnear⟩
  refine ⟨fun s y => (hcalc y).1 s, fun dirs => ?_⟩
  induction dirs using List.reverseRecOn with
  | nil => exact fun s => ⟨s, fun y u => by simp⟩
  | append_singleton dirs v ih =>
    intro s
    obtain ⟨t, ht⟩ := ih (D s v)
    refine ⟨t, fun y u => ?_⟩
    rw [iteratedFDeriv_append_singleton ((hcalc y).1 s),
      show (fun w => fderiv ℝ (Ψ s y) w v) = Ψ (D s v) y from funext fun w => (hcalc y).2 s w v]
    exact ht y u

variable {B : Type*} [CommGroup B] [TopologicalSpace B] [T2Space B]

set_option maxHeartbeats 1600000 in
/-- Haar averaging along the kernel of a continuous open surjection of
elementary groups gives an elementary Schwartz function on the quotient. -/
theorem elementarySchwartz_exists_fibreAverage (e : ElementaryLCAPresentation A)
    (d : ElementaryLCAPresentation B) (p : A →ₜ* B) (hpo : IsOpenMap p)
    (hps : Surjective p) (ν : Measure p.toMonoidHom.ker) [ν.IsHaarMeasure]
    (s : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor) :
    ∃ t : ElementarySchwartz d.realDim d.torusDim d.latticeRank d.finiteFactor,
      ∀ y : A, t (d.equiv (p y)).toAdd =
        ∫ k : p.toMonoidHom.ker, s (e.equiv (y * k.val)).toAdd ∂ν := by
  classical
  let E := ElementaryLCAModel e.realDim e.torusDim e.latticeRank e.finiteFactor
  let Y := ElementaryLCAModel d.realDim d.torusDim d.latticeRank d.finiteFactor
  let X := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let V := EuclideanSpace ℝ (Fin d.realDim) × EuclideanSpace ℝ (Fin d.torusDim)
  let K := p.toMonoidHom.ker
  have hK : IsClosed (K : Set A) := isClosed_singleton.preimage p.continuous
  let π : E →+ Y :=
    (d.equiv.toMonoidHom.comp (p.toMonoidHom.comp e.equiv.symm.toMonoidHom)).toAdditive
  have hc : Continuous π := d.equiv.continuous.comp (p.continuous.comp e.equiv.symm.continuous)
  have ho : IsOpenMap π := d.equiv.isOpenMap.comp (hpo.comp e.equiv.symm.isOpenMap)
  obtain ⟨L, hL, hcover⟩ := elementaryCoverHom_lift_of_open π hc ho
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hL)
  let R₁ : V →L[ℝ] X := ⟨R, R.continuous_of_finiteDimensional⟩
  let σ (u : V) := e.equiv.symm (Multiplicative.ofAdd (elementaryCoverHom (R₁ u)))
  have hσ (u : V) : p (σ u) = d.equiv.symm (Multiplicative.ofAdd (elementaryCoverHom u)) := by
    apply d.equiv.injective
    change Multiplicative.ofAdd (π (elementaryCoverHom (R₁ u))) = _
    rw [hcover, d.equiv.apply_symm_apply, show L (R₁ u) = u from DFunLike.congr_fun hR u]
  let avg (f : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor) (y : A) :=
    ∫ k : K, f (e.equiv (y * k.val)).toAdd ∂ν
  have havg (f : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor)
      {x y : A} (h : p x = p y) : avg f x = avg f y := by
    let k₀ : K := ⟨y⁻¹ * x, by change p (y⁻¹ * x) = 1; simp [h]⟩
    calc
      _ = ∫ k : K, f (e.equiv (y * (k₀ * k).val)).toAdd ∂ν := by
        apply integral_congr_ae
        exact .of_forall fun k => congrArg (fun z => f (e.equiv z).toAdd) (by dsimp [k₀]; group)
      _ = _ := integral_mul_left_eq_self (fun k : K => f (e.equiv (y * k.val)).toAdd) k₀
  let rep (y : Y) := Function.surjInv hps (d.equiv.symm (Multiplicative.ofAdd y))
  have hrep (y : Y) : p (rep y) = d.equiv.symm (Multiplicative.ofAdd y) :=
    Function.rightInverse_surjInv hps _
  let F (f : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor) (y : Y) :=
    avg f (rep y)
  have hF (f : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor) (y : A) :
      F f (d.equiv (p y)).toAdd = avg f y := by
    apply havg
    rw [hrep]
    exact d.equiv.symm_apply_apply _
  let y₀ (a : Fin d.latticeRank → ℤ) (b : d.finiteFactor) :=
    rep (elementaryCover (0 : V) a b)
  have hparam (u : V) (a : Fin d.latticeRank → ℤ) (b : d.finiteFactor) :
      (d.equiv (p (y₀ a b * σ u))).toAdd = elementaryCover u a b := by
    have he := elementaryCover_add (0 : V) u a b
    rw [zero_add] at he
    rw [map_mul, hσ, show p (y₀ a b) = _ from hrep _, map_mul,
      d.equiv.apply_symm_apply, d.equiv.apply_symm_apply]
    exact he.symm
  have hchart (f : ElementarySchwartz e.realDim e.torusDim e.latticeRank e.finiteFactor)
      (a : Fin d.latticeRank → ℤ) (b : d.finiteFactor) :
      (fun u : V => F f (elementaryCover u a b)) = fun u => avg f (y₀ a b * σ u) := by
    funext u
    rw [← hparam u a b, hF]
  obtain ⟨hs, hd⟩ := elementaryFibre_charts e K hK ν R₁
  obtain ⟨M, hM⟩ := elementary_fibreWeight_integrable e K hK ν
  obtain ⟨L₀, h₀⟩ := elementaryGrowth_hom π hc
  have hSchwartz : F s ∈ elementarySchwartzSubmodule d.realDim d.torusDim d.latticeRank d.finiteFactor := by
    refine ⟨fun a b => hchart s a b ▸ hs s (y₀ a b), fun i => ?_⟩
    let dirs : List V := (List.ofFn fun j => List.replicate (i.2.1 j) (EuclideanSpace.single j 1, 0)).flatten ++
      (List.ofFn fun j => List.replicate (i.2.2.1 j) (0, EuclideanSpace.single j 1)).flatten
    obtain ⟨s', hs'⟩ := hd dirs s
    obtain ⟨P, hP⟩ := linear_growth_monomial L₀.toLinearMap (Sum.elim i.1 i.2.2.2)
    obtain ⟨C, hC, hbound⟩ := elementarySchwartz_fibreDecay e P s'
    apply lt_of_le_of_lt (b := ENNReal.ofReal (C * M)) _ ENNReal.ofReal_lt_top
    refine iSup_le fun u => iSup_le fun a => iSup_le fun b => ?_
    let y := y₀ a b * σ u
    let W : ℂ := (∏ j, (u.1 j : ℂ) ^ i.1 j) * ∏ j, (a j : ℂ) ^ i.2.2.2 j
    have hpartial : elementaryPartial (F s) i.2.1 i.2.2.1 u a b = avg s' y := by
      change iteratedFDeriv ℝ dirs.length (fun w => F s (elementaryCover w a b)) u dirs.get = _
      rw [hchart]
      exact hs' (y₀ a b) u
    have hweight (k : K) : MvPolynomial.eval (elementaryGrowthVariables (e.equiv (y * k.val)).toAdd) P = W := by
      rw [elementaryGrowthVariables_eq, hP]
      have hk : p k.val = 1 := k.property
      have h : π (e.equiv (y * k.val)).toAdd = elementaryCover u a b := by
        change (d.equiv (p (e.equiv.symm (e.equiv (y * k.val))))).toAdd = _
        rw [e.equiv.symm_apply_apply, map_mul, hk, mul_one]
        exact hparam u a b
      have h' : L₀ (elementaryGrowth (e.equiv (y * k.val)).toAdd) =
          elementaryGrowth (elementaryCover u a b) := by rw [← h₀, h]
      change (∏ j, (L₀ (elementaryGrowth (e.equiv (y * k.val)).toAdd) j : ℂ) ^
        Sum.elim i.1 i.2.2.2 j) = W
      rw [h', Fintype.prod_sum_type]
      rfl
    let w (k : K) := ∏ j, (1 + (fibreCoordinate e (y * k.val) j)^2)⁻¹
    change ‖W * elementaryPartial (F s) i.2.1 i.2.2.1 u a b‖ₑ ≤ _
    rw [hpartial, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    change ‖W * ∫ k : K, s' (e.equiv (y * k.val)).toAdd ∂ν‖ ≤ C * M
    rw [← integral_const_mul]
    have hi := (elementarySchwartz_fibre_integrable_dominated e K hK ν s').1 y
    calc
      _ ≤ ∫ k : K, ‖W * s' (e.equiv (y * k.val)).toAdd‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ k : K, C * w k ∂ν :=
        integral_mono (hi.const_mul W).norm ((hM y).1.const_mul C) (fun k => by
          have h := hbound (y * k.val)
          dsimp only at h
          rwa [hweight k] at h)
      _ ≤ C * M := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hM y).2 hC
  exact ⟨⟨F s, hSchwartz⟩, hF s⟩

end Fibre
end
end Masullo
