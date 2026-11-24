import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Metrizable.Urysohn

open Filter Function MeasureTheory Set TopologicalSpace Topology
open scoped ENNReal InnerProductSpace

namespace Masullo

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (ν : Measure G) [ν.IsHaarMeasure]

abbrev HaarL2 := Lp ℂ 2 ν

private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
private instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩

/-- The regular representation acts by the inverse translation on a representative. -/
def leftRegularLinearIsometry (g : G) : HaarL2 ν →ₗᵢ[ℂ] HaarL2 ν where
  toFun f := DomMulAct.mk g⁻¹ • f
  map_add' := DomMulAct.smul_Lp_add _
  map_smul' := smul_comm _
  norm_map' := DomMulAct.norm_smul_Lp _

/-- Unitary automorphisms underlying the continuous left regular action. -/
def leftRegularUnitary (g : G) : HaarL2 ν ≃ₗᵢ[ℂ] HaarL2 ν where
  toLinearEquiv := {
    (leftRegularLinearIsometry ν g).toLinearMap with
    invFun := leftRegularLinearIsometry ν g⁻¹
    left_inv := by
      intro f
      change DomMulAct.mk (g⁻¹)⁻¹ • (DomMulAct.mk g⁻¹ • f) = _
      rw [smul_smul, ← DomMulAct.mk_mul, inv_inv, inv_mul_cancel, DomMulAct.mk_one, one_smul]
    right_inv := by
      intro f
      change DomMulAct.mk g⁻¹ • (DomMulAct.mk (g⁻¹)⁻¹ • f) = _
      rw [smul_smul, ← DomMulAct.mk_mul, inv_inv, mul_inv_cancel, DomMulAct.mk_one, one_smul] }
  norm_map' := (leftRegularLinearIsometry ν g).norm_map'

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem leftRegularUnitary_ae (g : G) (f : HaarL2 ν) :
    leftRegularUnitary ν g f =ᵐ[ν] (fun x => f (g⁻¹ * x)) :=
  DomMulAct.smul_Lp_ae_eq _ _

omit [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem leftRegularUnitary_mul (g h : G) (f : HaarL2 ν) :
    leftRegularUnitary ν (g * h) f = leftRegularUnitary ν g (leftRegularUnitary ν h f) := by
  change DomMulAct.mk (g * h)⁻¹ • f = DomMulAct.mk g⁻¹ • (DomMulAct.mk h⁻¹ • f)
  rw [mul_inv_rev, DomMulAct.mk_mul, smul_smul]

omit [T2Space G] in
theorem leftRegularUnitary_continuous :
    Continuous (fun p : G × HaarL2 ν => leftRegularUnitary ν p.1 p.2) := by
  change Continuous (fun p : G × HaarL2 ν => DomMulAct.mk p.1⁻¹ • p.2)
  exact ((DomMulAct.continuous_mk.comp continuous_fst.inv)).smul continuous_snd

private theorem haarL2_compactSupport_dense :
    Dense {w : HaarL2 ν | ∃ (f : G → ℂ) (hf : MemLp f 2 ν),
      Continuous f ∧ HasCompactSupport f ∧ w = hf.toLp f} := by
  rw [EMetric.dense_iff]
  intro w ε hε
  obtain ⟨r, hr₀, hrε⟩ := exists_between hε
  obtain ⟨f, hfSupp, hDist, hfCont, hf⟩ :=
    MemLp.exists_hasCompactSupport_eLpNorm_sub_le (by simp) (Lp.memLp w) hr₀.ne'
  refine ⟨hf.toLp f, ?_, ⟨f, hf, hfCont, hfSupp, rfl⟩⟩
  change edist (hf.toLp f) w < ε
  rw [edist_comm, Lp.edist_def]
  have hEq : (fun x => w x - hf.toLp f x) =ᵐ[ν] (fun x => w x - f x) :=
    (hf.coeFn_toLp).mono fun x hx => congrArg (w x - ·) hx
  rw [show (⇑w - ⇑(hf.toLp f)) = (fun x => w x - hf.toLp f x) from rfl, eLpNorm_congr_ae hEq]
  exact hDist.trans_lt hrε

set_option maxHeartbeats 800000 in
/-- Lemma 4.3.1.5. The Hilbert space is separable, and inverse left
translation gives the unique continuous unitary extension of the action
on compactly supported continuous functions. Any continuous real section
gives a strongly continuous unitary one-parameter group. -/
theorem leftRegularRepresentation (τ : Multiplicative ℝ →* G) (hτ : Continuous τ) :
    SeparableSpace (HaarL2 ν) ∧
    (∀ g : G, ∀ f h : HaarL2 ν, ⟪leftRegularUnitary ν g f, leftRegularUnitary ν g h⟫_ℂ = ⟪f,h⟫_ℂ) ∧
    (∀ (T : G → HaarL2 ν → HaarL2 ν),
      Continuous (fun z : G × HaarL2 ν => T z.1 z.2) →
      (∀ (g : G) (f : G → ℂ) (hf : MemLp f 2 ν), Continuous f → HasCompactSupport f →
        T g (hf.toLp f) =ᵐ[ν] (fun x => f (g⁻¹ * x))) →
      T = fun g f => leftRegularUnitary ν g f) ∧
    Continuous (fun p : Multiplicative ℝ × HaarL2 ν =>
      leftRegularUnitary ν (τ p.1) p.2) ∧
    (∀ s t : Multiplicative ℝ, ∀ f : HaarL2 ν,
      leftRegularUnitary ν (τ (s * t)) f =
        leftRegularUnitary ν (τ s) (leftRegularUnitary ν (τ t) f)) := by
  refine ⟨inferInstance, fun g f h => (leftRegularUnitary ν g).inner_map_map f h, ?_, ?_,
    fun s t f => ?_⟩
  · intro T hT hbase
    funext g
    apply Continuous.ext_on (haarL2_compactSupport_dense ν)
      (hT.comp (continuous_const.prodMk continuous_id))
      ((leftRegularUnitary ν g).continuous)
    intro w hw
    obtain ⟨f, hf, hc, hs, rfl⟩ := hw
    have h₁ := hbase g f hf hc hs
    have h₂ := (leftRegularUnitary_ae ν g (hf.toLp f)).trans
      ((measurePreserving_smul g⁻¹ ν).quasiMeasurePreserving.ae_eq hf.coeFn_toLp)
    exact Lp.ext (h₁.trans h₂.symm)
  · let ψ : Multiplicative ℝ × HaarL2 ν → G × HaarL2 ν := fun p => (τ p.1, p.2)
    have hψ : Continuous ψ := (hτ.comp continuous_fst).prodMk continuous_snd
    let Ψ : G × HaarL2 ν → HaarL2 ν := fun p => leftRegularUnitary ν p.1 p.2
    have hΨ : Continuous Ψ := leftRegularUnitary_continuous ν
    change Continuous (Ψ ∘ ψ)
    exact hΨ.comp hψ
  · calc
      leftRegularUnitary ν (τ (s * t)) f = leftRegularUnitary ν (τ s * τ t) f :=
        congrArg (fun g : G => leftRegularUnitary ν g f) (map_mul τ s t)
      _ = leftRegularUnitary ν (τ s) (leftRegularUnitary ν (τ t) f) :=
        leftRegularUnitary_mul ν (τ s) (τ t) f

end

end Masullo
