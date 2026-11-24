import ComplexArchimedeanZeta
import PointTemperedDistribution
import Mathlib.LinearAlgebra.Multilinear.Basis

open Function Set Topology
open scoped ContDiff Distributions SchwartzMap

namespace Masullo

noncomputable section

private abbrev S := 𝓢(ℂ, ℂ)

private def atZero : S →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ 0).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℂ ℂ)

/-- Evaluate a mixed Wirtinger derivative at the origin. -/
def complexSchwartzPointJet (a b : ℕ) : S →L[ℂ] ℂ :=
  atZero.comp ((complexWirtingerZ ^ a) * (complexWirtingerBar ^ b))

private theorem jet_apply_Z (a b : ℕ) (f : S) :
    complexSchwartzPointJet a b (complexWirtingerZ f) = complexSchwartzPointJet (a+1) b f := by
  have h : ((complexWirtingerZ ^ a) * (complexWirtingerBar ^ b)) * complexWirtingerZ =
      (complexWirtingerZ ^ (a+1)) * (complexWirtingerBar ^ b) := by
    rw [mul_assoc, (complexWirtinger_commute.pow_right b).eq.symm, ← mul_assoc, ← pow_succ]
  change atZero ((((complexWirtingerZ ^ a) * (complexWirtingerBar ^ b)) * complexWirtingerZ) f) = _
  rw [h]
  rfl

private theorem jet_apply_Bar (a b : ℕ) (f : S) :
    complexSchwartzPointJet a b (complexWirtingerBar f) = complexSchwartzPointJet a (b+1) f := by
  change atZero ((((complexWirtingerZ ^ a) * (complexWirtingerBar ^ b)) * complexWirtingerBar) f) =
    atZero (((complexWirtingerZ ^ a) * (complexWirtingerBar ^ (b+1))) f)
  rw [mul_assoc, pow_succ]

private theorem complexPartial_one :
    complexPartial 1 = complexWirtingerZ + complexWirtingerBar := by
  unfold complexWirtingerZ complexWirtingerBar
  module

private theorem complexPartial_I :
    complexPartial Complex.I = Complex.I • (complexWirtingerZ - complexWirtingerBar) := by
  have he : complexWirtingerZ - complexWirtingerBar = (-Complex.I) • complexPartial Complex.I := by
    unfold complexWirtingerZ complexWirtingerBar
    module
  rw [he, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

/-- All real Fréchet jets through order N vanish exactly when the mixed
Wirtinger jets through total degree N vanish. -/
theorem complexSchwartzPointJet_vanishing_iff (N : ℕ) (f : S) :
    (∀ a b : ℕ, a + b ≤ N → complexSchwartzPointJet a b f = 0) ↔
      (∀ k ≤ N, iteratedFDeriv ℝ k (f : ℂ → ℂ) 0 = 0) := by
  constructor
  · intro hf k hk
    induction k generalizing f N with
    | zero =>
      ext w
      rw [iteratedFDeriv_zero_apply]
      have h := hf 0 0 (by omega)
      simpa [complexSchwartzPointJet, atZero] using h
    | succ k ih =>
      have hZ (a b : ℕ) (hab : a + b ≤ k) :
          complexSchwartzPointJet a b (complexWirtingerZ f) = 0 :=
        (jet_apply_Z a b f).trans (hf (a+1) b (by omega))
      have hB (a b : ℕ) (hab : a + b ≤ k) :
          complexSchwartzPointJet a b (complexWirtingerBar f) = 0 :=
        (jet_apply_Bar a b f).trans (hf a (b+1) (by omega))
      have h₁ : iteratedFDeriv ℝ k (complexPartial 1 f : ℂ → ℂ) 0 = 0 := by
        apply ih (N := k)
        · intro a b hb
          rw [complexPartial_one, add_apply, map_add, hZ _ _ hb, hB _ _ hb, add_zero]
        · exact le_rfl
      have hI : iteratedFDeriv ℝ k (complexPartial Complex.I f : ℂ → ℂ) 0 = 0 := by
        apply ih (N := k)
        · intro a b hb
          rw [complexPartial_I, smul_apply, sub_apply, map_smul, map_sub,
            hZ _ _ hb, hB _ _ hb, sub_self, smul_zero]
        · exact le_rfl
      apply ContinuousMultilinearMap.toMultilinearMap_injective
      apply Module.Basis.ext_multilinear (fun _ ↦ Complex.basisOneI)
      intro w
      let u : Fin (k+1) → ℂ := fun j ↦ Complex.basisOneI (w j)
      change iteratedFDeriv ℝ (k+1) f 0 u = 0
      rw [← Fin.snoc_init_self u, ← iteratedFDeriv_complexPartial]
      have he : u (Fin.last k) = 1 ∨ u (Fin.last k) = Complex.I := by
        dsimp [u]
        generalize w (Fin.last k) = j
        fin_cases j <;> simp
      rcases he with h | h
      · rw [h, h₁]; rfl
      · rw [h, hI]; rfl
  · intro hf a b hab
    have h := complexAngularPolynomial_coeff_wirtinger (a+b) a (by omega) f 0
    rw [hf _ hab, show a + b - a = b by omega] at h
    rw [complexAngularPolynomial_zero, Polynomial.coeff_zero] at h
    have hn : ((a+b).choose a : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_ne_zero (show a ≤ a+b by omega))
    have he := (mul_eq_zero.mp h.symm).resolve_left hn
    exact he

private theorem norm_jet_partial_le (k : ℕ) (f : S) (v : ℂ) (hv : ‖v‖ = 1) :
    ‖iteratedFDeriv ℝ k (complexPartial v f : ℂ → ℂ) 0‖ ≤
      ‖iteratedFDeriv ℝ (k+1) f 0‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro w
  rw [iteratedFDeriv_complexPartial]
  have he := (iteratedFDeriv ℝ (k+1) f 0).le_opNorm (Fin.snoc w v)
  rw [Fin.prod_univ_castSucc] at he
  simpa only [Fin.snoc_castSucc, Fin.snoc_last, hv, mul_one] using he

private theorem norm_jet_wirtinger_le (k : ℕ) (f : S) :
    ‖iteratedFDeriv ℝ k (complexWirtingerZ f : ℂ → ℂ) 0‖ ≤ ‖iteratedFDeriv ℝ (k+1) f 0‖ ∧
    ‖iteratedFDeriv ℝ k (complexWirtingerBar f : ℂ → ℂ) 0‖ ≤ ‖iteratedFDeriv ℝ (k+1) f 0‖ := by
  let A := complexPartial 1 f
  let B := complexPartial Complex.I f
  let D := ‖iteratedFDeriv ℝ (k+1) f 0‖
  have hA : ‖iteratedFDeriv ℝ k (A : ℂ → ℂ) 0‖ ≤ D := norm_jet_partial_le k f _ norm_one
  have hB : ‖iteratedFDeriv ℝ k (B : ℂ → ℂ) 0‖ ≤ D :=
    norm_jet_partial_le k f _ Complex.norm_I
  have htop : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have hAs : ContDiffAt ℝ (k : ℕ∞ω) (A : ℂ → ℂ) 0 := (A.smooth'.of_le htop).contDiffAt
  have hBs : ContDiffAt ℝ (k : ℕ∞ω) (B : ℂ → ℂ) 0 := (B.smooth'.of_le htop).contDiffAt
  have hBIs : ContDiffAt ℝ (k : ℕ∞ω) (Complex.I • (B : ℂ → ℂ)) 0 := by
    change ContDiffAt ℝ (k : ℕ∞ω) (fun y ↦ Complex.I • B.toFun y) 0
    exact hBs.const_smul Complex.I
  constructor
  · change ‖iteratedFDeriv ℝ k ((1/2 : ℂ) • ((A : ℂ → ℂ) - Complex.I • (B : ℂ → ℂ))) 0‖ ≤ D
    have hd : ContDiffAt ℝ (k : ℕ∞ω) ((A : ℂ → ℂ) - Complex.I • (B : ℂ → ℂ)) 0 := hAs.sub hBIs
    rw [iteratedFDeriv_const_smul_apply hd, iteratedFDeriv_sub_apply hAs hBIs,
      iteratedFDeriv_const_smul_apply hBs, norm_smul]
    have h := norm_sub_le (iteratedFDeriv ℝ k (A : ℂ → ℂ) 0)
      (Complex.I • iteratedFDeriv ℝ k (B : ℂ → ℂ) 0)
    rw [norm_smul, Complex.norm_I, one_mul] at h
    rw [norm_div, norm_one, Complex.norm_ofNat]
    linarith
  · change ‖iteratedFDeriv ℝ k ((1/2 : ℂ) • ((A : ℂ → ℂ) + Complex.I • (B : ℂ → ℂ))) 0‖ ≤ D
    have hd : ContDiffAt ℝ (k : ℕ∞ω) ((A : ℂ → ℂ) + Complex.I • (B : ℂ → ℂ)) 0 := hAs.add hBIs
    rw [iteratedFDeriv_const_smul_apply hd, iteratedFDeriv_add_apply hAs hBIs,
      iteratedFDeriv_const_smul_apply hBs, norm_smul]
    have h := norm_add_le (iteratedFDeriv ℝ k (A : ℂ → ℂ) 0)
      (Complex.I • iteratedFDeriv ℝ k (B : ℂ → ℂ) 0)
    rw [norm_smul, Complex.norm_I, one_mul] at h
    rw [norm_div, norm_one, Complex.norm_ofNat]
    linarith

/-- A mixed Wirtinger jet is bounded by the operator norm of the real
Fréchet derivative of the same total order. -/
theorem norm_complexSchwartzPointJet_le (a b : ℕ) (f : S) :
    ‖complexSchwartzPointJet a b f‖ ≤ ‖iteratedFDeriv ℝ (a+b) f 0‖ := by
  induction a generalizing b f with
  | zero =>
    induction b generalizing f with
    | zero =>
      change ‖f 0‖ ≤ ‖iteratedFDeriv ℝ (0+0) f 0‖
      rw [Nat.zero_add, norm_iteratedFDeriv_zero]
    | succ b ih =>
      rw [← jet_apply_Bar]
      exact (ih _).trans (by
        rw [Nat.zero_add, Nat.zero_add]
        exact (norm_jet_wirtinger_le b f).2)
  | succ a ih =>
    rw [← jet_apply_Z]
    exact (ih b _).trans (by
      rw [show a + 1 + b = a + b + 1 by omega]
      exact (norm_jet_wirtinger_le (a+b) f).1)

end
end Masullo
