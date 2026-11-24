import CoordinatePlaneProductTests

open Set
open scoped SchwartzMap

namespace Masullo

noncomputable section

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem schwartzProduct_bound (φ : 𝓢(E, ℂ)) (p : ℕ × ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (g : 𝓢(V, ℂ)) (x : E × V),
      ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun z : E × V => φ z.1 * g z.2) x‖ ≤
        C * s.sup (schwartzSeminormFamily ℂ V ℂ) g := by
  obtain ⟨k, n⟩ := p
  let s := Finset.Iic (k, n)
  let S (g : 𝓢(V, ℂ)) := s.sup (schwartzSeminormFamily ℂ V ℂ) g
  let C (i : ℕ) := SchwartzMap.seminorm ℂ k i φ + SchwartzMap.seminorm ℂ 0 i φ
  refine ⟨s, ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i,
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (add_nonneg (apply_nonneg ..) (apply_nonneg ..)),
    fun g x => ?_⟩
  have hs {j l : ℕ} (hj : j ≤ k) (hl : l ≤ n) : SchwartzMap.seminorm ℂ j l g ≤ S g :=
    show schwartzSeminormFamily ℂ V ℂ (j, l) g ≤ S g from
      (Finset.le_sup (f := schwartzSeminormFamily ℂ V ℂ)
        (show (j, l) ∈ s from Finset.mem_Iic.mpr (Prod.le_def.mpr ⟨hj, hl⟩))) g
  have hw : ‖x‖ ^ k ≤ ‖x.1‖ ^ k + ‖x.2‖ ^ k := by
    change (max ‖x.1‖ ‖x.2‖) ^ k ≤ _
    rcases le_total ‖x.1‖ ‖x.2‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
  refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_separated_mul_le φ.smooth' g.smooth' x n)
    (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  let A := ‖iteratedFDeriv ℝ i φ x.1‖
  let B := ‖iteratedFDeriv ℝ (n - i) g x.2‖
  have hA : A ≤ SchwartzMap.seminorm ℂ 0 i φ :=
    SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ i x.1
  have hAk : ‖x.1‖ ^ k * A ≤ SchwartzMap.seminorm ℂ k i φ :=
    SchwartzMap.le_seminorm ℂ k i φ x.1
  have hB : B ≤ S g :=
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g (n - i) x.2).trans (hs (Nat.zero_le _) (Nat.sub_le ..))
  have hBk : ‖x.2‖ ^ k * B ≤ S g :=
    (SchwartzMap.le_seminorm ℂ k (n - i) g x.2).trans (hs le_rfl (Nat.sub_le ..))
  have h : ‖x‖ ^ k * (A * B) ≤ C i * S g := calc
    _ ≤ (‖x.1‖ ^ k + ‖x.2‖ ^ k) * (A * B) := mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (‖x.1‖ ^ k * A) * B + A * (‖x.2‖ ^ k * B) := by ring
    _ ≤ SchwartzMap.seminorm ℂ k i φ * S g + SchwartzMap.seminorm ℂ 0 i φ * S g :=
      add_le_add (mul_le_mul hAk hB (by positivity) (apply_nonneg ..))
        (mul_le_mul hA hBk (by positivity) (apply_nonneg ..))
    _ = _ := (add_mul _ _ _).symm
  calc
    _ = (n.choose i : ℝ) * (‖x‖ ^ k * (A * B)) := by
      change ‖x‖ ^ k * ((n.choose i : ℝ) * A * B) = _
      ring
    _ ≤ (n.choose i : ℝ) * (C i * S g) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

/-- With one factor fixed, the separated product is a continuous linear map
into the Schwartz space on the product. -/
def schwartzProductLeft (φ : 𝓢(E, ℂ)) : 𝓢(V, ℂ) →L[ℂ] 𝓢(E × V, ℂ) :=
  SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun g x => φ x.1 * g x.2)
    (fun _ _ _ => mul_add _ _ _)
    (fun a g x => by change _ * (a * _) = a * (_ * _); rw [mul_left_comm])
    (fun g => (φ.smooth'.comp contDiff_fst).mul (g.smooth'.comp contDiff_snd))
    (schwartzProduct_bound φ)

@[simp] theorem schwartzProductLeft_apply (φ : 𝓢(E, ℂ)) (g : 𝓢(V, ℂ)) (x : E × V) :
    schwartzProductLeft φ g x = φ x.1 * g x.2 := rfl

/-- The separated product is continuous in the other factor as well. -/
def schwartzProductRight (g : 𝓢(V, ℂ)) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E × V, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.prodComm ℝ E V).toContinuousLinearEquiv).comp (schwartzProductLeft g)

@[simp] theorem schwartzProductRight_apply (g : 𝓢(V, ℂ)) (φ : 𝓢(E, ℂ)) (x : E × V) :
    schwartzProductRight g φ x = φ x.1 * g x.2 := mul_comm _ _

/-- Local classification in each variable determines the product pairing
up to the value at the product of the two reference tests. -/
theorem schwartzProduct_eigen_eval
    {I J : Type*}
    (A : I → 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ)) (B : J → 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ))
    (χ : I → ℂ) (ψ : J → ℂ)
    (r : 𝓢(E, ℂ)) (s : 𝓢(V, ℂ)) (L : StrongDual ℂ 𝓢(E, ℂ)) (M : StrongDual ℂ 𝓢(V, ℂ))
    (hL : ∀ U : StrongDual ℂ 𝓢(E, ℂ), (∀ i f, U (A i f) = χ i * U f) →
      ∀ f, U f = U r * L f)
    (hM : ∀ U : StrongDual ℂ 𝓢(V, ℂ), (∀ j g, U (B j g) = ψ j * U g) →
      ∀ g, U g = U s * M g)
    (T : StrongDual ℂ 𝓢(E × V, ℂ))
    (hE : ∀ i f g, T (schwartzProductLeft (A i f) g) = χ i * T (schwartzProductLeft f g))
    (hV : ∀ j g, T (schwartzProductLeft r (B j g)) = ψ j * T (schwartzProductLeft r g))
    (f : 𝓢(E, ℂ)) (g : 𝓢(V, ℂ)) :
    T (schwartzProductLeft f g) = T (schwartzProductLeft r s) * (L f * M g) := by
  have he (h : 𝓢(E, ℂ)) : schwartzProductRight g h = schwartzProductLeft h g := by
    ext p
    rw [schwartzProductRight_apply, schwartzProductLeft_apply]
  let U := T.comp (schwartzProductRight g)
  have hU (i : I) (x : 𝓢(E, ℂ)) : U (A i x) = χ i * U x := by
    change T (schwartzProductRight g (A i x)) = χ i * T (schwartzProductRight g x)
    simpa only [he] using hE i x g
  have hfirst : T (schwartzProductLeft f g) = T (schwartzProductLeft r g) * L f := by
    simpa only [U, ContinuousLinearMap.comp_apply, he] using hL U hU f
  have hsecond : T (schwartzProductLeft r g) = T (schwartzProductLeft r s) * M g :=
    hM (T.comp (schwartzProductLeft r)) hV g
  rw [hfirst, hsecond, mul_assoc, mul_comm (M g)]

end
end Masullo
