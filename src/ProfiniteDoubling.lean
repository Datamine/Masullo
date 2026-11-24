import SubgroupDoubling
import Mathlib.GroupTheory.OrderOfElement

open Function Set Filter Topology
open scoped Classical Pointwise

namespace Masullo

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The symmetric compact open neighborhoods used during refinement. -/
structure OpenCompactNeighborhood (G : Type*) [Group G] [TopologicalSpace G] where
  set : Set G
  one_mem : 1 ∈ set
  open_set : IsOpen set
  compact_set : IsCompact set
  symmetric : set⁻¹ = set

/-- One refinement, with at most three translates of the smaller stage
covering the adjacent product. -/
def OpenCompactNeighborhood.Step (A B : OpenCompactNeighborhood G) : Prop :=
  B.set ⊆ A.set ∧
    ∃ t : Fin 3 → G, B.set * A.set ⊆ ⋃ i, t i • B.set

private def cyclicBand (K : Subgroup G) (x : G) (r : ℕ) : Set G :=
  ⋃ a : Set.Icc (-(r : ℤ)) (r : ℤ), x ^ a.val • (K : Set G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem cyclicBand_mem_iff (K : Subgroup G) (x : G) (r : ℕ) (y : G) :
    y ∈ cyclicBand K x r ↔ ∃ n : ℤ, -(r : ℤ) ≤ n ∧ n ≤ (r : ℤ) ∧
      ∃ k ∈ K, x ^ n * k = y := by
  constructor
  · intro h
    obtain ⟨⟨n, hn₁, hn₂⟩, z, hz, h⟩ := mem_iUnion.mp h
    exact ⟨n, hn₁, hn₂, z, hz, h⟩
  · rintro ⟨n, hn₁, hn₂, z, hz, h⟩
    exact mem_iUnion.mpr ⟨⟨n, hn₁, hn₂⟩, z, hz, h⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem cyclicBand_zero (K : Subgroup G) (x : G) :
    cyclicBand K x 0 = (K : Set G) := by
  ext y
  rw [cyclicBand_mem_iff]
  constructor
  · rintro ⟨n, h₁, h₂, z, hz, rfl⟩
    have hn : n = 0 := by omega
    simpa [hn] using hz
  · intro hy
    exact ⟨0, by norm_num, by norm_num, y, hy, by simp⟩

private def cyclicNeighborhood (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (x : G) (r : ℕ) : OpenCompactNeighborhood G where
  set := cyclicBand K x r
  one_mem := (cyclicBand_mem_iff K x r 1).mpr ⟨0, by omega, by omega, 1, K.one_mem, by simp⟩
  open_set := isOpen_iUnion fun i => isOpenMap_mul_left _ _ hKo
  compact_set := by
    letI : Finite (Set.Icc (-(r : ℤ)) (r : ℤ)) := (Set.finite_Icc _ _).to_subtype
    exact isCompact_iUnion fun i => hKc.image (continuous_const.mul continuous_id)
  symmetric := by
    have h {y : G} : y ∈ cyclicBand K x r → y⁻¹ ∈ cyclicBand K x r := by
      intro hy
      obtain ⟨n, h₁, h₂, z, hz, rfl⟩ := (cyclicBand_mem_iff K x r y).mp hy
      refine (cyclicBand_mem_iff _ _ _ _).mpr ⟨-n, by omega, by omega, z⁻¹, K.inv_mem hz, ?_⟩
      rw [zpow_neg, mul_inv_rev, mul_comm]
    ext z
    exact ⟨fun hz => inv_inv z ▸ h hz, h⟩

private theorem cyclicBand_step (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (x : G) (r : ℕ) :
    (cyclicNeighborhood K hKo hKc x r).Step (cyclicNeighborhood K hKo hKc x (r / 2)) := by
  let d := r / 2
  have h₁ : d ≤ r := Nat.div_le_self r 2
  have h₂ : r ≤ 2 * d + 1 := by omega
  let s := (2 : ℤ) * d + 1
  refine ⟨?_, ⟨fun i => x ^ (s * ((i.val : ℤ) - 1)), ?_⟩⟩
  · intro z hz
    obtain ⟨i, hi₁, hi₂, a, ha, he⟩ := (cyclicBand_mem_iff _ _ _ _).mp hz
    exact (cyclicBand_mem_iff _ _ _ _).mpr ⟨i, by omega, by omega, a, ha, he⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨i, hi₁, hi₂, y, hy, rfl⟩ := (cyclicBand_mem_iff _ _ _ _).mp ha
    obtain ⟨j, hj₁, hj₂, z, hz, rfl⟩ := (cyclicBand_mem_iff _ _ _ _).mp hb
    have claim (k : Fin 3) (m : ℤ) (hm₁ : -(d : ℤ) ≤ m) (hm₂ : m ≤ d)
        (he : s * ((k.val : ℤ) - 1) + m = i + j) :
        (x ^ i * y) * (x ^ j * z) ∈
          ⋃ k : Fin 3, x ^ (s * ((k.val : ℤ) - 1)) • cyclicBand K x d := by
      refine mem_iUnion.mpr ⟨k, x ^ m * (y * z),
        (cyclicBand_mem_iff _ _ _ _).mpr ⟨m, hm₁, hm₂, y * z, K.mul_mem hy hz, rfl⟩, ?_⟩
      change x ^ (s * ((k.val : ℤ) - 1)) * (x ^ m * (y * z)) = _
      rw [← mul_assoc, ← zpow_add, he, zpow_add, mul_mul_mul_comm]
    by_cases hlow : i + j < -(d : ℤ)
    · apply claim 0 (i + j + s)
      · dsimp [s]
        omega
      · dsimp [s]
        omega
      · simp [s]
        omega
    by_cases hhigh : (d : ℤ) < i + j
    · apply claim 2 (i + j - s)
      · dsimp [s]
        omega
      · dsimp [s]
        omega
      · simp [s]
    · exact claim 1 (i + j) (not_lt.mp hlow) (not_lt.mp hhigh) (by simp)

private theorem cyclicBand_refines (K : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (x : G) (r : ℕ) :
    Relation.ReflTransGen OpenCompactNeighborhood.Step (cyclicNeighborhood K hKo hKc x r)
      (cyclicNeighborhood K hKo hKc x 0) := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    by_cases hr : r = 0
    · subst r
      exact .refl
    · exact (Relation.ReflTransGen.single (cyclicBand_step K hKo hKc x r)).trans
        (ih (r / 2) (Nat.div_lt_self (by omega) (by decide)))


private def subgroupNeighborhood (H : Subgroup G) (hHo : IsOpen (H : Set G))
    (hHc : IsCompact (H : Set G)) : OpenCompactNeighborhood G where
  set := H
  one_mem := H.one_mem
  open_set := hHo
  compact_set := hHc
  symmetric := by
    ext x
    exact ⟨fun hx => by simpa using H.inv_mem hx, H.inv_mem⟩

omit [IsTopologicalGroup G] in
private theorem OpenCompactNeighborhood.ext_set (A B : OpenCompactNeighborhood G)
    (h : A.set = B.set) : A = B := by
  cases A
  cases B
  cases h
  rfl

private theorem cyclicBand_top (H K : Subgroup G) (hHK : K ≤ H)
    (hKo : IsOpen (K : Set G)) (hHc : IsCompact (H : Set G)) (g : G) (hg : g ∈ H)
    (he : H = Subgroup.zpowers g ⊔ K) :
    ∃ n : ℕ, cyclicBand K g n = (H : Set G) := by
  let J := K.subgroupOf H
  letI : J.FiniteIndex := compactOpen_finiteRelIndex hKo hHc
  letI : Finite (H ⧸ J) := Subgroup.finiteIndex_iff_finite_quotient.mp inferInstance
  let q := QuotientGroup.mk' J
  let u : H := ⟨g, hg⟩
  let n := orderOf (q u)
  have hn : 0 < n := orderOf_pos _
  refine ⟨n, Set.ext fun x => ?_⟩
  rw [cyclicBand_mem_iff]
  constructor
  · rintro ⟨i, _, _, y, hy, rfl⟩
    exact H.mul_mem (H.zpow_mem hg i) (hHK hy)
  · intro hx
    have hx' : x ∈ Subgroup.zpowers g ⊔ K := he ▸ hx
    obtain ⟨y, hy, k, hk, rfl⟩ := Subgroup.mem_sup.mp hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    let j := i % (n : ℤ)
    have hj₁ : 0 ≤ j := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    have hj₂ : j < n := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    have hq : q (u ^ j) = q (u ^ i) := by
      rw [map_zpow, map_zpow]
      exact zpow_mod_orderOf (q u) i
    have hK : (g ^ j)⁻¹ * g ^ i ∈ K := by
      have hq' : ((u ^ j : H) : H ⧸ J) = ((u ^ i : H) : H ⧸ J) := hq
      have hJ : (u ^ j)⁻¹ * (u ^ i) ∈ J := QuotientGroup.eq.mp hq'
      exact hJ
    refine ⟨j, by omega, hj₂.le, (g ^ j)⁻¹ * g ^ i * k, K.mul_mem hK hk, ?_⟩
    group

private theorem cyclicSubgroup_refinement (H K : Subgroup G) (hHK : K ≤ H)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (g : G) (hg : g ∈ H) (he : H = Subgroup.zpowers g ⊔ K) :
    Relation.ReflTransGen OpenCompactNeighborhood.Step
      (subgroupNeighborhood H hHo hHc) (subgroupNeighborhood K hKo hKc) := by
  obtain ⟨n, ht⟩ := cyclicBand_top H K hHK hKo hHc g hg he
  have hH : cyclicNeighborhood K hKo hKc g n = subgroupNeighborhood H hHo hHc :=
    OpenCompactNeighborhood.ext_set _ _ ht
  have hK : cyclicNeighborhood K hKo hKc g 0 = subgroupNeighborhood K hKo hKc :=
    OpenCompactNeighborhood.ext_set _ _ (cyclicBand_zero K g)
  simpa only [hH, hK] using cyclicBand_refines K hKo hKc g n

/-- Refine a finite-index inclusion of compact open subgroups by
compact open symmetric sets with bounded adjacent translate covers. -/
theorem compactOpenSubgroup_refinement (H K : Subgroup G) (hHK : K ≤ H)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    Relation.ReflTransGen OpenCompactNeighborhood.Step
      (subgroupNeighborhood H hHo hHc) (subgroupNeighborhood K hKo hKc) := by
  classical
  generalize hN : K.relIndex H = N
  induction N using Nat.strongRecOn generalizing H K with
  | ind N ih =>
    by_cases he : H ≤ K
    · have eq := le_antisymm hHK he
      subst K
      exact .refl
    · change ¬ ∀ g : G, g ∈ H → g ∈ K at he
      push Not at he
      obtain ⟨g, hg, hgK⟩ := he
      let J := Subgroup.zpowers g ⊔ K
      have hKJ : K ≤ J := le_sup_right
      have hJH : J ≤ H := sup_le (Subgroup.zpowers_le.mpr hg) hHK
      have hJo : IsOpen (J : Set G) := Subgroup.isOpen_mono hKJ hKo
      have hJc : IsCompact (J : Set G) := hHc.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJH
      have hgJ : g ∈ J := (show Subgroup.zpowers g ≤ J from le_sup_left) (Subgroup.mem_zpowers g)
      have hK_lt : 1 < K.relIndex J := by
        have hf : (K.subgroupOf J).FiniteIndex := compactOpen_finiteRelIndex hKo hJc
        have hp := Subgroup.finiteIndex_iff.mp hf
        have hneq : K.relIndex J ≠ 1 := fun h => hgK ((Subgroup.relIndex_eq_one.mp h) hgJ)
        change K.relIndex J ≠ 0 at hp
        omega
      have hJpos : 0 < J.relIndex H := by
        have hf : (J.subgroupOf H).FiniteIndex := compactOpen_finiteRelIndex hJo hHc
        exact Nat.pos_of_ne_zero (Subgroup.finiteIndex_iff.mp hf)
      have hmul := Subgroup.relIndex_mul_relIndex K J H hKJ hJH
      have hlt : J.relIndex H < N := by
        rw [← hN, ← hmul]
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hK_lt hJpos
      exact (ih (J.relIndex H) hlt H J hJH hHo hHc hJo hJc rfl).trans
        (cyclicSubgroup_refinement J K hKJ hJo hJc hKo hKc g hgJ rfl)


omit [IsTopologicalGroup G] in
private theorem subgroupNeighborhood_step_self (H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G)) :
    (subgroupNeighborhood H hHo hHc).Step (subgroupNeighborhood H hHo hHc) := by
  refine ⟨subset_rfl, fun _ => 1, ?_⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact mem_iUnion.mpr ⟨(0 : Fin 3), x * y, H.mul_mem hx hy, one_mul _⟩

omit [IsTopologicalGroup G] in
private theorem finiteStepPath {A B : OpenCompactNeighborhood G}
    (h : Relation.ReflTransGen OpenCompactNeighborhood.Step A B) :
    ∃ (n : ℕ) (f : ℕ → OpenCompactNeighborhood G), f 0 = A ∧ f n = B ∧
      ∀ i < n, (f i).Step (f (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => A, rfl, rfl, by simp⟩
  | @tail C D _ he ih =>
    obtain ⟨n, f, h₀, hn, hp⟩ := ih
    let g (i : ℕ) := if i ≤ n then f i else D
    refine ⟨n + 1, g, ?_, ?_, ?_⟩
    · simpa only [g, ite_eq_left (Nat.zero_le n)] using h₀
    · simp [g]
    · intro i hi
      by_cases hj : i < n
      · simpa only [g, ite_eq_left hj.le, ite_eq_left (Nat.succ_le_of_lt hj)] using hp i hj
      · have e : i = n := by omega
        subst i
        simpa only [g, ite_eq_left le_rfl, ite_eq_right (Nat.not_succ_le_self n), hn] using he

/-- Refine any decreasing compact-open subgroup basis, keeping its
subgroups as stages and obtaining a uniform bound of three translates.
The intermediate stages can be compact open sets with no subgroup law. -/
theorem refinedCompactOpenBasis (K : ℕ → Subgroup G)
    (hKo : ∀ k, IsOpen (K k : Set G)) (hKc : ∀ k, IsCompact (K k : Set G))
    (hdec : Antitone K) (hcof : CofinalAtOne (fun k => (K k : Set G))) :
    ∃ U : ℕ → Set G, OpenTranslateBasis U ∧ ∀ k, ∃ i, U i = (K k : Set G) := by
  classical
  let B (k : ℕ) := subgroupNeighborhood (K k) (hKo k) (hKc k)
  have hseg (k : ℕ) :
      ∃ (n : ℕ) (f : ℕ → OpenCompactNeighborhood G), 0 < n ∧
        f 0 = B k ∧ f n = B (k + 1) ∧ ∀ i < n, (f i).Step (f (i + 1)) := by
    obtain ⟨n, f, h₀, hn, hstep⟩ := finiteStepPath
      (compactOpenSubgroup_refinement (K k) (K (k + 1)) (hdec (Nat.le_succ k))
        (hKo k) (hKc k) (hKo (k + 1)) (hKc (k + 1)))
    let g (i : ℕ) := if i ≤ n then f i else B (k + 1)
    refine ⟨n + 1, g, Nat.zero_lt_succ n, ?_, ?_, ?_⟩
    · simpa only [g, ite_eq_left (Nat.zero_le _) ] using h₀
    · simp [g]
    · intro i hi
      by_cases hj : i < n
      · simpa only [g, ite_eq_left hj.le, ite_eq_left (Nat.succ_le_of_lt hj)] using hstep i hj
      · have e : i = n := by omega
        subst i
        simpa only [g, ite_eq_left le_rfl, ite_eq_right (Nat.not_succ_le_self n), hn] using
          subgroupNeighborhood_step_self (K (k + 1)) (hKo (k + 1)) (hKc (k + 1))
  choose len paths hp hs he hstep using hseg
  let start (k : ℕ) := ∑ i ∈ Finset.range k, len i
  have hzero : start 0 = 0 := rfl
  have hadd (k : ℕ) : start (k + 1) = start k + len k := Finset.sum_range_succ _ _
  have hmono : StrictMono start := strictMono_nat_of_lt_succ (fun k => by rw [hadd]; exact Nat.lt_add_of_pos_right (hp k))
  have hbound (k : ℕ) : k ≤ start k := hmono.le_apply
  have hex (n : ℕ) : ∃ k, n < start (k + 1) := ⟨n, (Nat.lt_succ_self n).trans_le (hbound _)⟩
  let seg (n : ℕ) := Nat.find (hex n)
  have hl (n : ℕ) : start (seg n) ≤ n := by
    rcases h : seg n with _ | k
    · rw [hzero]
      exact Nat.zero_le _
    · exact le_of_not_gt (Nat.find_min (hex n) (show k < seg n by omega))
  have hr (n : ℕ) : n < start (seg n + 1) := Nat.find_spec (hex n)
  have hu (n k : ℕ) (h₁ : start k ≤ n) (h₂ : n < start (k + 1)) : seg n = k := by
    apply Nat.le_antisymm
    · by_contra! h
      exact (not_lt_of_ge (hl n)) (h₂.trans_le (hmono.monotone (show k + 1 ≤ seg n by omega)))
    · by_contra! h
      exact (not_lt_of_ge h₁) ((hr n).trans_le (hmono.monotone (show seg n + 1 ≤ k by omega)))
  let f (n : ℕ) := paths (seg n) (n - start (seg n))
  have hstart (k : ℕ) : f (start k) = B k := by
    have hse : seg (start k) = k := hu _ _ le_rfl (hmono (Nat.lt_succ_self k))
    simp only [f, hse, Nat.sub_self, hs]
  have hf (n : ℕ) : (f n).Step (f (n + 1)) := by
    let k := seg n
    let i := n - start k
    have hL : start k ≤ n := hl n
    have hi : i < len k := by
      have e := hr n
      change n < start (k + 1) at e
      rw [hadd] at e
      dsimp [i]
      omega
    by_cases hm : n + 1 < start (k + 1)
    · have hse : seg (n + 1) = k := hu _ _ (hL.trans (Nat.le_succ n)) hm
      have eq : n + 1 - start k = i + 1 := by dsimp [i]; omega
      change (paths k i).Step (paths (seg (n + 1)) (n + 1 - start (seg (n + 1))))
      rw [hse, eq]
      exact hstep k i hi
    · have heq : n + 1 = start (k + 1) := by
        have hh := hr n
        change n < start (k + 1) at hh
        omega
      have hlen : i + 1 = len k := by rw [hadd] at heq; dsimp [i]; omega
      rw [heq, hstart]
      change (paths k i).Step (B (k + 1))
      rw [← he k, ← hlen]
      exact hstep k i hi
  refine ⟨fun n => (f n).set, ⟨fun k => (f k).one_mem, fun k => (f k).open_set,
    antitone_nat_of_succ_le (fun n => (hf n).1), fun k => (f k).symmetric,
    fun k => ⟨_, (f k).compact_set, subset_rfl⟩, ?_, ⟨3, fun k => (hf k).2⟩⟩,
    fun k => ⟨start k, congrArg OpenCompactNeighborhood.set (hstart k)⟩⟩
  intro V hV
  obtain ⟨k, hk⟩ := hcof V hV
  refine ⟨start k, ?_⟩
  change (f (start k)).set ⊆ V
  rw [hstart]
  exact hk

end

end Masullo
