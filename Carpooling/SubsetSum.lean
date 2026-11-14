import Carpooling.Basic

/-!
  Zero-sum subset-sum polytopes `P(β)` and the hitting-set safety criterion
  (carpooling paper §3, Lemma 3.1).
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- Zero-sum subset-sum polytope `P(β) = {q ∈ H_m : q(A) ≥ -β_{|A|} for all A}`
    (paper §3). -/
def Psub (β : ℕ → ℝ) : Set (Fin m → ℝ) :=
  { q | (∑ i, q i) = 0 ∧ ∀ A : Finset (Fin m), -β A.card ≤ ∑ i ∈ A, q i }

open Classical in
/-- Dangerous family `D(q)`: proper nonempty `A` whose post-drift sum
    `y(A) = q(A) - d x(A)` falls below `-β_{|A|}` (paper §3). -/
noncomputable def danger (β : ℕ → ℝ) (d : ℝ) (x q : Fin m → ℝ) :
    Finset (Finset (Fin m)) :=
  univ.filter fun A => 1 ≤ A.card ∧ A.card ≤ m - 1 ∧
    (∑ i ∈ A, q i) - d * (∑ i ∈ A, x i) < -β A.card

/-- Membership in the dangerous family. -/
lemma mem_danger {β : ℕ → ℝ} {d : ℝ} {x q : Fin m → ℝ} {A : Finset (Fin m)} :
    A ∈ danger β d x q ↔ 1 ≤ A.card ∧ A.card ≤ m - 1 ∧
      (∑ i ∈ A, q i) - d * (∑ i ∈ A, x i) < -β A.card := by
  simp [danger]

/-- A subset missing the support has zero share mass. -/
lemma sum_eq_zero_of_disjoint_supp {x : Fin m → ℝ} {A : Finset (Fin m)}
    (h : ∀ i ∈ A, i ∉ supp x) : (∑ i ∈ A, x i) = 0 :=
  Finset.sum_eq_zero fun i hi => by simpa [supp] using h i hi

/-- Lemma 3.1, first part: every dangerous set meets the support. -/
lemma danger_meets_supp {β : ℕ → ℝ} {d : ℝ} {x q : Fin m → ℝ}
    (hq : q ∈ Psub β) {A : Finset (Fin m)} (hA : A ∈ danger β d x q) :
    ∃ i ∈ A, i ∈ supp x := by
  by_contra h
  push Not at h
  have hx := sum_eq_zero_of_disjoint_supp h
  rw [mem_danger, hx] at hA
  have h1 := hq.2 A
  linarith [hA.2.2]

/-- A subset avoiding some index has cardinality at most `m - 1`. -/
lemma card_le_pred_of_not_mem {A : Finset (Fin m)} {k : Fin m} (hk : k ∉ A) :
    A.card ≤ m - 1 := by
  have hlt : A.card < (univ : Finset (Fin m)).card :=
    Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => hk (h ▸ mem_univ k))
  rw [Finset.card_univ, Fintype.card_fin] at hlt
  omega

/-- Lemma 3.1, safety criterion: a supported move `k` stays in `P(β)` iff `k`
    lies in every dangerous set. -/
lemma step_mem_Psub_iff {β : ℕ → ℝ} (hβ0 : 0 ≤ β 0) {d : ℝ} (hd : 0 ≤ d)
    {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    {q : Fin m → ℝ} (hq : q ∈ Psub β) (k : Fin m) :
    step d x k q ∈ Psub β ↔ ∀ A ∈ danger β d x q, k ∈ A := by
  constructor
  · intro hstep A hA
    by_contra hkA
    have h1 := hstep.2 A
    rw [sum_step, if_neg hkA] at h1
    rw [mem_danger] at hA
    linarith [hA.2.2]
  · intro hall
    refine ⟨by rw [sum_step_univ hx1]; exact hq.1, fun A => ?_⟩
    rw [sum_step]
    by_cases hkA : k ∈ A
    · rw [if_pos hkA]
      have h1 := hq.2 A
      have h2 := mul_nonneg hd (sub_nonneg.mpr (sum_subset_le_one hx0 hx1 A))
      linarith
    · rw [if_neg hkA]
      by_cases hAe : A = ∅
      · subst hAe
        simp only [Finset.card_empty, Finset.sum_empty]
        linarith
      · have hc1 : 1 ≤ A.card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAe)
        have hnot : A ∉ danger β d x q := fun h => hkA (hall A h)
        rw [mem_danger] at hnot
        push Not at hnot
        have h3 := hnot hc1 (card_le_pred_of_not_mem hkA)
        linarith

/-- Lemma 3.1, trap form: `q` is a trap for `(P(β), d, x)` iff the support
    misses the intersection of the dangerous family. -/
theorem trap_iff_Psub {β : ℕ → ℝ} (hβ0 : 0 ≤ β 0) {d : ℝ} (hd : 0 ≤ d)
    {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    {q : Fin m → ℝ} (hq : q ∈ Psub β) :
    (¬ ∃ k ∈ supp x, step d x k q ∈ Psub β) ↔
      ∀ k ∈ supp x, ∃ A ∈ danger β d x q, k ∉ A := by
  constructor
  · intro h k hk
    have hns : ¬ step d x k q ∈ Psub β := fun hs => h ⟨k, hk, hs⟩
    rw [step_mem_Psub_iff hβ0 hd hx0 hx1 hq] at hns
    push Not at hns
    exact hns
  · rintro h ⟨k, hk, hs⟩
    obtain ⟨A, hA, hkA⟩ := h k hk
    rw [step_mem_Psub_iff hβ0 hd hx0 hx1 hq] at hs
    exact hkA (hs A hA)

end Carpooling
