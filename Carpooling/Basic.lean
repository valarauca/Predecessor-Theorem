import FGPT

/-!
  Optimal Online Weighted Carpooling — Lean 4 / mathlib formalization.

  Builds on the Fixed-Generator Predecessor Theorem in `FGPT`.
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- One-step controllable predecessor `Pre_{d,x}(K)` of a target set `K` (paper §1). -/
def pred (d : ℝ) (x : Fin m → ℝ) (K : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  { q | q ∈ K ∧ ∃ k ∈ supp x, step d x k q ∈ K }

/-- `K` is one-step controlled invariant under `(d, x)` iff every state of `K`
    has a supported move that stays in `K`. -/
lemma pred_eq_self_iff {d : ℝ} {x : Fin m → ℝ} {K : Set (Fin m → ℝ)} :
    pred d x K = K ↔ ∀ q ∈ K, ∃ k ∈ supp x, step d x k q ∈ K := by
  constructor
  · intro h q hq
    rw [← h] at hq
    exact hq.2
  · intro h
    ext q
    exact ⟨fun hq => hq.1, fun hq => ⟨hq, h q hq⟩⟩

/-- The Fixed-Generator Predecessor Theorem in predecessor form
    (carpooling paper Theorem 2.2). -/
theorem fgpt_pred {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hm : 2 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    pred d x (Qbox m) = Qbox m ↔
      (d * sigma2 x ≤ (4 : ℝ) - (m : ℝ) ∧
       d * ((suppCard x : ℝ) - 1) ≤ 2 * (suppCard x : ℝ) - (m : ℝ)) := by
  rw [pred_eq_self_iff]
  exact fgpt hd0 hd2 hm hx0 hx1 hs

/-- Post-drift greedy choice: `k ∈ supp x` minimizes `q k - d * x k` over
    `supp x` (paper §4). -/
def IsGreedy (d : ℝ) (x q : Fin m → ℝ) (k : Fin m) : Prop :=
  k ∈ supp x ∧ ∀ j ∈ supp x, q k - d * x k ≤ q j - d * x j

/-- A probability vector has nonempty support. -/
lemma supp_nonempty {x : Fin m → ℝ} (hx1 : (∑ i, x i) = 1) : (supp x).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hz : ∀ i, x i = 0 := fun i => by
    by_contra hi
    have hmem : i ∈ supp x := by simp [supp, hi]
    simp [h] at hmem
  simp [hz] at hx1

/-- A greedy choice always exists for a probability vector. -/
lemma exists_isGreedy (d : ℝ) {x : Fin m → ℝ} (hx1 : (∑ i, x i) = 1)
    (q : Fin m → ℝ) : ∃ k, IsGreedy d x q k := by
  obtain ⟨k, hk, hmin⟩ :=
    Finset.exists_min_image (supp x) (fun j => q j - d * x j) (supp_nonempty hx1)
  exact ⟨k, hk, hmin⟩

/-- Every coordinate of a probability vector is at most one. -/
lemma le_one_of_prob {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (i : Fin m) : x i ≤ 1 := by
  have h := Finset.single_le_sum (f := x) (fun j _ => hx0 j) (mem_univ i)
  rwa [hx1] at h

/-- Subset sums of a probability vector lie in `[0, 1]`. -/
lemma sum_subset_le_one {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (A : Finset (Fin m)) : (∑ i ∈ A, x i) ≤ 1 := by
  rw [← hx1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hx0 i)

/-- Subset sum of a step: `q'(A) = q(A) + d (1_A(k) - x(A))`. -/
lemma sum_step (d : ℝ) (x : Fin m → ℝ) (k : Fin m) (q : Fin m → ℝ)
    (A : Finset (Fin m)) :
    (∑ i ∈ A, step d x k q i) =
      (∑ i ∈ A, q i) + d * ((if k ∈ A then (1 : ℝ) else 0) - ∑ i ∈ A, x i) := by
  simp only [step]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 2
  rw [Finset.sum_ite_eq']

/-- Steps preserve the zero-sum hyperplane. -/
lemma sum_step_univ {x : Fin m → ℝ} (hx1 : (∑ i, x i) = 1) (d : ℝ) (k : Fin m)
    (q : Fin m → ℝ) : (∑ i, step d x k q i) = ∑ i, q i := by
  rw [sum_step, if_pos (mem_univ k), hx1]
  ring

/-- With singleton support the only move is the identity (paper §1). -/
lemma step_of_supp_eq_singleton {x : Fin m → ℝ} (hx1 : (∑ i, x i) = 1)
    {k : Fin m} (hk : supp x = {k}) (d : ℝ) (q : Fin m → ℝ) :
    step d x k q = q := by
  have hzero : ∀ i, i ≠ k → x i = 0 := by
    intro i hik
    by_contra hi
    have hmem : i ∈ supp x := by simp [supp, hi]
    rw [hk, Finset.mem_singleton] at hmem
    exact hik hmem
  have hxk : x k = 1 := by
    rw [← hx1, Finset.sum_eq_single k (fun i _ hik => hzero i hik) (by simp)]
  funext i
  simp only [step]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, hxk]
    ring
  · rw [if_neg hik, hzero i hik]
    ring

end Carpooling
