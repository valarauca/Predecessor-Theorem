import Carpooling.Permutohedron

/-!
  A trap of a subset-sum polytope outside both cube modes at `m = 4`
  (carpooling paper Proposition 3.2).
-/

open Finset FGPT

namespace Carpooling

/-- Profile `β = (0, 1, 4/3, 1, 0)` of Proposition 3.2. -/
noncomputable def beta32 (r : ℕ) : ℝ :=
  if r = 2 then 4 / 3 else if r = 1 ∨ r = 3 then 1 else 0

/-- State `q = (-1/3, -1/3, -1/3, 1)` of Proposition 3.2. -/
noncomputable def q32 : Fin 4 → ℝ := fun i => if i = 3 then 1 else -1 / 3

/-- Share vector `x = (1/3, 1/3, 1/3, 0)` of Proposition 3.2. -/
noncomputable def x32 : Fin 4 → ℝ := fun i => if i = 3 then 0 else 1 / 3

/-- Demand `d = 6/5` of Proposition 3.2. -/
noncomputable def d32 : ℝ := 6 / 5

/-- Subset sums over `Fin 4` expanded coordinatewise. -/
lemma sum_fin4 {M : Type*} [AddCommMonoid M] (A : Finset (Fin 4)) (f : Fin 4 → M) :
    (∑ i ∈ A, f i) = (if (0 : Fin 4) ∈ A then f 0 else 0) + (if (1 : Fin 4) ∈ A then f 1 else 0) +
      (if (2 : Fin 4) ∈ A then f 2 else 0) + (if (3 : Fin 4) ∈ A then f 3 else 0) := by
  rw [← Fin.sum_univ_four (f := fun i => if i ∈ A then f i else 0), ← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- Cardinalities over `Fin 4` expanded coordinatewise. -/
lemma card_fin4 (A : Finset (Fin 4)) :
    A.card = (if (0 : Fin 4) ∈ A then 1 else 0) + (if (1 : Fin 4) ∈ A then 1 else 0) +
      (if (2 : Fin 4) ∈ A then 1 else 0) + (if (3 : Fin 4) ∈ A then 1 else 0) := by
  rw [Finset.card_eq_sum_ones, sum_fin4]

/-- Proposition 3.2: `q ∈ P(β)`. -/
lemma q32_mem : q32 ∈ Psub beta32 := by
  refine ⟨?_, fun A => ?_⟩
  · simp [Fin.sum_univ_four, q32]
    norm_num
  · rw [sum_fin4, card_fin4]
    by_cases h0 : (0 : Fin 4) ∈ A <;> by_cases h1 : (1 : Fin 4) ∈ A <;>
      by_cases h2 : (2 : Fin 4) ∈ A <;> by_cases h3 : (3 : Fin 4) ∈ A <;>
      simp [h0, h1, h2, h3, beta32, q32] <;> norm_num

/-- `x = (1/3, 1/3, 1/3, 0)` is nonnegative. -/
lemma x32_nonneg : ∀ i, 0 ≤ x32 i := by
  intro i
  unfold x32
  split_ifs <;> norm_num

/-- `x = (1/3, 1/3, 1/3, 0)` sums to one. -/
lemma x32_sum : (∑ i, x32 i) = 1 := by
  simp [Fin.sum_univ_four, x32]
  norm_num

/-- The support of `x` is `{0, 1, 2}`. -/
lemma mem_supp_x32 (k : Fin 4) : k ∈ supp x32 ↔ k ≠ 3 := by
  simp [supp, x32]

/-- Proposition 3.2: the dangerous family consists of the sets avoiding the
    unsupported coordinate `3` that contain at least two supported coordinates. -/
lemma mem_danger32 (A : Finset (Fin 4)) :
    A ∈ danger beta32 d32 x32 q32 ↔ (3 : Fin 4) ∉ A ∧
      (((0 : Fin 4) ∈ A ∧ (1 : Fin 4) ∈ A) ∨ ((0 : Fin 4) ∈ A ∧ (2 : Fin 4) ∈ A) ∨
        ((1 : Fin 4) ∈ A ∧ (2 : Fin 4) ∈ A)) := by
  rw [mem_danger, sum_fin4 A q32, sum_fin4 A x32, card_fin4]
  by_cases h0 : (0 : Fin 4) ∈ A <;> by_cases h1 : (1 : Fin 4) ∈ A <;>
    by_cases h2 : (2 : Fin 4) ∈ A <;> by_cases h3 : (3 : Fin 4) ∈ A <;>
    simp [h0, h1, h2, h3, beta32, q32, x32, d32] <;> norm_num

/-- Proposition 3.2: `D(q) = {{0,1}, {0,2}, {1,2}, {0,1,2}}`. -/
theorem danger32_eq :
    danger beta32 d32 x32 q32 = {{0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
  ext A
  rw [mem_danger32]
  revert A
  decide

/-- Proposition 3.2: `q` is a trap for `(P(β), d, x)`. -/
theorem trap32 : ¬ ∃ k ∈ supp x32, step d32 x32 k q32 ∈ Psub beta32 := by
  rw [trap_iff_Psub (by simp [beta32]) (by norm_num [d32]) x32_nonneg x32_sum q32_mem]
  intro k hk
  rw [mem_supp_x32] at hk
  fin_cases k
  · exact ⟨{1, 2}, by rw [mem_danger32]; decide, by decide⟩
  · exact ⟨{0, 2}, by rw [mem_danger32]; decide, by decide⟩
  · exact ⟨{0, 1}, by rw [mem_danger32]; decide, by decide⟩
  · exact absurd rfl hk

/-- Proposition 3.2: `D(q)` contains no singleton, so `q` is not in the
    double-floor cube mode. -/
theorem danger32_no_singleton (i : Fin 4) : ({i} : Finset (Fin 4)) ∉ danger beta32 d32 x32 q32 := by
  rw [mem_danger32]
  fin_cases i <;> decide

/-- Proposition 3.2: `D(q)` contains no complement `[4] \ {k}` with `k ∈ S`, so
    `q` is not in the complete-blocking cube mode. -/
theorem danger32_no_cosingleton (k : Fin 4) (hk : k ∈ supp x32) :
    univ.erase k ∉ danger beta32 d32 x32 q32 := by
  rw [mem_supp_x32] at hk
  rw [mem_danger32]
  fin_cases k
  · decide
  · decide
  · decide
  · exact absurd rfl hk

/-- Proposition 3.2: `D(q)` contains no two disjoint sets. -/
theorem danger32_not_disjoint {A B : Finset (Fin 4)} (hA : A ∈ danger beta32 d32 x32 q32)
    (hB : B ∈ danger beta32 d32 x32 q32) : ¬ Disjoint A B := by
  rw [mem_danger32] at hA hB
  rw [Finset.not_disjoint_iff]
  obtain ⟨-, ⟨a0, a1⟩ | ⟨a0, a2⟩ | ⟨a1, a2⟩⟩ := hA <;>
    obtain ⟨-, ⟨b0, b1⟩ | ⟨b0, b2⟩ | ⟨b1, b2⟩⟩ := hB <;>
    first
      | exact ⟨0, by assumption, by assumption⟩
      | exact ⟨1, by assumption, by assumption⟩
      | exact ⟨2, by assumption, by assumption⟩

end Carpooling
