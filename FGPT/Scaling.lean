import FGPT.Theorem

/-!
  Scaling (FGPT paper Remark 3.3): the map `q ↦ q / B` conjugates the
  `(d, x)`-dynamics on the radius-`B` box to the `(d / B, x)`-dynamics on `Q_m`.
-/

open Finset

namespace FGPT

variable {m : ℕ}

/-- The zero-sum box of radius `B`, `Q_m(B)` (paper Remark 3.3). -/
def QboxR (m : ℕ) (B : ℝ) : Set (Fin m → ℝ) :=
  { q | (∑ i, q i) = 0 ∧ ∀ i, |q i| ≤ B }

/-- The unit-radius box is `Q_m`. -/
lemma QboxR_one (m : ℕ) : QboxR m 1 = Qbox m := rfl

/-- Steps commute with scaling: `T^{B d}_k (B q) = B · T^d_k (q)` (paper Remark 3.3). -/
lemma step_smul (B d : ℝ) (x : Fin m → ℝ) (k : Fin m) (q : Fin m → ℝ) :
    step (B * d) x k (B • q) = B • step d x k q := by
  funext i
  simp only [step, Pi.smul_apply, smul_eq_mul]
  ring

/-- `B q ∈ Q_m(B)` iff `q ∈ Q_m`, for `B > 0` (paper Remark 3.3). -/
lemma smul_mem_QboxR_iff {B : ℝ} (hB : 0 < B) {q : Fin m → ℝ} :
    B • q ∈ QboxR m B ↔ q ∈ Qbox m := by
  simp only [QboxR, Qbox, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_eq_zero, or_iff_right hB.ne']
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  rw [abs_mul, abs_of_pos hB]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-- One-step invariance of `Q_m(B)` under `(d, x)` is one-step invariance of
    `Q_m` under `(d / B, x)` (paper Remark 3.3). -/
lemma invariant_QboxR_iff {B d : ℝ} (hB : 0 < B) {x : Fin m → ℝ} :
    (∀ q ∈ QboxR m B, ∃ k ∈ supp x, step d x k q ∈ QboxR m B) ↔
      (∀ q ∈ Qbox m, ∃ k ∈ supp x, step (d / B) x k q ∈ Qbox m) := by
  have hBd : B * (d / B) = d := by field_simp
  constructor
  · intro h q hq
    obtain ⟨k, hk, hstep⟩ := h (B • q) ((smul_mem_QboxR_iff hB).2 hq)
    refine ⟨k, hk, ?_⟩
    rw [← smul_mem_QboxR_iff hB, ← step_smul, hBd]
    exact hstep
  · intro h q hq
    have hBq : B • (B⁻¹ • q) = q := by
      rw [smul_smul, mul_inv_cancel₀ hB.ne', one_smul]
    have hq' : B⁻¹ • q ∈ Qbox m := by
      rw [← smul_mem_QboxR_iff hB, hBq]
      exact hq
    obtain ⟨k, hk, hstep⟩ := h _ hq'
    refine ⟨k, hk, ?_⟩
    rw [← smul_mem_QboxR_iff hB, ← step_smul, hBd, hBq] at hstep
    exact hstep

/-- **Fixed-Generator Predecessor Theorem on the radius-`B` box**
    (paper Remark 3.3 applied to Theorem 4.1): replace `d` by `d / B`. -/
theorem fgpt_scaled {B d : ℝ} (hB : 0 < B) (hd0 : 0 < d) (hd2 : d ≤ 2 * B)
    {x : Fin m → ℝ} (hm : 2 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    (∀ q ∈ QboxR m B, ∃ k ∈ supp x, step d x k q ∈ QboxR m B) ↔
      ((d / B) * sigma2 x ≤ (4 : ℝ) - (m : ℝ) ∧
       (d / B) * ((suppCard x : ℝ) - 1) ≤ 2 * (suppCard x : ℝ) - (m : ℝ)) := by
  have hdB0 : 0 < d / B := div_pos hd0 hB
  have hdB2 : d / B ≤ 2 := by
    rw [div_le_iff₀ hB]
    linarith
  rw [invariant_QboxR_iff hB]
  exact fgpt hdB0 hdB2 hm hx0 hx1 hs

end FGPT
