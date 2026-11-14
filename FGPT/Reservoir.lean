import FGPT.Theorem

/-!
  Interval feasibility with one conservation law (FGPT paper §7.1).
-/

open Finset

namespace FGPT

variable {m : ℕ}

/-- **Reservoir lemma** (paper Lemma 7.1): for `l i < u i`, a zero-sum vector
    with `l i < q i < u i` for all `i` exists iff `∑ l < 0 < ∑ u`. -/
theorem reservoir (hm : 0 < m) {l u : Fin m → ℝ} (hlu : ∀ i, l i < u i) :
    (∃ q : Fin m → ℝ, (∀ i, l i < q i ∧ q i < u i) ∧ (∑ i, q i) = 0) ↔
      (∑ i, l i) < 0 ∧ 0 < ∑ i, u i := by
  have hne : (univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, mem_univ _⟩
  constructor
  · rintro ⟨q, hq, hsum⟩
    constructor
    · rw [← hsum]
      exact Finset.sum_lt_sum_of_nonempty hne (fun i _ => (hq i).1)
    · rw [← hsum]
      exact Finset.sum_lt_sum_of_nonempty hne (fun i _ => (hq i).2)
  · rintro ⟨hl, hu⟩
    set L := ∑ i, l i with hL
    set U := ∑ i, u i with hU
    have hUL : 0 < U - L := by linarith
    set t := -L / (U - L) with ht
    have ht0 : 0 < t := div_pos (by linarith) hUL
    have ht1 : t < 1 := by
      rw [ht, div_lt_one hUL]
      linarith
    have htid : t * (U - L) = -L := by
      rw [ht]
      field_simp
    refine ⟨fun i => l i + t * (u i - l i), fun i => ⟨?_, ?_⟩, ?_⟩
    · have h := sub_pos.2 (hlu i)
      nlinarith
    · have h := sub_pos.2 (hlu i)
      nlinarith
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← hL, ← hU]
      linarith

end FGPT
