import FGPT.Theorem

/-!
  Threshold structure via monotone obstructions (FGPT paper §6).
-/

open Finset

namespace FGPT

variable {m : ℕ}

/-- **Monotone obstruction principle**, downward closure (paper Proposition 6.1):
    if `P θ ↔ ∀ α, g α θ ≤ 0` on `I` and every `g α` is monotone on `I`, then
    `{θ ∈ I | P θ}` is downward closed in `I`. -/
theorem monotone_obstruction {ι : Type*} {I : Set ℝ} (g : ι → ℝ → ℝ)
    (hg : ∀ α, MonotoneOn (g α) I) {P : ℝ → Prop}
    (hP : ∀ θ ∈ I, P θ ↔ ∀ α, g α θ ≤ 0)
    {θ θ' : ℝ} (hθ : θ ∈ I) (hθ' : θ' ∈ I) (hle : θ' ≤ θ) (hPθ : P θ) : P θ' := by
  rw [hP θ' hθ']
  intro α
  exact le_trans (hg α hθ' hθ hle) ((hP θ hθ).1 hPθ α)

/-- Individual obstruction threshold `τ_α := sup {θ ∈ I | g_α θ ≤ 0}`
    (paper Proposition 6.1). -/
noncomputable def obstructionThreshold (I : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup {θ ∈ I | f θ ≤ 0}

/-- **Monotone obstruction principle**, upper boundary (paper Proposition 6.1):
    the safe set lies between `{θ | θ < τ_α ∀ α}` and `{θ | θ ≤ τ_α ∀ α}`, so its
    upper boundary is `inf_α τ_α`; endpoint membership is checked separately. -/
theorem monotone_obstruction_boundary {ι : Type*} {I : Set ℝ} (hI : BddAbove I)
    (g : ι → ℝ → ℝ) (hg : ∀ α, MonotoneOn (g α) I)
    (hne : ∀ α, {θ ∈ I | g α θ ≤ 0}.Nonempty) {P : ℝ → Prop}
    (hP : ∀ θ ∈ I, P θ ↔ ∀ α, g α θ ≤ 0) :
    {θ ∈ I | ∀ α, θ < obstructionThreshold I (g α)} ⊆ {θ ∈ I | P θ} ∧
      {θ ∈ I | P θ} ⊆ {θ ∈ I | ∀ α, θ ≤ obstructionThreshold I (g α)} := by
  constructor
  · rintro θ ⟨hθI, hθlt⟩
    refine ⟨hθI, (hP θ hθI).2 fun α => ?_⟩
    obtain ⟨θ', ⟨hθ'I, hθ'g⟩, hlt⟩ := exists_lt_of_lt_csSup (hne α) (hθlt α)
    exact le_trans (hg α hθI hθ'I hlt.le) hθ'g
  · rintro θ ⟨hθI, hPθ⟩
    refine ⟨hθI, fun α => ?_⟩
    exact le_csSup (hI.mono (Set.sep_subset _ _)) ⟨hθI, (hP θ hθI).1 hPθ α⟩

/-- The two cube obstruction margins `g_D(d) = d σ₂(x) - (4 - m)` and
    `g_B(d) = d (s - 1) - (2s - m)` (paper §6). -/
noncomputable def cubeMargin (x : Fin m → ℝ) : Fin 2 → ℝ → ℝ :=
  ![fun d => d * sigma2 x - ((4 : ℝ) - m),
    fun d => d * ((suppCard x : ℝ) - 1) - (2 * (suppCard x : ℝ) - m)]

/-- Both cube margins are monotone in `d` (paper §6). -/
lemma cubeMargin_monotone {x : Fin m → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hs : 2 ≤ suppCard x) (α : Fin 2) : Monotone (cubeMargin x α) := by
  have hσ := sigma2_pos x hx0 hs
  have hsR : (2 : ℝ) ≤ (suppCard x : ℝ) := by exact_mod_cast hs
  intro a b hab
  fin_cases α
  · simp only [cubeMargin, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    nlinarith
  · simp only [cubeMargin, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    nlinarith

/-- `Q_m` is fixed iff both cube margins are nonpositive (paper §6, from Theorem 4.1). -/
lemma invariant_iff_cubeMargin {d : ℝ} (hd0 : 0 < d) (hd2 : d ≤ 2) {x : Fin m → ℝ}
    (hm : 2 ≤ m) (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1)
    (hs : 2 ≤ suppCard x) :
    (∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m) ↔
      ∀ α, cubeMargin x α d ≤ 0 := by
  rw [fgpt hd0 hd2 hm hx0 hx1 hs, Fin.forall_fin_two]
  simp only [cubeMargin, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sub_nonpos]

/-- The safe demand set of a fixed nontrivial generator is downward closed in
    `(0, 2]` (paper §6, Proposition 6.1 applied to `{g_D, g_B}`). -/
theorem safe_demand_downward_closed {x : Fin m → ℝ} (hm : 2 ≤ m)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1) (hs : 2 ≤ suppCard x)
    {d d' : ℝ} (hd : d ∈ Set.Ioc 0 2) (hd' : d' ∈ Set.Ioc 0 2) (hle : d' ≤ d)
    (hsafe : ∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m) :
    ∀ q ∈ Qbox m, ∃ k ∈ supp x, step d' x k q ∈ Qbox m :=
  monotone_obstruction (P := fun θ => ∀ q ∈ Qbox m, ∃ k ∈ supp x, step θ x k q ∈ Qbox m)
    (cubeMargin x) (fun α => (cubeMargin_monotone hx0 hs α).monotoneOn _)
    (fun _ hθ => invariant_iff_cubeMargin hθ.1 hθ.2 hm hx0 hx1 hs) hd hd' hle hsafe

/-- **Safe demand set** (paper §6): for a fixed nontrivial generator the safe
    demands are exactly `(0, 2] ∩ (-∞, d*]` with
    `d* = min ((2s - m)/(s - 1)) ((4 - m)/σ₂(x))`, endpoint included. -/
theorem safe_demand_set_eq {x : Fin m → ℝ} (hm : 2 ≤ m)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1) (hs : 2 ≤ suppCard x) :
    {d : ℝ | d ∈ Set.Ioc 0 2 ∧ ∀ q ∈ Qbox m, ∃ k ∈ supp x, step d x k q ∈ Qbox m} =
      Set.Ioc 0 2 ∩ Set.Iic (min ((2 * (suppCard x : ℝ) - m) / ((suppCard x : ℝ) - 1))
        (((4 : ℝ) - m) / sigma2 x)) := by
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Iic]
  constructor
  · rintro ⟨hd, hsafe⟩
    exact ⟨hd, (fgpt_ratio hd.1 hd.2 hm hx0 hx1 hs).1 hsafe⟩
  · rintro ⟨hd, hle⟩
    exact ⟨hd, (fgpt_ratio hd.1 hd.2 hm hx0 hx1 hs).2 hle⟩

end FGPT
