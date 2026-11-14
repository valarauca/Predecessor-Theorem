import Carpooling.Permutohedron

/-!
  Hypergraph uncrossing lower bound on trap demand (carpooling paper §3,
  Theorem 3.3).
-/

open Finset FGPT

namespace Carpooling

variable {m : ℕ}

/-- Multiplicity `c_i = #{A ∈ F : i ∈ A}` of a coordinate in a family
    (paper Theorem 3.3). -/
def mult (F : Finset (Finset (Fin m))) (i : Fin m) : ℕ := (F.filter fun A => i ∈ A).card

/-- Superlevel set `E_j = {i : c_i ≥ j}` (paper Theorem 3.3). -/
def level (F : Finset (Finset (Fin m))) (j : ℕ) : Finset (Fin m) :=
  univ.filter fun i => j ≤ mult F i

/-- Pair multiplicity `#{A ∈ F : i ∈ A ∧ r ∈ A}` (paper Theorem 3.3). -/
def pairMult (F : Finset (Finset (Fin m))) (i r : Fin m) : ℕ :=
  (F.filter fun A => i ∈ A ∧ r ∈ A).card

/-- `c_i ≤ |F|`. -/
lemma mult_le_card (F : Finset (Finset (Fin m))) (i : Fin m) : mult F i ≤ F.card :=
  Finset.card_filter_le _ _

/-- `#{j ∈ [1, t] : j ≤ a} = a` for `a ≤ t`. -/
lemma card_filter_Icc_le {a t : ℕ} (h : a ≤ t) :
    ((Icc 1 t).filter fun j => j ≤ a).card = a := by
  have hs : (Icc 1 t).filter (fun j => j ≤ a) = Icc 1 a := by
    ext j
    simp only [mem_filter, mem_Icc]
    omega
  rw [hs, Nat.card_Icc]
  omega

/-- `#{j ∈ [1, t] : j ≤ a ∧ j ≤ b} = min a b` once `min a b ≤ t`. -/
lemma card_filter_Icc_min {a b t : ℕ} (h : min a b ≤ t) :
    ((Icc 1 t).filter fun j => j ≤ a ∧ j ≤ b).card = min a b := by
  have hs : (Icc 1 t).filter (fun j => j ≤ a ∧ j ≤ b) = Icc 1 (min a b) := by
    ext j
    have h' := h
    simp only [mem_filter, mem_Icc, le_min_iff] at h' ⊢
    omega
  rw [hs, Nat.card_Icc]
  omega

/-- A subset sum as a sum over all coordinates. -/
lemma sum_eq_sum_ite {M : Type*} [AddCommMonoid M] (A : Finset (Fin m)) (f : Fin m → M) :
    (∑ i ∈ A, f i) = ∑ i, if i ∈ A then f i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

/-- Layer-cake identity: `∑_{A ∈ F} f(A) = ∑_{j=1}^{|F|} f(E_j)` for additive
    set functions `f` (paper Theorem 3.3). -/
lemma sum_family_eq_sum_levels (F : Finset (Finset (Fin m))) (f : Fin m → ℝ) :
    (∑ A ∈ F, ∑ i ∈ A, f i) = ∑ j ∈ Icc 1 F.card, ∑ i ∈ level F j, f i := by
  have h2 : ∀ j, (∑ i ∈ level F j, f i) = ∑ i, if j ≤ mult F i then f i else 0 :=
    fun j => by rw [level, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun A _ => sum_eq_sum_ite A f),
    Finset.sum_congr rfl (fun j _ => h2 j)]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [card_filter_Icc_le (mult_le_card F i)]
  rfl

/-- `#{A ∈ F : i, r ∈ A} ≤ min(c_i, c_r)` (paper Theorem 3.3). -/
lemma pairMult_le_min (F : Finset (Finset (Fin m))) (i r : Fin m) :
    pairMult F i r ≤ min (mult F i) (mult F r) :=
  le_min
    (Finset.card_le_card fun A hA => by
      simp only [mem_filter] at hA ⊢
      exact ⟨hA.1, hA.2.1⟩)
    (Finset.card_le_card fun A hA => by
      simp only [mem_filter] at hA ⊢
      exact ⟨hA.1, hA.2.2⟩)

/-- `∑_j e_j² = ∑_{i, r} min(c_i, c_r)` (paper Theorem 3.3). -/
lemma sum_level_sq (F : Finset (Finset (Fin m))) :
    (∑ j ∈ Icc 1 F.card, (level F j).card ^ 2) =
      ∑ i, ∑ r, min (mult F i) (mult F r) := by
  calc (∑ j ∈ Icc 1 F.card, (level F j).card ^ 2)
      = ∑ j ∈ Icc 1 F.card, ∑ i, ∑ r,
          (if j ≤ mult F i ∧ j ≤ mult F r then 1 else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [level, Finset.card_filter, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
        rw [ite_zero_mul_ite_zero, mul_one]
    _ = ∑ i, ∑ r, ∑ j ∈ Icc 1 F.card,
          (if j ≤ mult F i ∧ j ≤ mult F r then 1 else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ r, min (mult F i) (mult F r) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
        rw [← Finset.card_filter,
          card_filter_Icc_min (le_trans (min_le_left _ _) (mult_le_card F i))]

/-- `∑_ℓ a_ℓ² = ∑_{i, r} #{ℓ : i, r ∈ A_ℓ}` (paper Theorem 3.3). -/
lemma sum_card_sq (F : Finset (Finset (Fin m))) :
    (∑ A ∈ F, A.card ^ 2) = ∑ i, ∑ r, pairMult F i r := by
  calc (∑ A ∈ F, A.card ^ 2)
      = ∑ A ∈ F, ∑ i, ∑ r, (if i ∈ A ∧ r ∈ A then 1 else 0) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.card_eq_sum_ones, sum_eq_sum_ite, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
        rw [ite_zero_mul_ite_zero, mul_one]
    _ = ∑ i, ∑ r, ∑ A ∈ F, (if i ∈ A ∧ r ∈ A then 1 else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ r, pairMult F i r := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
        rw [← Finset.card_filter]
        rfl

/-- Sums of the quadratic profile: `∑ β(g) = (m ∑ g - ∑ g²) / (m - 1)`. -/
lemma sum_beta {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    (∑ i ∈ s, beta m (g i)) =
      ((m : ℝ) * (∑ i ∈ s, g i) - ∑ i ∈ s, g i ^ 2) / ((m : ℝ) - 1) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold beta
  ring

/-- Theorem 3.3 (hypergraph uncrossing lower bound on trap demand). If `F` is an
    inclusion-minimal subfamily of the dangerous family of `q ∈ P_m` whose
    intersection misses the support, then `|F| ≥ 2` and `d > |F| / (m - 1)`. -/
theorem uncrossing (hm : 2 ≤ m) {d : ℝ} (hd : 0 ≤ d) {x q : Fin m → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1) (hq : q ∈ Pm m 1)
    {F : Finset (Finset (Fin m))} (hF : F ⊆ danger (fun r => 1 * beta m r) d x q)
    (hcov : ∀ k ∈ supp x, ∃ A ∈ F, k ∉ A)
    (hmin : ∀ G ⊂ F, ¬ ∀ k ∈ supp x, ∃ A ∈ G, k ∉ A) :
    2 ≤ F.card ∧ (F.card : ℝ) / ((m : ℝ) - 1) < d := by
  have hkey : ∀ A ∈ F, ∃ k, k ∈ supp x ∧ k ∉ A ∧ ∀ B ∈ F, B ≠ A → k ∈ B := by
    intro A hA
    have h := hmin (F.erase A) (Finset.erase_ssubset hA)
    push Not at h
    obtain ⟨k, hkS, hk⟩ := h
    refine ⟨k, hkS, fun hkA => ?_, fun B hB hBA => hk B (mem_erase.mpr ⟨hBA, hB⟩)⟩
    obtain ⟨C, hC, hkC⟩ := hcov k hkS
    by_cases hCA : C = A
    · rw [hCA] at hkC
      exact hkC hkA
    · exact hkC (hk C (mem_erase.mpr ⟨hCA, hC⟩))
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  choose! kf hkS hkA hkB using hkey
  obtain ⟨k0, hk0⟩ := supp_nonempty hx1
  obtain ⟨A0, hA0, -⟩ := hcov k0 hk0
  have hFne : F.Nonempty := ⟨A0, hA0⟩
  have ht2 : 2 ≤ F.card := by
    by_contra hlt
    have hle : F.card ≤ 1 := by omega
    obtain ⟨i, hiA, hiS⟩ := danger_meets_supp hq (hF hA0)
    obtain ⟨B, hB, hiB⟩ := hcov i hiS
    rw [Finset.card_le_one.mp hle B hB A0 hA0] at hiB
    exact hiB hiA
  have hinj : ∀ A ∈ F, ∀ B ∈ F, kf A = kf B → A = B := by
    intro A hA B hB h
    by_contra hAB
    have h1 := hkB A hA B hB (Ne.symm hAB)
    rw [h] at h1
    exact hkA B hB h1
  have hmult : ∀ A ∈ F, F.card - 1 ≤ mult F (kf A) := by
    intro A hA
    rw [← Finset.card_erase_of_mem hA]
    exact Finset.card_le_card fun C hC => by
      rw [mem_erase] at hC
      exact mem_filter.mpr ⟨hC.2, hkB A hA C hC.2 hC.1⟩
  have hpair : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → pairMult F (kf A) (kf B) ≤ F.card - 2 := by
    intro A hA B hB hAB
    have hB' : B ∈ F.erase A := mem_erase.mpr ⟨Ne.symm hAB, hB⟩
    have hc : ((F.erase A).erase B).card = F.card - 2 := by
      rw [Finset.card_erase_of_mem hB', Finset.card_erase_of_mem hA]
      omega
    rw [← hc]
    exact Finset.card_le_card fun C hC => by
      rw [mem_filter] at hC
      refine mem_erase.mpr ⟨fun hCB => ?_, mem_erase.mpr ⟨fun hCA => ?_, hC.1⟩⟩
      · rw [hCB] at hC
        exact hkA B hB hC.2.2
      · rw [hCA] at hC
        exact hkA A hA hC.2.1
  have hsq : (∑ A ∈ F, A.card ^ 2) + (F.card * F.card - F.card) ≤
      ∑ j ∈ Icc 1 F.card, (level F j).card ^ 2 := by
    rw [sum_card_sq, sum_level_sq]
    set P := F.offDiag.image (fun p => (kf p.1, kf p.2)) with hP
    have hPc : P.card = F.card * F.card - F.card := by
      rw [hP, Finset.card_image_of_injOn, Finset.offDiag_card]
      rintro ⟨A, B⟩ hAB ⟨A', B'⟩ hAB' h
      simp only [coe_offDiag, Set.mem_offDiag, Prod.mk.injEq] at hAB hAB' h ⊢
      exact ⟨hinj A hAB.1 A' hAB'.1 h.1, hinj B hAB.2.1 B' hAB'.2.1 h.2⟩
    have hPs : P.card = ∑ p : Fin m × Fin m, if p ∈ P then 1 else 0 := by
      rw [← Finset.card_filter]
      congr 1
      ext p
      simp
    rw [← hPc, hPs, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type',
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hp : p ∈ P
    · rw [if_pos hp]
      obtain ⟨⟨A, B⟩, hAB, rfl⟩ := mem_image.mp hp
      rw [mem_offDiag] at hAB
      obtain ⟨hA, hB, hne⟩ := hAB
      have h1 := hmult A hA
      have h2 := hmult B hB
      have h3 := hpair A hA B hB hne
      change pairMult F (kf A) (kf B) + 1 ≤ min (mult F (kf A)) (mult F (kf B))
      exact le_min (by omega) (by omega)
    · rw [if_neg hp, add_zero]
      exact pairMult_le_min F p.1 p.2
  have hc : (0 : ℝ) < (m : ℝ) - 1 := cast_sub_one_pos hm
  have hR1 := sum_family_eq_sum_levels F q
  have hR3 : (∑ A ∈ F, (A.card : ℝ)) = ∑ j ∈ Icc 1 F.card, ((level F j).card : ℝ) := by
    have h := sum_family_eq_sum_levels F (fun _ => (1 : ℝ))
    simpa using h
  have hR2 : (∑ A ∈ F, ∑ i ∈ A, x i) ≤ (F.card : ℝ) - 1 := by
    rw [sum_family_eq_sum_levels F x]
    obtain ⟨s, hs⟩ : ∃ s, F.card = s + 1 := ⟨F.card - 1, by omega⟩
    have htop : (∑ i ∈ level F (s + 1), x i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      by_contra hxi
      have hiS : i ∈ supp x := by simp [supp, hxi]
      obtain ⟨A, hA, hiA⟩ := hcov i hiS
      have hlt : mult F i ≤ F.card - 1 := by
        rw [← Finset.card_erase_of_mem hA]
        exact Finset.card_le_card fun C hC => by
          rw [mem_filter] at hC
          refine mem_erase.mpr ⟨fun hCA => ?_, hC.1⟩
          rw [hCA] at hC
          exact hiA hC.2
      simp only [level, mem_filter, mem_univ, true_and] at hi
      omega
    rw [hs, Finset.sum_Icc_succ_top (by omega), htop, add_zero]
    calc (∑ j ∈ Icc 1 s, ∑ i ∈ level F j, x i) ≤ ∑ j ∈ Icc 1 s, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => sum_subset_le_one hx0 hx1 _
      _ = ((s + 1 : ℕ) : ℝ) - 1 := by
          simp
  have hR4 : (∑ A ∈ F, ((∑ i ∈ A, q i) - d * ∑ i ∈ A, x i)) <
      ∑ A ∈ F, -(1 * beta m A.card) :=
    Finset.sum_lt_sum_of_nonempty hFne fun A hA => (mem_danger.mp (hF hA)).2.2
  have hR5 : (∑ j ∈ Icc 1 F.card, -(1 * beta m (level F j).card)) ≤
      ∑ j ∈ Icc 1 F.card, ∑ i ∈ level F j, q i :=
    Finset.sum_le_sum fun j _ => hq.2 (level F j)
  have hsqR : (∑ A ∈ F, (A.card : ℝ) ^ 2) + ((F.card : ℝ) * F.card - F.card) ≤
      ∑ j ∈ Icc 1 F.card, ((level F j).card : ℝ) ^ 2 := by
    have hle : F.card ≤ F.card * F.card := Nat.le_mul_self _
    have h' : ((∑ A ∈ F, A.card ^ 2 + (F.card * F.card - F.card) : ℕ) : ℝ) ≤
        ((∑ j ∈ Icc 1 F.card, (level F j).card ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hsq
    push_cast [Nat.cast_sub hle] at h'
    exact h'
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib, one_mul]
    at hR4 hR5
  rw [sum_beta F (fun A => (A.card : ℝ))] at hR4
  rw [sum_beta (Icc 1 F.card) (fun j => ((level F j).card : ℝ))] at hR5
  have hdx := mul_le_mul_of_nonneg_left hR2 hd
  have key : ((∑ j ∈ Icc 1 F.card, ((level F j).card : ℝ) ^ 2) -
      ∑ A ∈ F, (A.card : ℝ) ^ 2) / ((m : ℝ) - 1) < d * ((F.card : ℝ) - 1) := by
    have e : ((m : ℝ) * (∑ A ∈ F, (A.card : ℝ)) - ∑ A ∈ F, (A.card : ℝ) ^ 2) / ((m : ℝ) - 1) -
        ((m : ℝ) * (∑ j ∈ Icc 1 F.card, ((level F j).card : ℝ)) -
          ∑ j ∈ Icc 1 F.card, ((level F j).card : ℝ) ^ 2) / ((m : ℝ) - 1) =
        ((∑ j ∈ Icc 1 F.card, ((level F j).card : ℝ) ^ 2) -
          ∑ A ∈ F, (A.card : ℝ) ^ 2) / ((m : ℝ) - 1) := by
      rw [hR3]
      ring
    linarith
  rw [div_lt_iff₀ hc] at key
  have ht2R : (2 : ℝ) ≤ F.card := by exact_mod_cast ht2
  refine ⟨ht2, ?_⟩
  rw [div_lt_iff₀ hc]
  nlinarith

/-- Theorem 3.3, trap form: every trap of `P_m` for a generator `(d, x)` has
    demand `d > 2 / (m - 1)`. A minimum-cardinality covering subfamily of the
    dangerous family is inclusion-minimal, so `uncrossing` applies. -/
theorem trap_demand_gt (hm : 2 ≤ m) {d : ℝ} (hd : 0 ≤ d) {x q : Fin m → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1) (hq : q ∈ Pm m 1)
    (htrap : ¬ ∃ k ∈ supp x, step d x k q ∈ Pm m 1) :
    2 / ((m : ℝ) - 1) < d := by
  classical
  have hcov : ∀ k ∈ supp x, ∃ A ∈ danger (fun r => 1 * beta m r) d x q, k ∉ A :=
    (trap_iff_Psub (β := fun r => 1 * beta m r) (by simp) hd hx0 hx1 hq).mp htrap
  set D := danger (fun r : ℕ => 1 * beta m r) d x q
  set C := D.powerset.filter fun G => ∀ k ∈ supp x, ∃ A ∈ G, k ∉ A
  have hCne : C.Nonempty := ⟨D, mem_filter.mpr ⟨mem_powerset_self D, hcov⟩⟩
  obtain ⟨F, hFC, hFmin⟩ := C.exists_min_image Finset.card hCne
  rw [mem_filter, mem_powerset] at hFC
  have hmin : ∀ G ⊂ F, ¬ ∀ k ∈ supp x, ∃ A ∈ G, k ∉ A := by
    intro G hGF hG
    have h := hFmin G (mem_filter.mpr ⟨mem_powerset.mpr (hGF.subset.trans hFC.1), hG⟩)
    exact absurd (Finset.card_lt_card hGF) (not_lt.mpr h)
  obtain ⟨ht, hlt⟩ := uncrossing hm hd hx0 hx1 hq hFC.1 hFC.2 hmin
  have hc := cast_sub_one_pos hm
  calc 2 / ((m : ℝ) - 1) ≤ F.card / ((m : ℝ) - 1) := by
        gcongr
        exact_mod_cast ht
    _ < d := hlt

/-- Sufficiency in Theorem 4.4(a) obtained independently from Theorem 3.3:
    for `0 ≤ d ≤ 2 / (m - 1)` every state of `P_m` has a supported move that
    stays in `P_m`. -/
theorem Pm_safe_of_le_uncrossing (hm : 2 ≤ m) {d : ℝ} (hd : 0 ≤ d)
    (hdm : d ≤ 2 / ((m : ℝ) - 1)) {x : Fin m → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : (∑ i, x i) = 1) :
    ∀ q ∈ Pm m 1, ∃ k ∈ supp x, step d x k q ∈ Pm m 1 := by
  intro q hq
  by_contra htrap
  have h := trap_demand_gt hm hd hx0 hx1 hq htrap
  linarith

end Carpooling
