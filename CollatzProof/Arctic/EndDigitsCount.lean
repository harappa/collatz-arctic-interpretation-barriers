/-
General counting lemmas for part (ii) of Lemma 6.4 (digits of the end point).
The main part (the specialization to the setting of Lemma 6.4) is in `CollatzProof/Arctic/EndDigits.lean`.

* `card_filter_mod_Ico_bounds`: in an interval of length `Λ`, the number of elements with residue `j` modulo `M` is between `Λ/M - 1` and `Λ/M + 1`.
* `residue_dev`: if a weight `c` on `[h0, h1]` is at most `C + 1` at every point and at least `C` except at the two ends, then the sum over the residue class `j`
  is within `3C + Λ/M + 1` of `1/M` of the total sum (the counting form of "an almost uniform integer on an interval of length `Λ`
  is close to uniform modulo `2^b`").
* `ap_fiber_le`, `ap_fiber_ge`: for the floor of an arithmetic progression, `u ↦ ⌊(A + D u)/P⌋`, each fiber has at most `⌊P/D⌋ + 1` points,
  and at least `⌊P/D⌋` points for values other than the two extremes ("each value of `h` is taken by `⌊2^(n-w)/Q⌋` or `⌈·⌉` values of `u`").
* `ap_floor_mod_dev`: combining the two, the sum of absolute differences between the distribution of the counts of `⌊(A + D u)/P⌋ mod M` and the uniform distribution is
  at most `(3 M P/D + N D/P + 2 + M)/N`.
-/
import Mathlib

namespace Collatz.Arctic

open Finset

namespace EndDigits

/-! ### Number of residues in an interval, and the weight of each residue class -/

/-- Among `M` consecutive numbers, exactly one has residue `j` modulo `M`. -/
lemma card_filter_mod_block (a M j : ℕ) (hj : j < M) :
    #{m ∈ Ico a (a + M) | m % M = j} = 1 := by
  rw [Nat.filter_Ico_card_eq_of_periodic _ _ _ (fun x => by simp [Nat.add_mod_right]),
    Nat.count_eq_card_filter_range, Finset.card_eq_one]
  refine ⟨j, ?_⟩
  ext m
  simp only [mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hm, rfl⟩
    exact (Nat.mod_eq_of_lt hm).symm
  · rintro rfl
    exact ⟨hj, Nat.mod_eq_of_lt hj⟩

/-- In `q` complete periods, the number of elements with residue `j` is `q`. -/
lemma card_filter_mod_blocks (a q M j : ℕ) (hj : j < M) :
    #{m ∈ Ico a (a + q * M) | m % M = j} = q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hsplit : Ico a (a + (q + 1) * M)
        = Ico a (a + q * M) ∪ Ico (a + q * M) (a + q * M + M) := by
      rw [Ico_union_Ico_eq_Ico (Nat.le_add_right _ _) (Nat.le_add_right _ _)]
      congr 1
      ring
    rw [hsplit, filter_union,
      card_union_of_disjoint (disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _)), ih,
      card_filter_mod_block _ _ _ hj]

/-- In an interval of length `Λ`, the number of elements with residue `j` modulo `M` is between `Λ/M - 1` and `Λ/M + 1`. -/
lemma card_filter_mod_Ico_bounds (a Λ M j : ℕ) (hj : j < M) :
    (Λ : ℚ) / M - 1 ≤ (#{m ∈ Ico a (a + Λ) | m % M = j} : ℚ) ∧
      (#{m ∈ Ico a (a + Λ) | m % M = j} : ℚ) ≤ (Λ : ℚ) / M + 1 := by
  have hM : 0 < M := by omega
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < M ∧ Λ = q * M + s :=
    ⟨Λ / M, Λ % M, Nat.mod_lt _ hM, by rw [mul_comm]; exact (Nat.div_add_mod Λ M).symm⟩
  have hsplit : Ico a (a + (q * M + s)) = Ico a (a + q * M) ∪ Ico (a + q * M) (a + q * M + s) := by
    rw [Ico_union_Ico_eq_Ico (Nat.le_add_right _ _) (Nat.le_add_right _ _), add_assoc]
  have hcard : #{m ∈ Ico a (a + (q * M + s)) | m % M = j}
      = q + #{m ∈ Ico (a + q * M) (a + q * M + s) | m % M = j} := by
    rw [hsplit, filter_union,
      card_union_of_disjoint (disjoint_filter_filter (Ico_disjoint_Ico_consecutive _ _ _)),
      card_filter_mod_blocks _ _ _ _ hj]
  have hrem : #{m ∈ Ico (a + q * M) (a + q * M + s) | m % M = j} ≤ 1 := by
    calc _ ≤ #{m ∈ Ico (a + q * M) (a + q * M + M) | m % M = j} :=
          card_le_card (filter_subset_filter _ (Ico_subset_Ico le_rfl (by omega)))
      _ = 1 := card_filter_mod_block _ _ _ hj
  rw [hcard]
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hsq : (s : ℚ) < M := by exact_mod_cast hs
  have hrq : ((#{m ∈ Ico (a + q * M) (a + q * M + s) | m % M = j} : ℕ) : ℚ) ≤ 1 := by
    exact_mod_cast hrem
  have hdiv : ((q * M + s : ℕ) : ℚ) / M = q + s / M := by
    push_cast
    field_simp
  have hsM : (s : ℚ) / M < 1 := (div_lt_one hMq).2 hsq
  have hsM0 : (0 : ℚ) ≤ s / M := by positivity
  rw [hdiv]
  push_cast
  constructor <;> linarith

/-- Upper and lower bounds on sums of weights: `T ⊆ [h0, h1]`, `c ≤ C + 1` at every point, and `C ≤ c` except at the two ends. -/
lemma sum_weight_bounds (c : ℕ → ℕ) (h0 h1 C : ℕ) (T : Finset ℕ) (hT : T ⊆ Icc h0 h1)
    (hup : ∀ m ∈ Icc h0 h1, c m ≤ C + 1)
    (hlo : ∀ m ∈ Icc h0 h1, m ≠ h0 → m ≠ h1 → C ≤ c m) :
    ∑ m ∈ T, c m ≤ #T * (C + 1) ∧ #T * C ≤ ∑ m ∈ T, c m + 2 * C := by
  constructor
  · calc ∑ m ∈ T, c m ≤ #T • (C + 1) := sum_le_card_nsmul _ _ _ (fun m hm => hup m (hT hm))
      _ = #T * (C + 1) := smul_eq_mul _ _
  · have hA : #(T.filter (fun m => m ≠ h0 ∧ m ≠ h1)) * C ≤ ∑ m ∈ T, c m := by
      calc #(T.filter (fun m => m ≠ h0 ∧ m ≠ h1)) * C
          = #(T.filter (fun m => m ≠ h0 ∧ m ≠ h1)) • C := (smul_eq_mul _ _).symm
        _ ≤ ∑ m ∈ T.filter (fun m => m ≠ h0 ∧ m ≠ h1), c m :=
            card_nsmul_le_sum _ _ _ (fun m hm => by
              rw [mem_filter] at hm
              exact hlo m (hT hm.1) hm.2.1 hm.2.2)
        _ ≤ ∑ m ∈ T, c m := sum_le_sum_of_subset (filter_subset _ _)
    have hB : #(T.filter (fun m => ¬(m ≠ h0 ∧ m ≠ h1))) ≤ 2 := by
      calc _ ≤ #({h0, h1} : Finset ℕ) := card_le_card (fun m hm => by
              rw [mem_filter] at hm
              simp only [mem_insert, mem_singleton]
              tauto)
        _ ≤ 2 := card_le_two
    have hC := card_filter_add_card_filter_not (s := T) (fun m => m ≠ h0 ∧ m ≠ h1)
    have hD := Nat.mul_le_mul_right C hB
    nlinarith

/-- **The weight of each residue class (general form)**: if a weight `c` on `[h0, h1]` is at most `C + 1` at every point and at least
`C` except at the two ends, then the sum over residue `j` differs from `1/M` of the total sum by at most `3C + Λ/M + 1` (`Λ := h1 + 1 - h0`). -/
theorem residue_dev (c : ℕ → ℕ) (h0 h1 M C j : ℕ) (hj : j < M) (h01 : h0 ≤ h1)
    (hup : ∀ m ∈ Icc h0 h1, c m ≤ C + 1)
    (hlo : ∀ m ∈ Icc h0 h1, m ≠ h0 → m ≠ h1 → C ≤ c m) :
    |((∑ m ∈ Icc h0 h1 with m % M = j, c m : ℕ) : ℚ) - ((∑ m ∈ Icc h0 h1, c m : ℕ) : ℚ) / M|
      ≤ 3 * C + ((h1 + 1 - h0 : ℕ) : ℚ) / M + 1 := by
  have hM : 0 < M := by omega
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℚ) ≤ M := by exact_mod_cast hM
  have hIcc : Icc h0 h1 = Ico h0 (h0 + (h1 + 1 - h0)) := by
    rw [← Ico_add_one_right_eq_Icc]
    congr 1
    omega
  set Λ := h1 + 1 - h0 with hΛ
  have hcardS : #(Icc h0 h1) = Λ := by rw [Nat.card_Icc]
  obtain ⟨hr1, hr2⟩ := card_filter_mod_Ico_bounds h0 Λ M j hj
  rw [← hIcc] at hr1 hr2
  set R := (Icc h0 h1).filter (fun m => m % M = j) with hR
  obtain ⟨hR1, hR2⟩ := sum_weight_bounds c h0 h1 C R (filter_subset _ _) hup hlo
  obtain ⟨hS1, hS2⟩ := sum_weight_bounds c h0 h1 C (Icc h0 h1) subset_rfl hup hlo
  rw [hcardS] at hS1 hS2
  set cnt := ∑ m ∈ R, c m
  set N := ∑ m ∈ Icc h0 h1, c m
  -- move to the rationals
  have q1 : (cnt : ℚ) ≤ #R * (C + 1) := by exact_mod_cast hR1
  have q2 : (#R : ℚ) * C ≤ cnt + 2 * C := by exact_mod_cast hR2
  have q3 : (N : ℚ) ≤ Λ * (C + 1) := by exact_mod_cast hS1
  have q4 : (Λ : ℚ) * C ≤ N + 2 * C := by exact_mod_cast hS2
  have hr1' : (Λ : ℚ) - M ≤ M * #R := by
    have := mul_le_mul_of_nonneg_left hr1 hMq.le
    rw [mul_sub, mul_div_cancel₀ _ hMq.ne', mul_one] at this
    exact this
  have hr2' : (M : ℚ) * #R ≤ Λ + M := by
    have := mul_le_mul_of_nonneg_left hr2 hMq.le
    rw [mul_add, mul_div_cancel₀ _ hMq.ne', mul_one] at this
    exact this
  have hC0 : (0 : ℚ) ≤ C := Nat.cast_nonneg _
  have key : |(M : ℚ) * cnt - N| ≤ 3 * M * C + Λ + M := by
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hr1' hC0, mul_le_mul_of_nonneg_left q2 hMq.le]
    · nlinarith [mul_le_mul_of_nonneg_right hr2' (by linarith : (0 : ℚ) ≤ C + 1),
        mul_le_mul_of_nonneg_left q1 hMq.le, mul_le_mul_of_nonneg_right hM1 hC0]
  have e1 : (cnt : ℚ) - N / M = ((M : ℚ) * cnt - N) / M := by field_simp
  have e2 : 3 * (C : ℚ) + Λ / M + 1 = (3 * M * C + Λ + M) / M := by field_simp
  rw [e1, e2, abs_div, abs_of_pos hMq]
  exact div_le_div_of_nonneg_right key hMq.le

/-! ### Floors of arithmetic progressions -/

/-- For the floor of an arithmetic progression, `u ↦ ⌊(A + D u)/P⌋`, each fiber has at most `⌊P/D⌋ + 1` points. -/
lemma ap_fiber_le (A D P N m : ℕ) (hD : 0 < D) (hP : 0 < P) :
    #{u ∈ range N | (A + D * u) / P = m} ≤ P / D + 1 := by
  set S := {u ∈ range N | (A + D * u) / P = m} with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]
    simp
  · set a := S.min' hne
    have ha : a ∈ S := S.min'_mem hne
    have hsub : S ⊆ Icc a (a + P / D) := by
      intro u hu
      have hau : a ≤ u := S.min'_le u hu
      rw [hS, mem_filter] at hu ha
      have h1 : m * P ≤ A + D * a := by
        rw [← ha.2]
        exact Nat.div_mul_le_self _ _
      have h2 : A + D * u < m * P + P := by
        rw [← hu.2]
        exact Nat.lt_div_mul_add hP
      have h3 : (u - a) * D ≤ P := by
        have e : D * u = D * a + (u - a) * D := by
          rw [mul_comm (u - a) D, ← mul_add, Nat.add_sub_cancel' hau]
        omega
      have h4 := (Nat.le_div_iff_mul_le hD).2 h3
      rw [mem_Icc]
      omega
    calc #S ≤ #(Icc a (a + P / D)) := card_le_card hsub
      _ = P / D + 1 := by rw [Nat.card_Icc, add_assoc, Nat.add_sub_cancel_left]

/-- For values `m` other than the two extremes (`⌊A/P⌋ < m < ⌊(A + D(N-1))/P⌋`), the fiber has at least `⌊P/D⌋` points. -/
lemma ap_fiber_ge (A D P N m : ℕ) (hD : 0 < D) (hP : 0 < P)
    (hm0 : A / P < m) (hm1 : m < (A + D * (N - 1)) / P) :
    P / D ≤ #{u ∈ range N | (A + D * u) / P = m} := by
  have hxA : A < m * P := (Nat.div_lt_iff_lt_mul hP).1 hm0
  have hend : m * P + P ≤ A + D * (N - 1) := by
    have h1 := Nat.div_mul_le_self (A + D * (N - 1)) P
    have h2 : (m + 1) * P ≤ (A + D * (N - 1)) / P * P := Nat.mul_le_mul_right _ hm1
    rw [add_mul, one_mul] at h2
    omega
  -- the first index a := ⌈(mP - A)/D⌉; write the product m P as A + x with a variable x
  obtain ⟨x, hx⟩ : ∃ x, m * P = A + x := ⟨m * P - A, by omega⟩
  obtain ⟨a, hDa⟩ : ∃ a, x ≤ D * a ∧ D * a < x + D := by
    refine ⟨(x + D - 1) / D, ?_⟩
    obtain ⟨y, hy⟩ : ∃ y, x + D - 1 = y := ⟨_, rfl⟩
    rw [hy]
    have h1 := Nat.div_add_mod y D
    have h2 := Nat.mod_lt y hD
    omega
  have hDP : D * (P / D) ≤ P := Nat.mul_div_le P D
  calc P / D = #((range (P / D)).map (addLeftEmbedding a)) := by rw [card_map, card_range]
    _ ≤ _ := card_le_card (by
        intro u hu
        rw [mem_map] at hu
        obtain ⟨i, hi, rfl⟩ := hu
        rw [mem_range] at hi
        rw [addLeftEmbedding_apply, mem_filter, mem_range]
        have hDi : D * (i + 1) ≤ D * (P / D) := Nat.mul_le_mul_left D hi
        have e : D * (a + i) = D * a + D * i := mul_add _ _ _
        have e' : D * (i + 1) = D * i + D := by ring
        have hlow : m * P ≤ A + D * (a + i) := by omega
        have hhigh : A + D * (a + i) < (m + 1) * P := by rw [add_mul, one_mul]; omega
        refine ⟨?_, Nat.div_eq_of_lt_le hlow hhigh⟩
        have : D * (a + i) < D * (N - 1) := by omega
        have := Nat.lt_of_mul_lt_mul_left this
        omega)

/-- **Residues of the floor of an arithmetic progression (general form)**: as `u` ranges over `[0, N)`, the sum of absolute differences between
the distribution of the counts of `⌊(A + D u)/P⌋ mod M` and the uniform distribution is at most `(3 M P/D + N D/P + 2 + M)/N`. -/
theorem ap_floor_mod_dev (A D P N M : ℕ) (hD : 0 < D) (hP : 0 < P) (hN : 0 < N) (hM : 0 < M) :
    ∑ j ∈ range M, |(#{u ∈ range N | (A + D * u) / P % M = j} : ℚ) / N - 1 / M|
      ≤ (3 * M * ((P : ℚ) / D) + N * D / P + 2 + M) / N := by
  set h0 := A / P
  set h1 := (A + D * (N - 1)) / P
  set C := P / D
  let c : ℕ → ℕ := fun m => #{u ∈ range N | (A + D * u) / P = m}
  have h01 : h0 ≤ h1 := Nat.div_le_div_right (Nat.le_add_right _ _)
  have hmaps : Set.MapsTo (fun u => (A + D * u) / P) ↑(range N) ↑(Icc h0 h1) := by
    intro u hu
    simp only [coe_range, Set.mem_Iio] at hu
    simp only [coe_Icc, Set.mem_Icc]
    refine ⟨Nat.div_le_div_right (Nat.le_add_right _ _), Nat.div_le_div_right ?_⟩
    have := Nat.mul_le_mul_left D (show u ≤ N - 1 by omega)
    omega
  -- the total sum is N
  have hNsum : N = ∑ m ∈ Icc h0 h1, c m := by
    have := card_eq_sum_card_fiberwise hmaps
    rwa [card_range] at this
  -- the count of residue j is the sum of the fibers of the values with residue j
  have hcnt : ∀ j, #{u ∈ range N | (A + D * u) / P % M = j}
      = ∑ m ∈ Icc h0 h1 with m % M = j, c m := by
    intro j
    have hmaps' : Set.MapsTo (fun u => (A + D * u) / P)
        ↑({u ∈ range N | (A + D * u) / P % M = j}) ↑((Icc h0 h1).filter (fun m => m % M = j)) := by
      intro u hu
      simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hu
      simp only [coe_filter, Set.mem_ofPred_eq]
      exact ⟨by simpa using hmaps (by simpa using hu.1), hu.2⟩
    rw [card_eq_sum_card_fiberwise hmaps']
    refine sum_congr rfl (fun m hm => ?_)
    rw [mem_filter] at hm
    rw [filter_filter]
    congr 1
    refine filter_congr (fun u _ => ?_)
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨by rw [h]; exact hm.2, h⟩
  have hup : ∀ m ∈ Icc h0 h1, c m ≤ C + 1 := fun m _ => ap_fiber_le A D P N m hD hP
  have hlo : ∀ m ∈ Icc h0 h1, m ≠ h0 → m ≠ h1 → C ≤ c m := by
    intro m hm hm0 hm1
    rw [mem_Icc] at hm
    exact ap_fiber_ge A D P N m hD hP (by omega) (by omega)
  -- Λ := h1 + 1 - h0 ≤ D(N-1)/P + 2
  have hΛ : h1 + 1 - h0 ≤ D * (N - 1) / P + 2 := by
    have := Nat.add_div (a := A) (b := D * (N - 1)) hP
    split_ifs at this <;> omega
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hPq : (0 : ℚ) < P := by exact_mod_cast hP
  have hΛq : ((h1 + 1 - h0 : ℕ) : ℚ) ≤ N * D / P + 2 := by
    have e1 : ((h1 + 1 - h0 : ℕ) : ℚ) ≤ ((D * (N - 1) / P : ℕ) : ℚ) + 2 := by exact_mod_cast hΛ
    have e2 : ((D * (N - 1) / P : ℕ) : ℚ) ≤ ((D * (N - 1) : ℕ) : ℚ) / P := Nat.cast_div_le
    have e3 : ((D * (N - 1) : ℕ) : ℚ) ≤ (N : ℚ) * D := by
      have : D * (N - 1) ≤ N * D := by rw [mul_comm N]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast this
    have e4 : ((D * (N - 1) : ℕ) : ℚ) / P ≤ (N : ℚ) * D / P := div_le_div_of_nonneg_right e3 hPq.le
    linarith
  have hCq : (C : ℚ) ≤ (P : ℚ) / D := Nat.cast_div_le
  -- the bound for each j
  have hj : ∀ j ∈ range M, |(#{u ∈ range N | (A + D * u) / P % M = j} : ℚ) / N - 1 / M|
      ≤ (3 * C + ((h1 + 1 - h0 : ℕ) : ℚ) / M + 1) / N := by
    intro j hjM
    rw [mem_range] at hjM
    have hd := residue_dev c h0 h1 M C j hjM h01 hup hlo
    rw [← hNsum, ← hcnt j] at hd
    have e : (#{u ∈ range N | (A + D * u) / P % M = j} : ℚ) / N - 1 / M
        = ((#{u ∈ range N | (A + D * u) / P % M = j} : ℚ) - N / M) / N := by
      field_simp
    rw [e, abs_div, abs_of_pos hNq]
    exact div_le_div_of_nonneg_right hd hNq.le
  calc _ ≤ ∑ j ∈ range M, (3 * C + ((h1 + 1 - h0 : ℕ) : ℚ) / M + 1) / N := sum_le_sum hj
    _ = M * (3 * C + ((h1 + 1 - h0 : ℕ) : ℚ) / M + 1) / N := by
        rw [sum_const, card_range, nsmul_eq_mul, mul_div_assoc]
    _ = (3 * M * C + ((h1 + 1 - h0 : ℕ) : ℚ) + M) / N := by
        congr 1
        field_simp
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hNq.le
        have := mul_le_mul_of_nonneg_left hCq (by positivity : (0 : ℚ) ≤ 3 * M)
        linarith

end EndDigits

end Collatz.Arctic
