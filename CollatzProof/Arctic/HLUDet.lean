/-
The deterministic part of the hypothesis `HLeftUse` (`CoreHyp.lean`), part 1: uses of the left-end rules and the
block boundary points of the model of `T`. The real-valued mantissa criterion and the main theorem `left_use_ge` are in `HLUDetReal.lean`.

Correspondence with the paper (Proposition 6.7; proof of Proposition B.9 (ii)):
* Step (a) (system `S_T`): the canonical derivation of an odd `n` uses the left-end rule of the digit `d = ⌊T(n)/2^{ℓ(n)-2}⌋ - 3` once
  (`ℓ(n) - 2 = ⌊log₂ n⌋ - 1`). `hlu_uses_left_odd`, `hlu_uses_left_even`. The proof is an induction on the sweep `sweepRules`
  (the same decomposition `y = 2y' + b` as in `Canon.sweep_chain`): the last carry is determined by the top digits of `(3y + d)`
  (`hlu_sweep_count`).
* Step (b), left-end rules: every block begins with an odd step (`hlu_P_odd`), so at each block boundary point
  `P_i = T^{L_i} x₀` (`L_i = blockEnd β i`) the rule `leftRule d` is used once if the top window is `3 + d`. The boundary points
  occur at different steps, so the number of uses is at least the number of boundaries satisfying the condition (`hlu_usesOrbit_ge_boundary`).
* Shape of the boundary points (`terras_prefix`): `P_i = c_i + 3^{a_i} (r' + 2^{m - L_i} t)`, `c_i < 3^{a_i}`, `r' < 2^{m - L_i}`
  (`hlu_P_eq`). Hence `3^{a_i} 2^{m-L_i} t ≤ P_i < 3^{a_i} 2^{m-L_i} (t + 1)` (`hlu_P_bounds`). This is the input for the log of the mantissa
  being close to `{a_i log₂ 3 + log₂ t}`.
* `a_i` (number of odd steps) is the sum over the blocks (5 for `X'`, 7 for `Y'`): `hlu_terrasA_parityOf` (definitionally the same shape as
  `oddPrefix` in `HLUWalk.lean`).
-/
import CollatzProof.Arctic.Family

namespace Collatz.Arctic

/-! ## Left-end rules and top bits (Proposition B.9 (ii)(a)) -/

open Letter in
/-- A carry rule (`aRule`) is not a left-end rule (its left-hand side starts with `f` or `t`, that of a left-end rule with `lft`). -/
lemma hlu_aRule_ne_left (b d e : ℕ) : aRule b d ≠ leftRule e := by
  unfold aRule leftRule bitL
  split_ifs <;> simp

open Letter in
/-- The odd-step rule `t. → 2.` is not a left-end rule. -/
lemma hlu_dyn_odd_ne_left (e : ℕ) : (⟨[t, rgt], [d2, rgt]⟩ : Rule) ≠ leftRule e := by
  unfold leftRule
  split_ifs <;> simp

open Letter in
/-- The even-step rule `f. → .` is not a left-end rule. -/
lemma hlu_dyn_even_ne_left (e : ℕ) : (⟨[f, rgt], [rgt]⟩ : Rule) ≠ leftRule e := by
  unfold leftRule
  split_ifs <;> simp

/-- `⌊log₂ (2y + b)⌋ = ⌊log₂ y⌋ + 1` (`y ≥ 1`, `b < 2`). -/
lemma hlu_log_two_mul_add (y b : ℕ) (hy : 1 ≤ y) (hb : b < 2) :
    Nat.log 2 (2 * y + b) = Nat.log 2 y + 1 := by
  rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]
  congr 2
  omega

/-- Left-end rule of the sweep: when the ternary digit `d` has crossed `bin'(y)`, the carry `e` is determined by
`(3y + d) / 2^{⌊log₂ y⌋} = 3 + e`, and the left-end rule `leftRule e` is used exactly once. -/
lemma hlu_sweep_count : ∀ y : ℕ, 1 ≤ y → ∀ d : ℕ, d ≤ 2 → ∀ e : ℕ, e ≤ 2 →
    (sweepRules (tailBitsLSB y) d).count (leftRule e)
      = if (3 * y + d) / 2 ^ Nat.log 2 y = 3 + e then 1 else 0 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy d hd e he
    by_cases h1 : y = 1
    · subst h1
      rw [tailBitsLSB_one]
      simp only [sweepRules, Nat.log_one_right, pow_zero, Nat.div_one]
      interval_cases d <;> interval_cases e <;> decide
    · set y' := y / 2 with hy'
      set b := y % 2 with hb
      have hyy : y = 2 * y' + b := by omega
      have hy'1 : 1 ≤ y' := by omega
      have hb2 : b < 2 := by omega
      have hlt : y' < y := by omega
      have hd'2 : (3 * b + d) / 2 ≤ 2 := by omega
      have hlog : Nat.log 2 y = Nat.log 2 y' + 1 := by rw [hyy]; exact hlu_log_two_mul_add y' b hy'1 hb2
      have hdiv : (3 * y + d) / 2 ^ Nat.log 2 y = (3 * y' + (3 * b + d) / 2) / 2 ^ Nat.log 2 y' := by
        rw [hlog, pow_succ, Nat.mul_comm (2 ^ _) 2, ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      rw [hdiv, hyy, tailBitsLSB_two_mul_add y' b hy'1 hb2]
      simp only [sweepRules]
      rw [List.count_cons, ih y' hlt hy'1 _ hd'2 e he]
      have : (aRule b d == leftRule e) = false := by
        simpa using hlu_aRule_ne_left b d e
      rw [this]
      simp

/-- **Left-end rules and top bits** (Proposition B.9 (ii)(a)): the canonical derivation of an odd `n ≥ 3` uses `leftRule d`
(once) if and only if the top window of `T(n)` is `T(n) / 2^{⌊log₂ n⌋ - 1} = 3 + d`. -/
theorem hlu_uses_left_odd (n d : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) (hd : d ≤ 2) :
    uses (leftRule d) n = if T n / 2 ^ (Nat.log 2 n - 1) = 3 + d then 1 else 0 := by
  set y := (n - 1) / 2 with hy
  have hy1 : 1 ≤ y := by omega
  have hny : n = 2 * y + 1 := by omega
  have hT : T n = 3 * y + 2 := by rw [T_of_odd n hodd]; omega
  have hlog : Nat.log 2 n - 1 = Nat.log 2 y := by
    rw [hny, hlu_log_two_mul_add y 1 hy1 (by norm_num)]; omega
  unfold uses canDeriv
  have hne : ¬ n % 2 = 0 := by omega
  simp only [hne, ↓reduceIte]
  rw [List.count_cons, ← hy, hlu_sweep_count y hy1 2 (le_refl 2) d hd, hT, hlog]
  have : ((⟨[Letter.t, Letter.rgt], [Letter.d2, Letter.rgt]⟩ : Rule) == leftRule d) = false := by
    simpa using hlu_dyn_odd_ne_left d
  rw [this]
  simp

/-- The canonical derivation of an even `n` uses no left-end rule. -/
theorem hlu_uses_left_even (n d : ℕ) (hev : n % 2 = 0) : uses (leftRule d) n = 0 := by
  unfold uses canDeriv
  simp only [hev, ↓reduceIte]
  rw [List.count_singleton]
  have : ((⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩ : Rule) == leftRule d) = false := by
    simpa using hlu_dyn_even_ne_left d
  simp [this]

/-! ## Block boundaries -/

/-- The first block of `parityOf`. -/
lemma hlu_parityOf_cons (x : Bool) (β : List Bool) :
    parityOf (x :: β) = (if x then blkX else blkY) ++ parityOf β := by
  simp [parityOf]

/-- `σ = σ_{<i} σ_{≥i}` (the first `i` blocks and the rest). -/
lemma hlu_parityOf_split (β : List Bool) (i : ℕ) :
    parityOf β = parityOf (β.take i) ++ parityOf (β.drop i) := by
  rw [← fam_parityOf_append, List.take_append_drop]

/-- A block has at least 8 steps. -/
lemma hlu_parityOf_length_ge (β : List Bool) : 8 * β.length ≤ (parityOf β).length := by
  rw [(fam_parityOf_counts β).1, fam_length_eq_count]
  omega

/-- After the boundary `L_i` at least one block (at least 8 steps) remains. -/
lemma hlu_blockEnd_add_le (β : List Bool) (i : ℕ) (hi : i < β.length) :
    blockEnd β i + 8 ≤ (parityOf β).length := by
  unfold blockEnd
  rw [hlu_parityOf_split β i, List.length_append]
  have := hlu_parityOf_length_ge (β.drop i)
  rw [List.length_drop] at this
  omega

/-- The boundary positions `L_i` are strictly increasing. -/
lemma hlu_blockEnd_lt_of_lt (β : List Bool) (i j : ℕ) (hij : i < j) (hj : j ≤ β.length) :
    blockEnd β i < blockEnd β j := by
  unfold blockEnd
  obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
  rw [List.take_add, fam_parityOf_append, List.length_append]
  have h := hlu_parityOf_length_ge ((β.drop i).take (k + 1))
  rw [List.length_take, List.length_drop] at h
  have : 1 ≤ min (k + 1) (β.length - i) := by omega
  omega

/-- Blocks begin with an odd step: position `L_i` of `σ` is an odd step. -/
lemma hlu_parity_blockEnd (β : List Bool) (i : ℕ) (hi : i < β.length) :
    (parityOf β).getD (blockEnd β i) false = true := by
  unfold blockEnd
  rw [hlu_parityOf_split β i, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
    List.drop_eq_getElem_cons hi, hlu_parityOf_cons]
  cases β[i] <;> simp [blkX, blkY]

/-- The boundary point `P_i = T^[L_i] x₀` is odd. -/
theorem hlu_P_odd (β : List Bool) (t i : ℕ) (hi : i < β.length) :
    T^[blockEnd β i] (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) % 2 = 1 := by
  have hlt : blockEnd β i < (parityOf β).length := by
    have := hlu_blockEnd_add_le β i hi; omega
  rw [terras_parity (parityOf β) t _ hlt, hlu_parity_blockEnd β i hi]
  rfl

/-- A list sum as a sum over `Finset.range`. -/
lemma hlu_list_sum_range (f : ℕ → ℕ) : ∀ m : ℕ,
    ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- Counting: for an injective reindexing `g` with `u (g i) ≥ 1` for every `i` satisfying `p`, the count is at most the sum. -/
lemma hlu_card_le_sum (n m : ℕ) (g u : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p]
    (hg : ∀ i < n, g i < m) (hmono : ∀ i j, i < j → j < n → g i < g j)
    (hu : ∀ i < n, p i → 1 ≤ u (g i)) :
    ((Finset.range n).filter p).card ≤ ∑ j ∈ Finset.range m, u j := by
  set S := (Finset.range n).filter p with hS
  have hinj : Set.InjOn g (S : Set ℕ) := by
    intro i hi j hj hij
    simp only [hS, Finset.coe_filter, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (hmono i j h hj.1).ne
    · exact h
    · exact absurd hij (hmono j i h hi.1).ne'
  have hsub : S.image g ⊆ Finset.range m := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hiS, rfl⟩ := hj
    rw [hS, Finset.mem_filter, Finset.mem_range] at hiS
    exact Finset.mem_range.mpr (hg i hiS.1)
  calc S.card = ∑ i ∈ S, 1 := Finset.card_eq_sum_ones S
    _ ≤ ∑ i ∈ S, u (g i) := Finset.sum_le_sum (fun i hi => by
        rw [hS, Finset.mem_filter, Finset.mem_range] at hi; exact hu i hi.1 hi.2)
    _ = ∑ j ∈ S.image g, u j := (Finset.sum_image hinj).symm
    _ ≤ ∑ j ∈ Finset.range m, u j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- **Uses of the left-end rules at the boundary points** (Proposition B.9 (ii)(b)): for `t ≥ 1`, the number of block indices `i`
whose boundary point `P_i` has top window `3 + d` is at most the number of uses of `leftRule d` in `m` steps from `x₀`. -/
theorem hlu_usesOrbit_ge_boundary (β : List Bool) (t d : ℕ) (ht : 1 ≤ t) (hd : d ≤ 2) :
    ((Finset.range β.length).filter (fun i =>
        T (T^[blockEnd β i] (terrasR (parityOf β) + 2 ^ (parityOf β).length * t))
          / 2 ^ (Nat.log 2 (T^[blockEnd β i] (terrasR (parityOf β) + 2 ^ (parityOf β).length * t)) - 1)
          = 3 + d)).card
      ≤ usesOrbit (leftRule d) (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) (parityOf β).length := by
  have hlt : ∀ i < β.length, blockEnd β i < (parityOf β).length := fun i hi => by
    have := hlu_blockEnd_add_le β i hi; omega
  unfold usesOrbit
  rw [hlu_list_sum_range]
  refine hlu_card_le_sum _ _ (blockEnd β) _ _ hlt (fun i j hij hj => hlu_blockEnd_lt_of_lt β i j hij hj.le) ?_
  intro i hi hp
  have hodd := hlu_P_odd β t i hi
  have h2 := terras_orbit_two_le (parityOf β) t ht _ (hlt i hi)
  rw [hlu_uses_left_odd _ d (by omega) hodd hd]
  simp [hp]

/-! ## Shape of the boundary points -/

/-- **Shape of the boundary points** (`terras_prefix`): `P_i = c_i + 3^{a_i} (r' + 2^{m - L_i} t)`, `r' < 2^{m - L_i}`. -/
theorem hlu_P_eq (β : List Bool) (t i : ℕ) :
    ∃ r' < 2 ^ ((parityOf β).length - blockEnd β i),
      T^[blockEnd β i] (terrasR (parityOf β) + 2 ^ (parityOf β).length * t)
        = terrasC (parityOf (β.take i)) + 3 ^ terrasA (parityOf (β.take i))
            * (r' + 2 ^ ((parityOf β).length - blockEnd β i) * t) := by
  obtain ⟨r', hr', -, hT⟩ := terras_prefix (parityOf (β.take i)) (parityOf (β.drop i))
  have hlen : (parityOf β).length - blockEnd β i = (parityOf (β.drop i)).length := by
    unfold blockEnd; rw [hlu_parityOf_split β i, List.length_append]; omega
  rw [hlen]
  refine ⟨r', hr', ?_⟩
  unfold blockEnd
  rw [hlu_parityOf_split β i]
  exact hT t

/-- Sandwich for the boundary points: `3^{a_i} 2^{m - L_i} t ≤ P_i < 3^{a_i} 2^{m - L_i} (t + 1)`. -/
theorem hlu_P_bounds (β : List Bool) (t i : ℕ) :
    3 ^ terrasA (parityOf (β.take i)) * 2 ^ ((parityOf β).length - blockEnd β i) * t
        ≤ T^[blockEnd β i] (terrasR (parityOf β) + 2 ^ (parityOf β).length * t) ∧
      T^[blockEnd β i] (terrasR (parityOf β) + 2 ^ (parityOf β).length * t)
        < 3 ^ terrasA (parityOf (β.take i)) * 2 ^ ((parityOf β).length - blockEnd β i) * (t + 1) := by
  obtain ⟨r', hr', hP⟩ := hlu_P_eq β t i
  rw [hP]
  have hc := terrasC_lt (parityOf (β.take i))
  generalize terrasC (parityOf (β.take i)) = c at hc ⊢
  generalize 3 ^ terrasA (parityOf (β.take i)) = a at hc ⊢
  generalize 2 ^ ((parityOf β).length - blockEnd β i) = q at hr' ⊢
  have h1 : a * (r' + 1) ≤ a * q := Nat.mul_le_mul_left _ hr'
  constructor
  · nlinarith
  · nlinarith

/-! ## Number of odd steps -/

/-- `a_σ` is the sum of the numbers of odd steps of the blocks (5 for `X'`, 7 for `Y'`). -/
theorem hlu_terrasA_parityOf (β : List Bool) :
    terrasA (parityOf β) = (β.map (fun x => if x then 5 else 7)).sum := by
  induction β with
  | nil => simp [parityOf, terrasA_eq]
  | cons x β ih =>
    rw [hlu_parityOf_cons, terrasA_append, ih, List.map_cons, List.sum_cons]
    cases x <;> simp [terrasA_eq, blkX, blkY]

/-- `a_i` at the boundary points (the same shape as `oddPrefix β i` in `HLUWalk.lean`). -/
theorem hlu_terrasA_take (β : List Bool) (i : ℕ) :
    terrasA (parityOf (β.take i)) = ((β.take i).map (fun x => if x then 5 else 7)).sum :=
  hlu_terrasA_parityOf _

end Collatz.Arctic
