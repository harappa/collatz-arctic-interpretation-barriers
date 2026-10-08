/-
# Natural-number interpretations of 𝒯 (Section 12.5): the numbers of uses of the rules

The numbers of uses of the rules (as counted in an earlier, longer argument that is not used here; the event of the numbers of uses in Theorems 10.10
and 10.11, which does not depend on the interpretation), proved on the point family of Section 6.1 (the model of `T`, `Family.lean`):
Proposition 12.17 and Corollary 12.18.

* **The two dynamic rules** (`f. → .`, `t. → 2.`): `FamilyUses.fam_usesOrbit_odd_ge`, `fam_usesOrbit_even_ge` (deterministically at least `3|β|` times).
* **The three left-end rules**: `HLUMain.hLeftUse` (on an event on `σ`, at least `c k` times for every `t ≥ 2^m`). For the points of the family,
  `t = famT ≥ 2^{n-1} ≥ 2^m` (`m < n`, `famT_pow_le`). All three at once: `leftUse_all`.
* **The six carry rules** (added for the natural-number part): in the first step (odd) the ternary digit 2 crosses the binary digits of `y = (x₀ - 1)/2`
  from the least significant end (`ARuleCarry.uses_aRule_odd`). The number of uses of the rule `aRule b d` is the number of positions at which the digit `b` is read
  with carry `d` (`carry`) (`count_aRulesOf_ge`). Reading `0, 0` from the least significant end always brings the carry back to 0 (synchronizing word, `carry_sync`), so it is
  bounded below by the number of occurrences (`occS`) of the pattern of length 5 `pat5 b d = 0 0 · w5 d · b` (from the least significant end; `w5 0 = 00`, `w5 1 = 01`, `w5 2 = 11`).
  The occurrences of the pattern are counted only inside the word of the free bits `u` (read from the least significant end, `(bitsMSB F u).reverse`) (`uses_aRule_famX0_ge`).
  If the window frequencies of length 5 are within `1/128` of uniform, each of the six patterns occurs at least `F/128` times (`aRule_of_winClose`). The window
  frequencies come from `WindowLLN2.winClose_lln_interval` (`CoreU.win_bad_count`), and the proportion of failing `u` is at most `ε`
  (`aRule_bad_count`; the reversal of words is the bijection `card_filter_reverse` of `wordsOfLen F`). The main theorem is **`aRule_uses_free`**.
* **Summary for the 11 rules**: `uses_rulesST_famX0` (the deterministic assembly), **`uses_family`** (the probability `1 - ε` of the event on `σ`, and
  on it the number `≤ ε 2^F` of failing `u`), **`uses_family_inter`** (intersection with a set of `2^{F-L}` values `u` of the type of the event (c);
  the form used for Lemma 12.30).

Probabilities are written with `Prσ` (the choice of blocks) and with counting over `Finset.range (2^F)` (the free bits), in the same style as the arctic part.
Nothing here depends on the simplifications made elsewhere (the count for the carry rules uses only the carry chain of `ARuleCarry.lean` and the family of Section 6.1).
Only the three standard axioms (the axiom checks are in `verify/Probe.lean`). No `sorry`, `axiom` or `native_decide` is used.
-/
import CollatzProof.Arctic.Nat.W3Bridge
import CollatzProof.Arctic.ARuleCarry
import CollatzProof.Arctic.FamilyUses
import CollatzProof.Arctic.CoreSigma

namespace Collatz.Arctic.NatQ5.W3a

open Collatz.Arctic

/-! ## §1 The carry chain and the numbers of uses of the carry rules -/

/-- A digit letter as a natural number (`t ↦ 1`, all others 0). -/
def l2n (s : Letter) : ℕ := if s = Letter.t then 1 else 0

theorem l2n_lt_two (s : Letter) : l2n s < 2 := by unfold l2n; split_ifs <;> omega

/-- `tailBitsLSB n` (from the least significant end, without the leading 1) is `binTail n` read by `l2n` and reversed. -/
theorem tailBitsLSB_eq_map (n : ℕ) : tailBitsLSB n = ((binTail n).map l2n).reverse := by
  unfold tailBitsLSB binTail
  congr 1
  rw [List.map_map]
  conv_lhs => rw [← List.map_id ((Nat.digits 2 n).reverse.drop 1)]
  refine List.map_congr_left (fun b hb => ?_)
  have hb2 : b < 2 := Nat.digits_lt_base (by norm_num)
    (List.mem_reverse.mp (List.mem_of_mem_drop hb))
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> rfl

/-- The carry: the carry after the ternary digit `d` has crossed a list of digits (from the least significant end). -/
def carry (d : ℕ) (l : List ℕ) : ℕ := l.foldl (fun d b => (3 * b + d) / 2) d

@[simp] theorem carry_nil (d : ℕ) : carry d [] = d := rfl

theorem carry_cons (d b : ℕ) (l : List ℕ) : carry d (b :: l) = carry ((3 * b + d) / 2) l := rfl

theorem carry_append (d : ℕ) (l₁ l₂ : List ℕ) : carry d (l₁ ++ l₂) = carry (carry d l₁) l₂ := by
  unfold carry; rw [List.foldl_append]

/-- The list of carry rules in a sweep (without the left-end rule). -/
def aRulesOf : List ℕ → ℕ → List Rule
  | [], _ => []
  | b :: bs, d => aRule b d :: aRulesOf bs ((3 * b + d) / 2)

theorem sweepRules_eq_aRulesOf : ∀ (l : List ℕ) (d : ℕ),
    sweepRules l d = aRulesOf l d ++ [leftRule (carry d l)]
  | [], d => rfl
  | b :: bs, d => by
    simp only [sweepRules, aRulesOf, List.cons_append, carry_cons]
    rw [sweepRules_eq_aRulesOf bs]

theorem aRulesOf_append : ∀ (l₁ l₂ : List ℕ) (d : ℕ),
    aRulesOf (l₁ ++ l₂) d = aRulesOf l₁ d ++ aRulesOf l₂ (carry d l₁)
  | [], l₂, d => rfl
  | b :: bs, l₂, d => by
    simp only [List.cons_append, aRulesOf, carry_cons]
    rw [aRulesOf_append bs]

theorem aRulesOf_snoc (l : List ℕ) (x d : ℕ) :
    aRulesOf (l ++ [x]) d = aRulesOf l d ++ [aRule x (carry d l)] := by
  rw [aRulesOf_append]; rfl

/-- The carry stays at most 2 (if the digits are 0 or 1). -/
theorem carry_le_two : ∀ (l : List ℕ), (∀ x ∈ l, x < 2) → ∀ d ≤ 2, carry d l ≤ 2
  | [], _, d, hd => hd
  | b :: bs, hl, d, hd => by
    rw [carry_cons]
    have hb := hl b List.mem_cons_self
    exact carry_le_two bs (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ (by omega)

/-- The end of the synchronizing word: `w5 0 = 00`, `w5 1 = 01`, `w5 2 = 11` (from the least significant end; reading it from carry 0 gives carry `d`). -/
def w5 (d : ℕ) : List ℕ := if d = 0 then [0, 0] else if d = 1 then [0, 1] else [1, 1]

/-- **The pattern of the carry rule `aRule b d`** (length 5, from the least significant end): the synchronizing word `00`, `w5 d`, the digit `b`. -/
def pat5 (b d : ℕ) : List ℕ := [0, 0] ++ w5 d ++ [b]

theorem pat5_length (b d : ℕ) : (pat5 b d).length = 5 := by
  unfold pat5 w5; split_ifs <;> rfl

/-- **Synchronization**: reading `00 · w5 d` from a carry `e ≤ 3` gives carry `d` (`d ≤ 2`). -/
theorem carry_sync {e : ℕ} (he : e ≤ 3) {d : ℕ} (hd : d ≤ 2) : carry e ([0, 0] ++ w5 d) = d := by
  have h0 : carry e [0, 0] = 0 := by
    simp only [carry_cons, carry_nil]; omega
  rw [carry_append, h0]
  unfold w5
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> rfl

/-- **The number of occurrences of a pattern** (counted at the right ends of prefixes): the number of `j ≤ |l|` such that `P` is a suffix of `l.take j`. -/
def occS (l P : List ℕ) : ℕ := ((Finset.range (l.length + 1)).filter (fun j => P <:+ l.take j)).card

theorem occS_snoc (l : List ℕ) (x : ℕ) (P : List ℕ) :
    occS (l ++ [x]) P = occS l P + if P <:+ l ++ [x] then 1 else 0 := by
  unfold occS
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have hfil : (Finset.range (l.length + 1)).filter (fun j => P <:+ (l ++ [x]).take j) =
      (Finset.range (l.length + 1)).filter (fun j => P <:+ l.take j) := by
    apply Finset.filter_congr
    intro j hj
    rw [List.take_append_of_le_length (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj)]
  have htake : (l ++ [x]).take (l.length + 1) = l ++ [x] := List.take_of_length_le (by simp)
  rw [htake, hfil]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- Extracting a suffix: if `(Q ++ [b]) <:+ (l ++ [x])`, then `b = x` and `Q <:+ l`. -/
theorem suffix_snoc {Q l : List ℕ} {b x : ℕ} (h : (Q ++ [b]) <:+ (l ++ [x])) : b = x ∧ Q <:+ l := by
  rw [← List.reverse_prefix, List.reverse_append, List.reverse_append] at h
  simp only [List.reverse_singleton, List.singleton_append] at h
  obtain ⟨h1, h2⟩ := List.cons_prefix_cons.mp h
  exact ⟨h1, List.reverse_prefix.mp h2⟩

/-- **A lower bound for the number of uses of a carry rule**: when the digits `l` (0 or 1) are crossed from a carry `d₀ ≤ 2`, `aRule b d` is used at least
as often as the pattern `pat5 b d` occurs. -/
theorem count_aRulesOf_ge (b d : ℕ) (hd : d ≤ 2) : ∀ (l : List ℕ), (∀ x ∈ l, x < 2) → ∀ d₀ ≤ 2,
    occS l (pat5 b d) ≤ (aRulesOf l d₀).count (aRule b d) := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro _ d₀ _
    have : ¬ pat5 b d <:+ [] := by
      intro h
      have := h.length_le
      rw [pat5_length] at this
      simp at this
    simp [occS, this]
  | append_singleton l x ih =>
    intro hl d₀ hd₀
    have hl' : ∀ y ∈ l, y < 2 := fun y hy => hl y (List.mem_append_left _ hy)
    rw [occS_snoc, aRulesOf_snoc, List.count_append]
    have hih := ih hl' d₀ hd₀
    split_ifs with h
    · have h' : ([0, 0] ++ w5 d ++ [b]) <:+ (l ++ [x]) := h
      obtain ⟨hbx, hQ⟩ := suffix_snoc h'
      obtain ⟨A, rfl⟩ := hQ
      have hA : ∀ y ∈ A, y < 2 := fun y hy => hl' y (List.mem_append_left _ hy)
      have hcarry : carry d₀ (A ++ ([0, 0] ++ w5 d)) = d := by
        rw [carry_append]
        exact carry_sync (by have := carry_le_two A hA d₀ hd₀; omega) hd
      rw [hcarry, ← hbx, List.count_singleton_self]
      omega
    · omega

/-- The same lower bound for the whole sweep (including the left-end rule). -/
theorem count_sweep_ge (b d : ℕ) (hd : d ≤ 2) (l : List ℕ) (hl : ∀ x ∈ l, x < 2) (d₀ : ℕ) (hd₀ : d₀ ≤ 2) :
    occS l (pat5 b d) ≤ (sweepRules l d₀).count (aRule b d) := by
  rw [sweepRules_eq_aRulesOf, List.count_append]
  have := count_aRulesOf_ge b d hd l hl d₀ hd₀
  omega

/-- Prepending a word does not decrease the number of occurrences. -/
theorem occS_append_left (A U P : List ℕ) : occS U P ≤ occS (A ++ U) P := by
  unfold occS
  refine Finset.card_le_card_of_injOn (fun j => A.length + j) ?_ ?_
  · intro j hj
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨by rw [List.length_append]; omega, ?_⟩
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    exact hj.2.trans (List.suffix_append A _)
  · intro j _ j' _ h
    simpa using h

/-- Appending a word does not decrease the number of occurrences. -/
theorem occS_append_right (U B P : List ℕ) : occS U P ≤ occS (U ++ B) P := by
  unfold occS
  refine Finset.card_le_card_of_injOn (fun j => j) ?_ (fun _ _ _ _ h => h)
  intro j hj
  dsimp only
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj ⊢
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  rw [List.take_append_of_le_length (by omega)]
  exact hj.2

/-- **The bridge to window counts**: the number of windows of length `|v|` of a binary word `w` of length `F` that equal `v` is at most the number of occurrences
of the pattern `v.map l2n` in the list `w` read by `l2n`. -/
theorem winCount_le_occS (w v : Word) :
    winCount w 0 w.length v.length v ≤ occS (w.map l2n) (v.map l2n) := by
  rw [winCount_eq_card]
  unfold occS
  refine Finset.card_le_card_of_injOn (fun i => i + v.length) ?_ ?_
  · intro i hi
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, zero_add] at hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨by rw [List.length_map]; omega, ?_⟩
    rw [List.take_add]
    have : ((w.map l2n).drop i).take v.length = v.map l2n := by
      rw [← List.map_drop, ← List.map_take]
      exact congrArg (List.map l2n) hi.2
    rw [this]
    exact List.suffix_append _ _
  · intro i _ i' _ h
    simpa using h

/-! ## §2 Carry rules at the points of the family -/

/-- A point of the family is odd if `β ≠ []` (every block begins with an odd step). -/
theorem famX0_odd {β₀ β : List Bool} (hne : β ≠ []) (n K τ u : ℕ) : famX0 β₀ β n K τ u % 2 = 1 := by
  obtain ⟨x, β', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hσ : parityOf (x :: β') = (if x then blkX else blkY) ++ parityOf β' := by simp [parityOf]
  have hlen : 0 < (parityOf (x :: β')).length := by
    rw [hσ, List.length_append]; cases x <;> simp [blkX, blkY]
  have h := terras_parity (parityOf (x :: β')) (famT β₀ (x :: β') n K τ u) 0 hlen
  have hg : (parityOf (x :: β')).getD 0 false = true := by
    rw [hσ]; cases x <;> rfl
  rw [hg] at h
  simpa [famX0] using h

/-- A point of the family is at least 3 (`β ≠ []`, `τ ≥ 1`). -/
theorem famX0_ge_three {β₀ β : List Bool} (hne : β ≠ []) {n K τ : ℕ} (u : ℕ) (hτ : 1 ≤ τ) :
    3 ≤ famX0 β₀ β n K τ u := by
  have hodd := famX0_odd (β₀ := β₀) hne n K τ u
  have hm : 1 ≤ (parityOf β).length := by
    have := (parityOf_length_bounds β).1
    have : 1 ≤ β.length := List.length_pos_iff.mpr hne
    omega
  have ht := fam_T_pos (β₀ := β₀) (β := β) (n := n) (K := K) u hτ
  have h2 : 2 ≤ 2 ^ (parityOf β).length * famT β₀ β n K τ u :=
    le_trans (by calc 2 = 2 ^ 1 * 1 := by norm_num
                    _ ≤ 2 ^ (parityOf β).length * 1 := Nat.mul_le_mul_right _
                        (Nat.pow_le_pow_right (by norm_num) hm))
      (Nat.mul_le_mul_left _ ht)
  have : 2 ≤ famX0 β₀ β n K τ u := by unfold famX0; omega
  omega

/-- **The numbers of uses of the carry rules at a point of the family**: the number of uses of `aRule b d` is at least the number of occurrences of the pattern `pat5 b d` in the word of the free bits `u` (from the least significant end). -/
theorem uses_aRule_famX0_ge {β₀ β : List Bool} {n K τ u : ℕ} (hne : β ≠ [])
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ) (hu : u < 2 ^ (n - K - (parityOf β₀).length))
    (b d : ℕ) (hd : d ≤ 2) :
    occS (((bitsMSB (n - K - (parityOf β₀).length) u).reverse).map l2n) (pat5 b d) ≤
      uses (aRule b d) (famX0 β₀ β n K τ u) := by
  set x₀ := famX0 β₀ β n K τ u with hx₀
  have hodd : x₀ % 2 = 1 := famX0_odd hne n K τ u
  have h3 : 3 ≤ x₀ := famX0_ge_three hne u hτ
  rw [ARule.uses_aRule_odd b d x₀ hodd]
  set y := (x₀ - 1) / 2 with hy
  have hxy : x₀ = 2 * y + 1 := by omega
  have hty : tailBitsLSB x₀ = 1 :: tailBitsLSB y := by
    rw [hxy]; exact tailBitsLSB_two_mul_add y 1 (by omega) (by norm_num)
  -- splitting `tailBitsLSB x₀`
  have hsplit := binTail_famX0_split (β := β) hKn hτ hu
  rw [← hx₀] at hsplit
  set F := n - K - (parityOf β₀).length with hF
  set R := ((bitsMSB (parityOf β).length (terrasR (parityOf β))).map l2n).reverse with hR
  set Rho := ((bitsMSB (parityOf β₀).length (famRho β₀ β)).map l2n).reverse with hRho
  set U := ((bitsMSB F u).map l2n).reverse with hU
  set Tau := ((binTail τ).map l2n).reverse with hTau
  have htail : tailBitsLSB x₀ = R ++ Rho ++ U ++ Tau := by
    rw [tailBitsLSB_eq_map, hsplit]
    simp only [List.map_append, List.reverse_append, List.append_assoc]
    rfl
  have hRne : R ≠ [] := by
    rw [hR]
    have hm : 1 ≤ (parityOf β).length := by
      have := (parityOf_length_bounds β).1
      have : 1 ≤ β.length := List.length_pos_iff.mpr hne
      omega
    intro h
    have := congrArg List.length h
    simp only [List.length_reverse, List.length_map, bitsMSB_length, List.length_nil] at this
    omega
  have hty' : tailBitsLSB y = R.tail ++ Rho ++ U ++ Tau := by
    have := hty.symm.trans htail
    have h2 := congrArg List.tail this
    simp only [List.tail_cons] at h2
    rw [h2, List.append_assoc, List.append_assoc, List.tail_append_of_ne_nil hRne,
      List.append_assoc, List.append_assoc]
  have hdig : ∀ z ∈ tailBitsLSB y, z < 2 := by
    intro z hz
    rw [tailBitsLSB_eq_map, List.mem_reverse] at hz
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hz
    exact l2n_lt_two s
  have hcount := count_sweep_ge b d hd (tailBitsLSB y) hdig 2 le_rfl
  refine le_trans ?_ hcount
  rw [hty']
  have e : ((bitsMSB F u).reverse).map l2n = U := by rw [hU, List.map_reverse]
  rw [e]
  calc occS U (pat5 b d) ≤ occS (U ++ Tau) (pat5 b d) := occS_append_right _ _ _
    _ ≤ occS ((R.tail ++ Rho) ++ (U ++ Tau)) (pat5 b d) := occS_append_left _ _ _
    _ = occS (R.tail ++ Rho ++ U ++ Tau) (pat5 b d) := by simp only [List.append_assoc]

/-- The number of uses along a segment of an orbit is at least the number of uses at its first point. -/
theorem uses_le_usesOrbit (ρ : Rule) (x m : ℕ) (hm : 1 ≤ m) : uses ρ x ≤ usesOrbit ρ x m := by
  unfold usesOrbit
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons]
  simp

/-! ## §3 Counting the free bits -/

/-- Reversal of words is a bijection of the binary words of length `F`. -/
theorem card_filter_reverse (F : ℕ) (P : Word → Prop) [DecidablePred P] :
    ((wordsOfLen F).filter (fun w => P w.reverse)).card = ((wordsOfLen F).filter P).card := by
  apply Finset.card_nbij' List.reverse List.reverse
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    refine ⟨?_, hw.2⟩
    rw [WinLLN.mem_iff] at hw ⊢
    exact ⟨by rw [List.length_reverse]; exact hw.1.1, fun s hs => hw.1.2 s (List.mem_reverse.mp hs)⟩
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    refine ⟨?_, by rw [List.reverse_reverse]; exact hw.2⟩
    rw [WinLLN.mem_iff] at hw ⊢
    exact ⟨by rw [List.length_reverse]; exact hw.1.1, fun s hs => hw.1.2 s (List.mem_reverse.mp hs)⟩
  · intro w _; exact List.reverse_reverse w
  · intro w _; exact List.reverse_reverse w

open Classical in
/-- **The number of failing free bits**: for `F` large, at most `ε 2^F` values `u` have a word, read from the least significant end, whose window frequencies of length 5 are not within `1/128` of uniform.
-/
theorem aRule_bad_count (ε : ℚ) (hε : 0 < ε) : ∃ F₀ : ℕ, ∀ F, F₀ ≤ F →
    (((Finset.range (2 ^ F)).filter (fun u => ¬ WinClose (bitsMSB F u).reverse 0 F 5 (1 / 128))).card : ℚ) ≤
      ε * 2 ^ F := by
  obtain ⟨M₀, hM₀⟩ := win_bad_count 5 (1 / 128) ε (by norm_num) hε
  refine ⟨M₀, fun F hF => ?_⟩
  have e1 := card_filter_bitsMSB F (fun w => ¬ WinClose w.reverse 0 F 5 (1 / 128))
  have e2 := card_filter_reverse F (fun w => ¬ WinClose w 0 F 5 (1 / 128))
  have e3 := card_filter_bitsMSB F (fun w => ¬ WinClose w 0 F 5 (1 / 128))
  have h := hM₀ F 0 F (Nat.zero_le _) le_rfl (by omega)
  rw [e1, e2, ← e3]
  exact h

/-- **Occurrences of the patterns**: if the window frequencies of length 5 of the word of `u` read from the least significant end are within `1/128` of uniform (`F ≥ 8`), each of the six patterns
`pat5 b d` occurs at least `F/128` times. -/
theorem aRule_of_winClose {F u : ℕ} (hF : 8 ≤ F) (h : WinClose (bitsMSB F u).reverse 0 F 5 (1 / 128))
    (b : ℕ) (hb : b < 2) (d : ℕ) :
    (F : ℚ) / 128 ≤ occS (((bitsMSB F u).reverse).map l2n) (pat5 b d) := by
  set w := (bitsMSB F u).reverse with hw
  have hwlen : w.length = F := by rw [hw, List.length_reverse, bitsMSB_length]
  set v := (pat5 b d).map bitL with hv
  have hvlen : v.length = 5 := by rw [hv, List.length_map, pat5_length]
  have hvmem : v ∈ wordsOfLen 5 := by
    refine mem_wordsOfLen_of hvlen (fun s hs => ?_)
    rw [hv] at hs
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hs
    unfold bitL; split_ifs <;> simp
  have hvl : v.map l2n = pat5 b d := by
    rw [hv, List.map_map]
    conv_rhs => rw [← List.map_id (pat5 b d)]
    refine List.map_congr_left (fun x hx => ?_)
    have hx2 : x < 2 := by
      unfold pat5 w5 at hx
      split_ifs at hx <;> simp at hx <;> omega
    rcases (by omega : x = 0 ∨ x = 1) with rfl | rfl <;> rfl
  obtain ⟨-, -, hsum⟩ := h
  have hsingle := Finset.single_le_sum (f := fun v' => |((winCount w 0 F 5 v' : ℚ) /
      ((F + 1 - 5 - 0 : ℕ) : ℚ)) - 1 / 2 ^ 5|) (fun _ _ => abs_nonneg _) hvmem
  have habs := le_trans hsingle hsum
  have hN : ((F + 1 - 5 - 0 : ℕ) : ℚ) = (F : ℚ) - 4 := by
    rw [show F + 1 - 5 - 0 = F - 4 by omega, Nat.cast_sub (by omega)]; norm_num
  rw [hN] at habs
  have hNpos : (0 : ℚ) < (F : ℚ) - 4 := by
    have : (8 : ℚ) ≤ F := by exact_mod_cast hF
    linarith
  have hlow : (1 : ℚ) / 64 ≤ (winCount w 0 F 5 v : ℚ) / ((F : ℚ) - 4) := by
    have := (abs_le.mp habs).1
    norm_num at this ⊢
    linarith
  rw [le_div_iff₀ hNpos] at hlow
  have hocc := winCount_le_occS w v
  rw [hwlen, hvlen, hvl] at hocc
  have hoccq : (winCount w 0 F 5 v : ℚ) ≤ occS (w.map l2n) (pat5 b d) := by exact_mod_cast hocc
  have hF8 : (8 : ℚ) ≤ F := by exact_mod_cast hF
  calc (F : ℚ) / 128 ≤ 1 / 64 * ((F : ℚ) - 4) := by linarith
    _ ≤ winCount w 0 F 5 v := hlow
    _ ≤ occS (w.map l2n) (pat5 b d) := hoccq

/-- The numbers of uses of the six carry rules along the segment of `m` steps of the orbit from the point `x` are all at least `F/128`. -/
def AGood (F x m : ℕ) : Prop := ∀ b < 2, ∀ d ≤ 2, (F : ℚ) / 128 ≤ (usesOrbit (aRule b d) x m : ℚ)

/-- The numbers of uses of the 11 rules along the segment of `m` steps of the orbit from the point `x` are all at least `c k`. -/
def UsesGood (c : ℚ) (k x m : ℕ) : Prop := ∀ ρ ∈ rulesST, c * k ≤ (usesOrbit ρ x m : ℚ)

open Classical in
/-- **The numbers of uses of the carry rules** (Proposition 12.17 (ii), `aRule_uses_free`): with `c = 1/128`, for every `ε > 0` there is `F₀` such that,
for the points of the family (`β ≠ []`, `K + s' ≤ n`, `τ ≥ 1`, `F := n - K - s' ≥ F₀`), at most `ε 2^F` free bits `u < 2^F` give some of the six carry rules
fewer than `F/128` uses (uniformly in `β₀`, `β`, `n`, `K`, `τ`). -/
theorem aRule_uses_free (ε : ℚ) (hε : 0 < ε) : ∃ F₀ : ℕ, ∀ (β₀ β : List Bool) (n K τ : ℕ), β ≠ [] →
    K + (parityOf β₀).length ≤ n → 1 ≤ τ → F₀ ≤ n - K - (parityOf β₀).length →
    (((Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
        ¬ AGood (n - K - (parityOf β₀).length) (famX0 β₀ β n K τ u) (parityOf β).length)).card : ℚ) ≤
      ε * 2 ^ (n - K - (parityOf β₀).length) := by
  obtain ⟨F₀, hF₀⟩ := aRule_bad_count ε hε
  refine ⟨max F₀ 8, fun β₀ β n K τ hne hKn hτ hF => ?_⟩
  set F := n - K - (parityOf β₀).length with hFdef
  refine le_trans ?_ (hF₀ F (le_of_max_le_left hF))
  have hm : 1 ≤ (parityOf β).length := by
    have := (parityOf_length_bounds β).1
    have : 1 ≤ β.length := List.length_pos_iff.mpr hne
    omega
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro u hu
  rw [Finset.mem_filter] at hu ⊢
  refine ⟨hu.1, fun hw => hu.2 (fun b hb d hd => ?_)⟩
  have h1 := aRule_of_winClose (le_of_max_le_right hF) hw b hb d
  have h2 := uses_aRule_famX0_ge (β := β) hne hKn hτ (Finset.mem_range.mp hu.1) b d hd
  have h3 := uses_le_usesOrbit (aRule b d) (famX0 β₀ β n K τ u) _ hm
  have h23 : (occS (((bitsMSB F u).reverse).map l2n) (pat5 b d) : ℚ) ≤
      (usesOrbit (aRule b d) (famX0 β₀ β n K τ u) (parityOf β).length : ℚ) := by
    exact_mod_cast h2.trans h3
  exact h1.trans h23

/-! ## §4 Summary for the 11 rules -/

/-- The `t` of the family is at least `2^m` (`m < n`): the event of the left-end rules (for every `t ≥ 2^m`) applies to the points of the family. -/
theorem famT_pow_le {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hmn : (parityOf β).length < n) :
    2 ^ (parityOf β).length ≤ famT β₀ β n K τ u :=
  le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (fam_T_ge u hK hKn hτ1)

/-- The left-end event on the side of `σ`: each of the three left-end rules is used at least `c k` times, for every `t ≥ 2^m`. -/
def EvLeft (c : ℚ) (k : ℕ) (β : List Bool) : Prop :=
  ∀ d ≤ 2, ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
    c * k ≤ (usesOrbit (leftRule d) (terrasR (parityOf β) + 2 ^ (parityOf β).length * t)
      (parityOf β).length : ℚ)

theorem evLeft_mono {c c' : ℚ} (hcc : c' ≤ c) {k : ℕ} {β : List Bool} (h : EvLeft c k β) : EvLeft c' k β :=
  fun d hd t ht => le_trans (mul_le_mul_of_nonneg_right hcc (Nat.cast_nonneg _)) (h d hd t ht)

/-- **The three left-end rules at once** (`hLeftUse` and a union bound). -/
theorem leftUse_all (β₀ : List Bool) : ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    1 - ε ≤ Prσ β₀ k (EvLeft c k) := by
  obtain ⟨c, hc, h⟩ := hLeftUse β₀
  refine ⟨c, hc, fun ε hε => ?_⟩
  obtain ⟨k₀, hk₀⟩ := h (ε / 3) (by positivity)
  refine ⟨k₀, fun k hk => ?_⟩
  have h3 := sig_forall_lt β₀ k (fun d β => ∀ t : ℕ, 2 ^ (parityOf β).length ≤ t →
      c * k ≤ (usesOrbit (leftRule d) (terrasR (parityOf β) + 2 ^ (parityOf β).length * t)
        (parityOf β).length : ℚ)) (ε / 3) 3 (fun d hd => hk₀ k hk d (by omega))
  have e : 1 - (3 : ℕ) * (ε / 3) = 1 - ε := by push_cast; ring
  rw [e] at h3
  refine le_trans h3 (Prσ_mono β₀ k (fun β _ hβ d hd t ht => hβ d (by omega) t ht))

/-- The classification of the 11 rules of 𝒯 (the same as `CoreFinal.rulesST_cases`). -/
theorem rulesST_cases' (ρ : Rule) (h : ρ ∈ rulesST) :
    (∃ b d, b < 2 ∧ d ≤ 2 ∧ ρ = aRule b d) ∨ ρ = ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩ ∨
      ρ = ⟨[Letter.t, Letter.rgt], [Letter.d2, Letter.rgt]⟩ ∨ ∃ d ≤ 2, ρ = leftRule d := by
  simp only [rulesST, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl ⟨0, 0, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨0, 1, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨0, 2, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 0, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 1, by norm_num, by norm_num, by decide⟩
  · exact Or.inl ⟨1, 2, by norm_num, by norm_num, by decide⟩
  · exact Or.inr (Or.inr (Or.inr ⟨0, by norm_num, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨1, by norm_num, by decide⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨2, by norm_num, by decide⟩))

/-- **Deterministic assembly for the 11 rules**: under the left-end event on `σ` (constant `c`), the lower bound `F/128` for the carry rules, `c ≤ 1/128`, `k ≤ |β|` and
`k ≤ F`, every rule is used at least `c k` times. -/
theorem uses_rulesST_famX0 {c : ℚ} (hc128 : c ≤ 1 / 128) {k : ℕ} {β₀ β : List Bool}
    {n K τ u : ℕ} (hk : k ≤ β.length) (hK : 1 ≤ K) (hKn : K + (parityOf β₀).length ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hmn : (parityOf β).length < n) (hkF : k ≤ n - K - (parityOf β₀).length)
    (hL : EvLeft c k β)
    (hA : AGood (n - K - (parityOf β₀).length) (famX0 β₀ β n K τ u) (parityOf β).length) :
    UsesGood c k (famX0 β₀ β n K τ u) (parityOf β).length := by
  intro ρ hρ
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  have hc3 : c * k ≤ 3 * β.length := by
    have : (k : ℚ) ≤ β.length := by exact_mod_cast hk
    nlinarith
  rcases rulesST_cases' ρ hρ with ⟨b, d, hb, hd, rfl⟩ | rfl | rfl | ⟨d, hd, rfl⟩
  · have hkF' : (k : ℚ) ≤ ((n - K - (parityOf β₀).length : ℕ) : ℚ) := by exact_mod_cast hkF
    calc c * k ≤ 1 / 128 * k := mul_le_mul_of_nonneg_right hc128 hk0
      _ ≤ ((n - K - (parityOf β₀).length : ℕ) : ℚ) / 128 := by linarith
      _ ≤ _ := hA b hb d hd
  · have := fam_usesOrbit_even_ge β₀ β n K τ u
    have : (3 * β.length : ℚ) ≤ (usesOrbit ⟨[Letter.f, Letter.rgt], [Letter.rgt]⟩
        (famX0 β₀ β n K τ u) (parityOf β).length : ℚ) := by exact_mod_cast this
    linarith
  · have := fam_usesOrbit_odd_ge β₀ β n K τ u
    have : (3 * β.length : ℚ) ≤ (usesOrbit ⟨[Letter.t, Letter.rgt], [Letter.d2, Letter.rgt]⟩
        (famX0 β₀ β n K τ u) (parityOf β).length : ℚ) := by exact_mod_cast this
    linarith
  · exact hL d hd _ (famT_pow_le u hK (by omega) hτ1 hmn)

open Classical in
/-- **The event of the numbers of uses of the 11 rules** (the main theorem of this file): once the first blocks `β₀` are fixed, there is a constant `c > 0` such that for every `ε > 0`
there is `k₀` with the following for `k ≥ k₀`: (1) the left-end event `EvLeft c k` on `σ` has probability at least `1 - ε`; (2) on it, for the points of the family
(`k ≤ |β|`, `m < n`, `k ≤ F`), at most `ε 2^F` free bits `u < 2^F` give some of the 11 rules fewer than `c k` uses
(uniformly in `n`, `K`, `τ`). -/
theorem uses_family (β₀ : List Bool) : ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (1 - ε ≤ Prσ β₀ k (EvLeft c k)) ∧
    ∀ β : List Bool, EvLeft c k β → k ≤ β.length → ∀ n K τ : ℕ, 1 ≤ K → K + (parityOf β₀).length ≤ n →
      2 ^ (K - 1) ≤ τ → (parityOf β).length < n → k ≤ n - K - (parityOf β₀).length →
      (((Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun u =>
          ¬ UsesGood c k (famX0 β₀ β n K τ u) (parityOf β).length)).card : ℚ) ≤
        ε * 2 ^ (n - K - (parityOf β₀).length) := by
  obtain ⟨cL, hcL, hL⟩ := leftUse_all β₀
  set c := min cL (1 / 128) with hcdef
  have hc : 0 < c := lt_min hcL (by norm_num)
  refine ⟨c, hc, fun ε hε => ?_⟩
  obtain ⟨k₁, hk₁⟩ := hL ε hε
  obtain ⟨F₀, hF₀⟩ := aRule_uses_free ε hε
  refine ⟨max (max k₁ F₀) 1, fun k hk => ⟨?_, ?_⟩⟩
  · exact le_trans (hk₁ k (le_trans (le_max_left _ _) (le_of_max_le_left hk)))
      (Prσ_mono β₀ k (fun β _ hβ => evLeft_mono (min_le_left _ _) hβ))
  · intro β hβL hkβ n K τ hK hKn hτ1 hmn hkF
    have hk1 : 1 ≤ k := le_of_max_le_right hk
    have hne : β ≠ [] := List.length_pos_iff.mp (by omega)
    have hτ : 1 ≤ τ := by have := Nat.one_le_two_pow (n := K - 1); omega
    have hF : F₀ ≤ n - K - (parityOf β₀).length :=
      le_trans (le_trans (le_max_right _ _) (le_of_max_le_left hk)) hkF
    refine le_trans ?_ (hF₀ β₀ β n K τ hne hKn hτ hF)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨hu.1, fun hA => hu.2 ?_⟩
    exact uses_rulesST_famX0 (min_le_right _ _) hkβ hK hKn hτ1 hmn hkF hβL hA

/-- Intersection by counting: a set `s` of at least `2^{F-L}` values `u < 2^F` (satisfying `P`) meets the event `G` whose failure set `t` has size at most
`ε 2^F < 2^{F-L}` (the `Finset` may be the `filter` of any `DecidablePred`). -/
theorem exists_of_card_lt {F L : ℕ} (P G : ℕ → Prop) (s t : Finset ℕ) (ε : ℚ)
    (hs : ∀ u ∈ s, u < 2 ^ F ∧ P u) (ht : ∀ u < 2 ^ F, ¬ G u → u ∈ t)
    (hP : 2 ^ (F - L) ≤ s.card) (hG : (t.card : ℚ) ≤ ε * 2 ^ F) (hlt : ε * 2 ^ F < 2 ^ (F - L)) :
    ∃ u < 2 ^ F, P u ∧ G u := by
  by_contra hno
  push Not at hno
  have hsub : s ⊆ t := fun u hu => ht u (hs u hu).1 (hno u (hs u hu).1 (hs u hu).2)
  have h2 : ((2 ^ (F - L) : ℕ) : ℚ) ≤ (t.card : ℚ) := by exact_mod_cast hP.trans (Finset.card_le_card hsub)
  push_cast at h2
  linarith

/-- `2^F / 2^{L+1} < 2^{F-L}` (whatever the order of `F` and `L`). -/
theorem pow_div_lt (F L : ℕ) : (1 / 2 ^ (L + 1) : ℚ) * 2 ^ F < 2 ^ (F - L) := by
  have h : (2 : ℚ) ^ F < 2 ^ (L + 1) * 2 ^ (F - L) := by
    rw [← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [one_div, inv_mul_lt_iff₀ (by positivity)]
  exact h

open Classical in
/-- **The form that meets the event (c)** (the form used for Lemma 12.30; Corollary 12.18 (ii)): there is a constant `c > 0` such that for every `ε > 0` and `L` there is `k₀` with the following for `k ≥ k₀`:
(1) the left-end event on `σ` has probability at least `1 - ε`; (2) on it, for the points of the family, every set `s` of at least `2^{F-L}` values `u < 2^F` (of the type of the event (c),
`CoreStart.start_count`, `CoreU.cfg_count`, satisfying `P`; it is taken as a `Finset`, so the `DecidablePred` of a `filter` does not matter)
contains a `u` at which each of the 11 rules is used at least `c k` times. The order of the quantifiers is
`ε_A → k → σ → n → t` (`ε := ε_A < η₀/4` comes before `k`, and `L` comes from `η₀ = 2^{-L}` of the event (c)). -/
theorem uses_family_inter (β₀ : List Bool) : ∃ c : ℚ, 0 < c ∧ ∀ ε : ℚ, 0 < ε → ∀ L : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (1 - ε ≤ Prσ β₀ k (EvLeft c k)) ∧
    ∀ β : List Bool, EvLeft c k β → k ≤ β.length → ∀ n K τ : ℕ, 1 ≤ K → K + (parityOf β₀).length ≤ n →
      2 ^ (K - 1) ≤ τ → (parityOf β).length < n → k ≤ n - K - (parityOf β₀).length →
      ∀ (P : ℕ → Prop) (s : Finset ℕ), (∀ u ∈ s, u < 2 ^ (n - K - (parityOf β₀).length) ∧ P u) →
        2 ^ (n - K - (parityOf β₀).length - L) ≤ s.card →
        ∃ u < 2 ^ (n - K - (parityOf β₀).length), P u ∧
          UsesGood c k (famX0 β₀ β n K τ u) (parityOf β).length := by
  obtain ⟨c, hc, h⟩ := uses_family β₀
  refine ⟨c, hc, fun ε hε L => ?_⟩
  set ε' := min ε (1 / 2 ^ (L + 1)) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  obtain ⟨k₀, hk₀⟩ := h ε' hε'pos
  refine ⟨k₀, fun k hk => ⟨?_, ?_⟩⟩
  · exact le_trans (by linarith [min_le_left ε (1 / 2 ^ (L + 1))]) (hk₀ k hk).1
  · intro β hβL hkβ n K τ hK hKn hτ1 hmn hkF P s hs hP
    have hbad := (hk₀ k hk).2 β hβL hkβ n K τ hK hKn hτ1 hmn hkF
    refine exists_of_card_lt P _ s _ ε' hs
      (fun u hu hG => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu, hG⟩) hP hbad ?_
    calc ε' * 2 ^ (n - K - (parityOf β₀).length)
        ≤ 1 / 2 ^ (L + 1) * 2 ^ (n - K - (parityOf β₀).length) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ < 2 ^ (n - K - (parityOf β₀).length - L) := pow_div_lt _ _

end Collatz.Arctic.NatQ5.W3a
