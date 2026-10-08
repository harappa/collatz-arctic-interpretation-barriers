/-
# Natural-number interpretations of 𝒯 (Section 12.7): small tails and Proposition 12.24 (few long runs of misses, a weak form)

An internal review asked for "the expectation per group is
`δ(J) := Σ_{R>J} C(R+1)^{d}((R+L_R)/8g+3)(1-c_u)^{K_R} → 0`". This file proves it in an abstract form: the weights are polynomial
in the range `R`, the window `A R` is at most linear in `R`, and the number `K R` of consecutive groups that miss is at least linear
in `R` (`R ≤ κ K R + κ'`).

* `tail_small`: `∀ ε > 0, ∃ J` such that the finite sums over ranges `J < R` only satisfy `Σ_{R ∈ S} C (R+1)^d (A R + 1) q^{K R} ≤ ε`
  (`q < 1`). This follows from the convergence of `Σ (R+1)^{d+1} ρ^R` over the reals (`summable_pow_mul_geometric_of_norm_lt_one`) and from the
  tail sums (`tendsto_sum_nat_add`).
* `free_run_le`, `free_expect`: the same form on the side of the free bits (the uniform bits `u` of `t`). The words in which `v` does not occur
  in a window of length `Lw` starting somewhere in the positions `[a, a + A]` number at most `(A + 1) 2^L (1 - 2^{-|v|})^{⌊Lw/|v|⌋}`
  (`WindowLLN3.card_noOcc_le` and a union bound over the start; the chain of groups is not needed).
* **`gap_twin`**: Proposition 12.24, a weak form (failure probability "`≤ η`", as asked in an internal review). `∃ n₀ c > 0, ∀ n₁ ≥ n₀`, for every polynomial weight
  and linear window, `∀ ε η' > 0, ∃ J` such that for every set `I` of groups (group `i` fits in `k` blocks) and every set `S` of ranges (all
  greater than `J`), `Pr(Σ_{i ∈ I} Σ_{R ∈ S} C (R+1)^d 1[RunMiss i (A R) (K R)] > ε |I|) ≤ η'`.

Downstream (`W3h*.lean`, `W3hMain.lean`) applies the bound `ξ(p) 1[R(p) = R] ≤ C (R+1)^d` on the detour weights at the positions `p` of the Terras part
of the starting point and the fact "if a detour of range `R` starts at the position of group `i`, then `RunMiss i (A R) (K R)`" (of the type of Lemma 12.25 (ii): a window
without u♯ covers the cuts of `K R` consecutive groups entirely), and multiplies by the number of positions per group (at most `11 g`).

All auxiliary declarations are in the namespace `Collatz.Arctic.NatQ5.W3b`. No `sorry`, `axiom` or `native_decide` is used.
-/
import CollatzProof.Arctic.Nat.W3Gap
import CollatzProof.Arctic.WindowLLN3

namespace Collatz.Arctic.NatQ5.W3b

open Collatz.Arctic Finset Filter Topology
open Classical

/-! ## §1 Real tails -/

/-- If `ρ ∈ [0, 1)`, then `(R+1)^e ρ^R` is summable. -/
theorem summable_succ_pow_mul_geom (e : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun R : ℕ => ((R : ℝ) + 1) ^ e * ρ ^ R) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have hs := summable_pow_mul_geometric_of_norm_lt_one e hn
  -- `(R+1)^e ρ^R ≤ 2^e (R^e ρ^R + ρ^R)`
  have hg : Summable (fun R : ℕ => (2 : ℝ) ^ e * ((R : ℝ) ^ e * ρ ^ R + ρ ^ R)) :=
    (hs.add (summable_geometric_of_lt_one h0 h1)).mul_left _
  refine Summable.of_nonneg_of_le (fun R => by positivity) (fun R => ?_) hg
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hpow : ((R : ℝ) + 1) ^ e ≤ 2 ^ e * ((R : ℝ) ^ e + 1) := by
    rcases le_or_gt 1 (R : ℝ) with h | h
    · calc ((R : ℝ) + 1) ^ e ≤ (2 * R) ^ e := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = 2 ^ e * (R : ℝ) ^ e := by rw [mul_pow]
        _ ≤ 2 ^ e * ((R : ℝ) ^ e + 1) := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) e]
    · have hR1 : (R : ℝ) + 1 ≤ 2 := by linarith
      calc ((R : ℝ) + 1) ^ e ≤ 2 ^ e := pow_le_pow_left₀ (by positivity) hR1 _
        _ ≤ 2 ^ e * ((R : ℝ) ^ e + 1) := by
            nlinarith [pow_nonneg hR e, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) e]
  have hρR : 0 ≤ ρ ^ R := pow_nonneg h0 R
  calc ((R : ℝ) + 1) ^ e * ρ ^ R ≤ 2 ^ e * ((R : ℝ) ^ e + 1) * ρ ^ R :=
        mul_le_mul_of_nonneg_right hpow hρR
    _ = 2 ^ e * ((R : ℝ) ^ e * ρ ^ R + ρ ^ R) := by ring

/-- For a summable non-negative sequence, the finite sums over the indices greater than `J` only are small if `J` is large. -/
theorem tail_finset_small {f : ℕ → ℝ} (hf0 : ∀ R, 0 ≤ f R) (hf : Summable f) :
    ∀ ε > 0, ∃ J : ℕ, ∀ S : Finset ℕ, (∀ R ∈ S, J < R) → ∑ R ∈ S, f R ≤ ε := by
  intro ε hε
  have ht := tendsto_sum_nat_add f
  obtain ⟨J, hJ⟩ := eventually_atTop.mp ((tendsto_order.1 ht).2 ε hε)
  refine ⟨J, fun S hS => ?_⟩
  have hsh : Summable (fun k => f (k + J)) := (summable_nat_add_iff J).mpr hf
  have hinj : Set.InjOn (fun R => R - J) (S : Set ℕ) := by
    intro x hx y hy h
    have hx' := hS x hx
    have hy' := hS y hy
    simp only at h
    omega
  have e : ∑ R ∈ S, f R = ∑ k ∈ S.image (fun R => R - J), f (k + J) := by
    rw [sum_image hinj]
    refine sum_congr rfl (fun R hR => ?_)
    have := hS R hR
    congr 1
    omega
  rw [e]
  exact le_trans (hsh.sum_le_tsum _ (fun k _ => hf0 _)) (hJ J le_rfl).le

/-- **Small tails** (`δ(J) → 0` of an internal review): if `C ≥ 0`, `A R ≤ α R + α'`, `R ≤ κ K R + κ'` (`κ ≥ 1`) and `0 ≤ q < 1`,
then `∀ ε > 0, ∃ J` such that the finite sums over ranges greater than `J` only satisfy `Σ_{R ∈ S} C (R+1)^d ((A R + 1) q^{K R}) ≤ ε`. -/
theorem tail_small (C : ℚ) (hC : 0 ≤ C) (d : ℕ) (α α' : ℚ) (hα : 0 ≤ α) (hα' : 0 ≤ α')
    (κ κ' : ℕ) (hκ : 1 ≤ κ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (A K : ℕ → ℕ)
    (hA : ∀ R, (A R : ℚ) ≤ α * R + α') (hK : ∀ R, R ≤ κ * K R + κ') :
    ∀ ε : ℚ, 0 < ε → ∃ J : ℕ, ∀ S : Finset ℕ, (∀ R ∈ S, J < R) →
      ∑ R ∈ S, C * ((R : ℚ) + 1) ^ d * ((A R + 1) * q ^ K R) ≤ ε := by
  intro ε hε
  -- `ρ := max (q^{1/κ}) (1/2)`: `0 < ρ < 1`, `q ≤ ρ^κ`
  set qr : ℝ := (q : ℝ) with hqr
  have hqr0 : 0 ≤ qr := by rw [hqr]; exact_mod_cast hq0
  have hqr1 : qr < 1 := by rw [hqr]; exact_mod_cast hq1
  have hκpos : (0 : ℝ) < κ := by exact_mod_cast hκ
  set ρ : ℝ := max (qr ^ ((1 : ℝ) / κ)) (1 / 2) with hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ1 : ρ < 1 := max_lt (Real.rpow_lt_one hqr0 hqr1 (by positivity)) (by norm_num)
  have hqρ : qr ≤ ρ ^ κ := by
    have h1 : qr = (qr ^ ((1 : ℝ) / κ)) ^ κ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hqr0, one_div, inv_mul_cancel₀ hκpos.ne',
        Real.rpow_one]
    rw [h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hqr0 _) (le_max_left _ _) _
  -- the bound `f R ≤ M (R+1)^{d+1} ρ^R` for each term
  set M : ℝ := (C : ℝ) * (α + α' + 1) / ρ ^ κ' with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
    have : (0 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
    have : (0 : ℝ) ≤ (α' : ℝ) := by exact_mod_cast hα'
    positivity
  have hterm : ∀ R : ℕ, ((C * ((R : ℚ) + 1) ^ d * ((A R + 1) * q ^ K R) : ℚ) : ℝ) ≤
      M * (((R : ℝ) + 1) ^ (d + 1) * ρ ^ R) := by
    intro R
    push_cast
    have hCr : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
    have hαr : (0 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
    have hα'r : (0 : ℝ) ≤ (α' : ℝ) := by exact_mod_cast hα'
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    -- `q^{K R} ≤ ρ^R / ρ^{κ'}`
    have hq : qr ^ K R ≤ ρ ^ R / ρ ^ κ' := by
      calc qr ^ K R ≤ (ρ ^ κ) ^ K R := pow_le_pow_left₀ hqr0 hqρ _
        _ = ρ ^ (κ * K R) := by rw [← pow_mul]
        _ ≤ ρ ^ (R - κ') := pow_le_pow_of_le_one hρ0.le hρ1.le (by have := hK R; omega)
        _ ≤ ρ ^ R / ρ ^ κ' := by
            rw [le_div_iff₀ (by positivity), ← pow_add]
            exact pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)
    -- `A R + 1 ≤ (α + α' + 1)(R + 1)`
    have hAr : (A R : ℝ) + 1 ≤ (α + α' + 1) * ((R : ℝ) + 1) := by
      have h := hA R
      have h' : ((A R : ℚ) : ℝ) ≤ ((α * R + α' : ℚ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      nlinarith
    have hqK0 : 0 ≤ qr ^ K R := pow_nonneg hqr0 _
    have hpd : 0 ≤ ((R : ℝ) + 1) ^ d := by positivity
    calc (C : ℝ) * ((R : ℝ) + 1) ^ d * (((A R : ℝ) + 1) * qr ^ K R)
        ≤ (C : ℝ) * ((R : ℝ) + 1) ^ d * (((α + α' + 1) * ((R : ℝ) + 1)) * (ρ ^ R / ρ ^ κ')) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hAr hq hqK0 (by positivity)
      _ = M * (((R : ℝ) + 1) ^ (d + 1) * ρ ^ R) := by
          rw [hM, pow_succ]
          field_simp
  -- the tail
  have hsum := summable_succ_pow_mul_geom (d + 1) hρ0.le hρ1
  have hsumM : Summable (fun R : ℕ => M * (((R : ℝ) + 1) ^ (d + 1) * ρ ^ R)) := hsum.mul_left M
  obtain ⟨J, hJ⟩ := tail_finset_small (fun R => by positivity) hsumM (ε : ℝ) (by exact_mod_cast hε)
  refine ⟨J, fun S hS => ?_⟩
  have hreal : ((∑ R ∈ S, C * ((R : ℚ) + 1) ^ d * ((A R + 1) * q ^ K R) : ℚ) : ℝ) ≤ (ε : ℝ) := by
    rw [Rat.cast_sum]
    exact le_trans (sum_le_sum (fun R _ => hterm R)) (hJ S hS)
  exact_mod_cast hreal

/-! ## §2 Few long runs of misses (Proposition 12.24, a weak form) -/

/-- **`gap_twin`** (Proposition 12.24, a weak form): if the proportion of uniform words without `P` is at most `η < 1`,
there are `n₀` and `c > 0` depending only on `a` and `η` such that, for `n₁ ≥ n₀`, a polynomial weight `C (R+1)^d` and a linear window
(`A R ≤ α R + α'`, `R ≤ κ K R + κ'`), `∀ ε η' > 0, ∃ J` such that for every `β₀`, `k`, set `I` of groups (fitting in `k`
blocks) and set `S` of ranges (greater than `J`),
`Pr(ε |I| < Σ_{i ∈ I} Σ_{R ∈ S} C (R+1)^d 1[RunMiss i (A R) (K R)]) ≤ η'`. -/
theorem gap_twin (P : Word → Prop) (a : ℕ) (η : ℚ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hP : MissFrac P a η) :
    ∃ n₀ : ℕ, ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ ∀ n₁ ≥ n₀,
      ∀ (C : ℚ) (d : ℕ) (α α' : ℚ) (κ κ' : ℕ) (A K : ℕ → ℕ),
        0 ≤ C → 0 ≤ α → 0 ≤ α' → 1 ≤ κ → (∀ R, (A R : ℚ) ≤ α * R + α') →
        (∀ R, R ≤ κ * K R + κ') →
      ∀ ε : ℚ, 0 < ε → ∀ η' : ℚ, 0 < η' → ∃ J : ℕ, ∀ (β₀ : List Bool) (k : ℕ) (I S : Finset ℕ),
        (∀ i ∈ I, (i + 1) * (n₁ + a) ≤ k) → (∀ R ∈ S, J < R) →
        Prσ β₀ k (fun β => ε * I.card < ∑ i ∈ I, ∑ R ∈ S,
          C * ((R : ℚ) + 1) ^ d * (if RunMiss P β₀.length n₁ a i (A R) (K R) β then 1 else 0)) ≤ η' := by
  obtain ⟨n₀, c, hc0, hc1, hchain⟩ := gap_chain' P a η hη0 hη1 hP
  refine ⟨n₀, c, hc0, hc1, fun n₁ hn₁ C d α α' κ κ' A K hC hα hα' hκ hA hK ε hε η' hη' => ?_⟩
  obtain ⟨J, hJ⟩ := tail_small C hC d α α' hα hα' κ κ' hκ (1 - c) (by linarith) (by linarith) A K hA hK
    (ε * η') (by positivity)
  refine ⟨J, fun β₀ k I S hI hS => ?_⟩
  set w : ℕ → ℚ := fun R => C * ((R : ℚ) + 1) ^ d with hw
  have hw0 : ∀ R, 0 ≤ w R := fun R => by rw [hw]; positivity
  set X : List Bool → ℚ := fun β => ∑ i ∈ I, ∑ R ∈ S,
    C * ((R : ℚ) + 1) ^ d * (if RunMiss P β₀.length n₁ a i (A R) (K R) β then 1 else 0) with hX
  have hX0 : ∀ β, 0 ≤ X β := fun β => by
    rw [hX]
    exact sum_nonneg (fun i _ => sum_nonneg (fun R _ => mul_nonneg (by positivity)
      (by split_ifs <;> norm_num)))
  rcases Nat.eq_zero_or_pos I.card with hI0 | hIpos
  · -- if `I` is empty, the event does not occur
    rw [prσ_false β₀ k _ (fun β hβ => ?_)]
    · exact hη'.le
    · have hIe : I = ∅ := card_eq_zero.mp hI0
      simp [hIe] at hβ
  · have hIq : (0 : ℚ) < I.card := by exact_mod_cast hIpos
    have hmk := prσ_markov β₀ k X hX0 (ε * I.card) (by positivity)
    have hexp : ∑ β ∈ blockChoices k, wtβ β * X (β₀ ++ β) ≤
        I.card * ∑ R ∈ S, w R * ((A R + 1) * (1 - c) ^ K R) := by
      have := run_expect_groups P a n₁ (1 - c) (by linarith) (hchain n₁ hn₁) β₀ k I hI S w hw0 A K
      convert this using 1
    have htail : ∑ R ∈ S, w R * ((A R + 1) * (1 - c) ^ K R) ≤ ε * η' := hJ S hS
    calc Prσ β₀ k (fun β => ε * I.card < X β)
        ≤ (∑ β ∈ blockChoices k, wtβ β * X (β₀ ++ β)) / (ε * I.card) := hmk
      _ ≤ (I.card * (ε * η')) / (ε * I.card) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact le_trans hexp (mul_le_mul_of_nonneg_left htail hIq.le)
      _ = η' := by field_simp

/-! ## §3 The side of the free bits -/

/-- **Runs on the free bits**: among the binary words of length `L`, those in which `v` does not occur in a window of length `Lw` starting
somewhere in the positions `[a, a + A]` (`a + A + Lw ≤ L`) number at most `(A + 1) 2^L (1 - 2^{-|v|})^{⌊Lw/|v|⌋}`. -/
theorem free_run_le (L a A Lw : ℕ) {v : Word} (hv : v ∈ wordsOfLen v.length) (hb : a + A + Lw ≤ L) :
    (((wordsOfLen L).filter (fun w => ∃ s, a ≤ s ∧ s ≤ a + A ∧
        ∀ i, s ≤ i → i + v.length ≤ s + Lw → window w i v.length ≠ v)).card : ℚ) ≤
      (A + 1) * (2 ^ L * (1 - 1 / 2 ^ v.length) ^ (Lw / v.length)) := by
  set F : ℕ → Finset Word := fun s => (wordsOfLen L).filter (fun w =>
    ∀ i, s ≤ i → i + v.length ≤ s + Lw → window w i v.length ≠ v) with hF
  have hsub : (wordsOfLen L).filter (fun w => ∃ s, a ≤ s ∧ s ≤ a + A ∧
      ∀ i, s ≤ i → i + v.length ≤ s + Lw → window w i v.length ≠ v) ⊆ (Icc a (a + A)).biUnion F := by
    intro w hw
    obtain ⟨hwL, s, hs1, hs2, hs3⟩ := mem_filter.mp hw
    exact mem_biUnion.mpr ⟨s, mem_Icc.mpr ⟨hs1, hs2⟩, mem_filter.mpr ⟨hwL, hs3⟩⟩
  have hcard := le_trans (card_le_card hsub) card_biUnion_le
  have hterm : ∀ s ∈ Icc a (a + A), ((F s).card : ℚ) ≤ 2 ^ L * (1 - 1 / 2 ^ v.length) ^ (Lw / v.length) := by
    intro s hs
    have hsL : s + Lw ≤ L := by have := (mem_Icc.mp hs).2; omega
    have h := card_noOcc_le L s (s + Lw) hv hsL
    rw [Nat.add_sub_cancel_left] at h
    exact h
  calc (((wordsOfLen L).filter (fun w => ∃ s, a ≤ s ∧ s ≤ a + A ∧
        ∀ i, s ≤ i → i + v.length ≤ s + Lw → window w i v.length ≠ v)).card : ℚ)
      ≤ ((∑ s ∈ Icc a (a + A), (F s).card : ℕ) : ℚ) := by exact_mod_cast hcard
    _ = ∑ s ∈ Icc a (a + A), ((F s).card : ℚ) := by push_cast; rfl
    _ ≤ ∑ s ∈ Icc a (a + A), (2 ^ L * (1 - 1 / 2 ^ v.length) ^ (Lw / v.length)) := sum_le_sum hterm
    _ = ((Icc a (a + A)).card : ℚ) * (2 ^ L * (1 - 1 / 2 ^ v.length) ^ (Lw / v.length)) := by
        rw [sum_const, nsmul_eq_mul]
    _ = (A + 1) * (2 ^ L * (1 - 1 / 2 ^ v.length) ^ (Lw / v.length)) := by
        rw [Nat.card_Icc]
        congr 1
        push_cast [show a + A + 1 - a = A + 1 by omega]
        ring

/-- **Expectation on the side of the free bits** (counting form): for weights `w R ≥ 0` for each range `R ∈ S`, start widths `A R` and window
lengths `Lw R` (`a + A R + Lw R ≤ L`), `Σ_{w} Σ_R w R 1[the run occurs] ≤ 2^L Σ_R w R (A R + 1)(1 - 2^{-|v|})^{⌊Lw R/|v|⌋}`. -/
theorem free_expect (L a : ℕ) {v : Word} (hv : v ∈ wordsOfLen v.length) (S : Finset ℕ) (w : ℕ → ℚ)
    (hw : ∀ R, 0 ≤ w R) (A Lw : ℕ → ℕ) (hb : ∀ R ∈ S, a + A R + Lw R ≤ L) :
    ∑ x ∈ wordsOfLen L, ∑ R ∈ S, w R * (if ∃ s, a ≤ s ∧ s ≤ a + A R ∧
        ∀ i, s ≤ i → i + v.length ≤ s + Lw R → window x i v.length ≠ v then 1 else 0) ≤
      2 ^ L * ∑ R ∈ S, w R * ((A R + 1) * (1 - 1 / 2 ^ v.length) ^ (Lw R / v.length)) := by
  rw [sum_comm, mul_sum]
  refine sum_le_sum (fun R hR => ?_)
  rw [← mul_sum, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have h := free_run_le L a (A R) (Lw R) hv (hb R hR)
  calc w R * (((wordsOfLen L).filter (fun x => ∃ s, a ≤ s ∧ s ≤ a + A R ∧
        ∀ i, s ≤ i → i + v.length ≤ s + Lw R → window x i v.length ≠ v)).card : ℚ)
      ≤ w R * ((A R + 1) * (2 ^ L * (1 - 1 / 2 ^ v.length) ^ (Lw R / v.length))) :=
        mul_le_mul_of_nonneg_left h (hw R)
    _ = 2 ^ L * (w R * ((A R + 1) * (1 - 1 / 2 ^ v.length) ^ (Lw R / v.length))) := by ring

end Collatz.Arctic.NatQ5.W3b
