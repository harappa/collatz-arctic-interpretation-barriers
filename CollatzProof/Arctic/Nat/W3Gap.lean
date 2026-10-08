/-
# Natural-number interpretations of 𝒯 (Section 12.7): the chain of groups `gap_chain` (the probabilistic part of the tail bounds)

The chain part of the tail bounds. Its written counterparts are Lemma 12.23 (i) of the paper (`HKeyTop`, Theorem B.7, chained group by group)
and a lemma of an earlier, longer argument that is not used here (windows counted by block indices; the bookkeeping trap). Following internal
review, **probabilities are counted by group indices** (read by bit positions, the groups covered by a window move with `σ`, and the union has `O(m²)` terms).
The logarithmic-window theorem of that earlier argument and its corollary are not used.

**Groups**: the random blocks after the prefix `β₀` (`b₀ := |β₀|` blocks) are split into groups of `g := n₁ + a` blocks (group `i` has
the remaining indices `[i g, (i+1) g)`, counted from 0). The last `a` blocks of group `i` form its **target cut**, and the `n₁` blocks before it
are the mixing part of `HKeyTop`. The cut word `cutWord a β c` is the part of the bits of the cut in the expansion of `r_σ` (`cutWord_segment`,
`HTWCut.htw_bits_split`). Group `i` is a **hit** (`GHit P …`) if the word of its target cut has the property `P`.

* `cutWord_take`, `cutWord_append`: the cut word is determined by the blocks up to the end of the cut (the bits are identified by the Terras
  consistency `terrasR_append`; a version of `HTWCut.htw_good_take` for general properties). `cutWord_cut`: the cut word in terms of the
  quantities of `HKeyTop`.
* `cut_miss_le`: the probability that one cut misses is at most `2τ + η`, however the earlier blocks are fixed (`HTWProb.htw_cut_prob` for
  a general property `P`; `η` is the proportion of uniform words without `P`).
* `chain_le`: the probability that all groups with indices in `[j, j + K)` miss is at most `(2τ + η)^K` (Fubini via `sum_split`, and
  `cut_miss_le` applied from the last group backwards).
* **`gap_chain`**: if `η < 1`, then `∃ n₀ c > 0, ∀ n₁ ≥ n₀`, the probability that `K` consecutive groups all miss is at most `(1 - c)^K`
  (`c = (1 - η)/2`). **`gap_chain_infix`**: for the property "the cut word contains the word `bitsMSB ℓ v`" (`ℓ ≤ 8a`),
  `c = 2^{-ℓ-1}`.
* **`gap_run`** (an abstraction added after internal review): the probability that the indices `[i - A, i]` contain `K` consecutive groups that all miss is
  at most `(A + 1)(1 - c)^K` (`RunMiss`).
* `run_expect`, `run_expect_groups`: for weights `w R` and windows `A R`, `K R` for each range `R` of a detour, the expectation per group is
  `E[Σ_R w R 1[RunMiss i (A R) (K R)]] ≤ Σ_R w R (A R + 1)(1 - c)^{K R}`; summed over a set `I` of groups, it is multiplied by `|I|`.
  That the tail is small (polynomial weights against an exponential tail) is shown in `W3GapTail.lean`.

All auxiliary declarations are in the namespace `Collatz.Arctic.NatQ5.W3b`. No `sorry`, `axiom` or `native_decide` is used.
-/
import CollatzProof.Arctic.Nat.W3bBase
import CollatzProof.Arctic.KeyFinal

namespace Collatz.Arctic.NatQ5.W3b

open Collatz.Arctic Finset
open Classical

/-! ## §1 Cut words -/

/-- The word of the cut `[c, c + K)` (block indices): the part of the bits of the cut in the expansion of `r_σ` from the most significant end. -/
def cutWord (K : ℕ) (β : List Bool) (c : ℕ) : Word := bitsMSB (htwLen K β c) (htwVal K β c)

theorem cutWord_length (K : ℕ) (β : List Bool) (c : ℕ) :
    (cutWord K β c).length = htwLen K β c := bitsMSB_length _ _

/-- The cut word is determined by the blocks up to the end of the cut. -/
theorem cutWord_take (K : ℕ) (β : List Bool) (c : ℕ) :
    cutWord K (β.take (c + K)) c = cutWord K β c := by
  have h1 : htwLen K (β.take (c + K)) c = htwLen K β c := by
    unfold htwLen
    rw [List.drop_take, List.take_take, show min K (c + K - c) = K by omega]
  have h2 : htwVal K (β.take (c + K)) c = htwVal K β c := by
    unfold htwVal
    rw [List.take_take, List.take_take, min_self, min_eq_left (by omega)]
  unfold cutWord
  rw [h1, h2]

/-- Appending blocks does not change the cut word (when the cut lies in `β`). -/
theorem cutWord_append (K : ℕ) (β δ : List Bool) (c : ℕ) (h : c + K ≤ β.length) :
    cutWord K (β ++ δ) c = cutWord K β c := by
  rw [← cutWord_take K (β ++ δ) c, List.take_append_of_le_length h, cutWord_take]

/-- The cut word in terms of the quantities of `HKeyTop`. -/
theorem cutWord_cut (K : ℕ) (β₀ β₁ γ : List Bool) (hγ : γ.length = K) :
    cutWord K (β₀ ++ β₁ ++ γ) (β₀ ++ β₁).length =
      bitsMSB (parityOf γ).length (htwCutVal β₀ β₁ γ) := by
  have h1 : htwLen K (β₀ ++ β₁ ++ γ) (β₀ ++ β₁).length = (parityOf γ).length := by
    unfold htwLen
    rw [List.drop_left, List.take_of_length_le (by omega)]
  have h2 : htwVal K (β₀ ++ β₁ ++ γ) (β₀ ++ β₁).length = htwCutVal β₀ β₁ γ := by
    unfold htwVal htwCutVal
    rw [List.take_left, List.take_of_length_le (by simp only [List.length_append]; omega)]
  unfold cutWord
  rw [h1, h2]

/-- **Identification of the bits** (the interface to downstream): the cut word is a factor of the `m`-digit expansion of `r_σ`, and the part
before it has length `m - L_{c+K}` (`HTWCut.htw_bits_split`). -/
theorem cutWord_segment (β : List Bool) (c K : ℕ) :
    ∃ X Y : Word, bitsMSB (parityOf β).length (terrasR (parityOf β)) = X ++ cutWord K β c ++ Y ∧
      X.length = (parityOf β).length - blockEnd β (c + K) :=
  htw_bits_split β c K

/-- The cut word has length at least `8K` (when the cut lies in `β`). -/
theorem cutWord_length_ge (K : ℕ) (β : List Bool) (c : ℕ) (h : c + K ≤ β.length) :
    8 * K ≤ (cutWord K β c).length := by
  rw [cutWord_length]
  have hb := htw_blockEnd_ge β c K h
  rw [htw_blockEnd_add] at hb
  omega

/-! ## §2 The probability that one cut misses -/

/-- The form of the conclusion of `HKeyTop` (`a` blocks in the cut, total variation distance `τ`, mixing part of length at least `n₀`). -/
def KeyAt (a : ℕ) (τ : ℚ) (n₀ : ℕ) : Prop :=
  ∀ n ≥ n₀, ∀ (β₀ γ : List Bool), γ.length = a →
    ∑ u ∈ Finset.range (2 ^ (parityOf γ).length),
      |(∑ β ∈ (blockChoices n).filter (fun β =>
          terrasR (parityOf (β₀ ++ β ++ γ)) / 2 ^ (parityOf (β₀ ++ β)).length = u), wtβ β)
        - 1 / 2 ^ (parityOf γ).length| ≤ 2 * τ

/-- The proportion of uniform words without the property `P` is at most `η` (for each choice `γ` of the blocks of the cut). -/
def MissFrac (P : Word → Prop) (a : ℕ) (η : ℚ) : Prop :=
  ∀ γ : List Bool, γ.length = a →
    (((Finset.range (2 ^ (parityOf γ).length)).filter (fun u =>
      ¬ P (bitsMSB (parityOf γ).length u))).card : ℚ) ≤ η * 2 ^ (parityOf γ).length

/-- **The probability that one cut misses**: the probability that the word of the cut `[|β₀| + j, |β₀| + j + a)` (`n₀ ≤ j`, `j + a ≤ k`) does not
have `P` is at most `2τ + η`, however the earlier blocks `β₀` are fixed. -/
theorem cut_miss_le (P : Word → Prop) (a : ℕ) (τ η : ℚ) (n₀ : ℕ) (hkey : KeyAt a τ n₀)
    (hP : MissFrac P a η) (β₀ : List Bool) (k j : ℕ) (hj : n₀ ≤ j) (hjk : j + a ≤ k) :
    ∑ β ∈ blockChoices k,
      wtβ β * (if P (cutWord a (β₀ ++ β) (β₀.length + j)) then 0 else 1) ≤ 2 * τ + η := by
  set F : List Bool → ℚ := fun x => if P (cutWord a (β₀ ++ x) (β₀.length + j)) then 0 else 1
    with hF
  have hloc : ∀ β ∈ blockChoices k,
      (if P (cutWord a (β₀ ++ β) (β₀.length + j)) then (0 : ℚ) else 1) = F (β.take (j + a)) := by
    intro β _
    rw [hF]
    simp only
    have e : (β₀ ++ β).take (β₀.length + j + a) = β₀ ++ β.take (j + a) := by
      rw [show β₀.length + j + a = β₀.length + (j + a) by omega, List.take_length_add_append]
    have hg := cutWord_take a (β₀ ++ β) (β₀.length + j)
    rw [e] at hg
    rw [hg]
  rw [sum_congr rfl (fun β hβ => by rw [hloc β hβ])]
  rw [show k = (j + a) + (k - (j + a)) by omega, walk_sum_take]
  have hsplit := htw_sum_split j a (fun β₁ γ => F (β₁ ++ γ))
  simp only [List.take_append_drop] at hsplit
  rw [hsplit]
  have hcut : ∀ β₁ ∈ blockChoices j, ∀ γ ∈ blockChoices a,
      F (β₁ ++ γ) = if ¬ P (bitsMSB (parityOf γ).length (htwCutVal β₀ β₁ γ)) then 1 else 0 := by
    intro β₁ hβ₁ γ hγ
    have hl₁ := length_of_mem_blockChoices hβ₁
    have hlγ := length_of_mem_blockChoices hγ
    have hg := cutWord_cut a β₀ β₁ γ hlγ
    rw [List.length_append, hl₁] at hg
    rw [hF]
    simp only
    rw [← List.append_assoc, hg]
    split_ifs <;> simp_all
  rw [sum_congr rfl (fun β₁ hβ₁ => sum_congr rfl (fun γ hγ => by rw [hcut β₁ hβ₁ γ hγ]))]
  rw [sum_comm]
  calc ∑ γ ∈ blockChoices a, ∑ β₁ ∈ blockChoices j, wtβ β₁ * (wtβ γ *
        (if ¬ P (bitsMSB (parityOf γ).length (htwCutVal β₀ β₁ γ)) then (1 : ℚ) else 0))
      = ∑ γ ∈ blockChoices a, wtβ γ * ∑ β₁ ∈ blockChoices j, wtβ β₁ *
        (if ¬ P (bitsMSB (parityOf γ).length (htwCutVal β₀ β₁ γ)) then (1 : ℚ) else 0) := by
        refine sum_congr rfl (fun γ _ => ?_)
        rw [mul_sum]
        refine sum_congr rfl (fun β₁ _ => ?_)
        ring
    _ ≤ ∑ γ ∈ blockChoices a, wtβ γ * (2 * τ + η) := by
        refine sum_le_sum (fun γ hγ => mul_le_mul_of_nonneg_left ?_ (fam_wt_nonneg γ))
        have hlγ := length_of_mem_blockChoices hγ
        exact htw_bad_le β₀ γ j τ η (fun w => ¬ P w) (hkey j hj β₀ γ hlγ) (hP γ hlγ)
    _ = 2 * τ + η := by rw [← sum_mul, sum_wt, one_mul]

/-! ## §3 Chains of groups -/

/-- Group `i` (remaining block indices `[i g, (i+1) g)`, `g = n₁ + a`) is a hit: the word of the target cut
`[b₀ + i g + n₁, b₀ + (i+1) g)` has `P`. Here `β` is the whole choice, including the prefix blocks. -/
def GHit (P : Word → Prop) (b₀ n₁ a i : ℕ) (β : List Bool) : Prop :=
  P (cutWord a β (b₀ + i * (n₁ + a) + n₁))

/-- Whether group `i` is a hit is determined by the blocks up to the end of group `i`. -/
theorem gHit_append (P : Word → Prop) (b₀ n₁ a i : ℕ) (β δ : List Bool)
    (h : b₀ + (i + 1) * (n₁ + a) ≤ β.length) :
    GHit P b₀ n₁ a i (β ++ δ) ↔ GHit P b₀ n₁ a i β := by
  unfold GHit
  rw [cutWord_append a β δ _ (by nlinarith)]

/-- All groups with indices in `[j, j + K)` miss (given a name so that `Decidable` inference does not enter the concrete form). -/
def AllMiss (P : Word → Prop) (b₀ n₁ a j K : ℕ) (β : List Bool) : Prop :=
  ∀ i, j ≤ i → i < j + K → ¬ GHit P b₀ n₁ a i β

/-- **Chain of groups** (Lemma 12.23 (i)): if `n₁ ≥ n₀`, the probability that all groups with indices in `[j, j + K)` miss is at most
`(2τ + η)^K` (`(j + K) g ≤ k`). -/
theorem chain_le (P : Word → Prop) (a : ℕ) (τ η : ℚ) (n₀ : ℕ) (hkey : KeyAt a τ n₀)
    (hP : MissFrac P a η) (hρ : 0 ≤ 2 * τ + η) (n₁ : ℕ) (hn₁ : n₀ ≤ n₁) (β₀ : List Bool) (j : ℕ) :
    ∀ K k : ℕ, (j + K) * (n₁ + a) ≤ k →
      ∑ β ∈ blockChoices k, wtβ β * (if AllMiss P β₀.length n₁ a j K (β₀ ++ β) then 1 else 0) ≤
        (2 * τ + η) ^ K := by
  intro K
  induction K with
  | zero =>
    intro k _
    rw [pow_zero]
    exact sum_ind_le_one k _
  | succ K ih =>
    intro k hk
    set g := n₁ + a with hg
    set N := (j + K) * g with hN
    have hNk : N + g ≤ k := by
      have : (j + (K + 1)) * g = N + g := by rw [hN]; ring
      omega
    rw [show k = N + (k - N) by omega, sum_split]
    -- for each `β₁`, split into the event of the first `K` groups and the event of the last group
    have hfac : ∀ β₁ ∈ blockChoices N, ∀ β₂ : List Bool,
        (if AllMiss P β₀.length n₁ a j (K + 1) (β₀ ++ (β₁ ++ β₂)) then (1 : ℚ) else 0) =
        (if AllMiss P β₀.length n₁ a j K (β₀ ++ β₁) then 1 else 0) *
        (if P (cutWord a ((β₀ ++ β₁) ++ β₂) ((β₀ ++ β₁).length + n₁)) then 0 else 1) := by
      intro β₁ hβ₁ β₂
      have hl := length_of_mem_blockChoices hβ₁
      have hlast : GHit P β₀.length n₁ a (j + K) (β₀ ++ (β₁ ++ β₂)) ↔
          P (cutWord a ((β₀ ++ β₁) ++ β₂) ((β₀ ++ β₁).length + n₁)) := by
        unfold GHit
        rw [← List.append_assoc, List.length_append, hl]
      have hearly : ∀ i, i < j + K →
          (GHit P β₀.length n₁ a i (β₀ ++ (β₁ ++ β₂)) ↔ GHit P β₀.length n₁ a i (β₀ ++ β₁)) := by
        intro i hi
        rw [← List.append_assoc]
        apply gHit_append
        rw [List.length_append, hl, hN, hg]
        have : (i + 1) * (n₁ + a) ≤ (j + K) * (n₁ + a) := Nat.mul_le_mul_right _ (by omega)
        omega
      by_cases hA : AllMiss P β₀.length n₁ a j K (β₀ ++ β₁)
      · by_cases hB : P (cutWord a ((β₀ ++ β₁) ++ β₂) ((β₀ ++ β₁).length + n₁))
        · have hn : ¬ AllMiss P β₀.length n₁ a j (K + 1) (β₀ ++ (β₁ ++ β₂)) := by
            intro hall
            exact hall (j + K) (by omega) (by omega) (hlast.mpr hB)
          simp only [hn, hA, hB, ↓reduceIte]; ring
        · have hy : AllMiss P β₀.length n₁ a j (K + 1) (β₀ ++ (β₁ ++ β₂)) := by
            intro i hji hi
            rcases Nat.lt_or_ge i (j + K) with h | h
            · rw [hearly i h]; exact hA i hji h
            · have : i = j + K := by omega
              subst this
              rw [hlast]; exact hB
          simp only [hy, hA, hB, ↓reduceIte]; ring
      · have hn : ¬ AllMiss P β₀.length n₁ a j (K + 1) (β₀ ++ (β₁ ++ β₂)) := by
          intro hall
          apply hA
          intro i hji hi
          rw [← hearly i hi]
          exact hall i hji (by omega)
        simp only [hn, hA, ↓reduceIte]; ring
    calc ∑ β₁ ∈ blockChoices N, wtβ β₁ * ∑ β₂ ∈ blockChoices (k - N), wtβ β₂ *
          (if AllMiss P β₀.length n₁ a j (K + 1) (β₀ ++ (β₁ ++ β₂)) then (1 : ℚ) else 0)
        = ∑ β₁ ∈ blockChoices N, wtβ β₁ *
          ((if AllMiss P β₀.length n₁ a j K (β₀ ++ β₁) then 1 else 0) *
          ∑ β₂ ∈ blockChoices (k - N), wtβ β₂ *
            (if P (cutWord a ((β₀ ++ β₁) ++ β₂) ((β₀ ++ β₁).length + n₁)) then 0 else 1)) := by
          refine sum_congr rfl (fun β₁ hβ₁ => ?_)
          congr 1
          rw [mul_sum]
          refine sum_congr rfl (fun β₂ _ => ?_)
          rw [hfac β₁ hβ₁ β₂]
          ring
      _ ≤ ∑ β₁ ∈ blockChoices N, wtβ β₁ *
          ((if AllMiss P β₀.length n₁ a j K (β₀ ++ β₁) then 1 else 0) * (2 * τ + η)) := by
          refine sum_le_sum (fun β₁ _ => mul_le_mul_of_nonneg_left ?_ (fam_wt_nonneg β₁))
          refine mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> norm_num)
          exact cut_miss_le P a τ η n₀ hkey hP (β₀ ++ β₁) (k - N) n₁ hn₁ (by omega)
      _ = (∑ β₁ ∈ blockChoices N, wtβ β₁ *
          (if AllMiss P β₀.length n₁ a j K (β₀ ++ β₁) then 1 else 0)) * (2 * τ + η) := by
          rw [sum_mul]
          refine sum_congr rfl (fun β₁ _ => ?_)
          ring
      _ ≤ (2 * τ + η) ^ K * (2 * τ + η) :=
          mul_le_mul_of_nonneg_right (ih N le_rfl) hρ
      _ = (2 * τ + η) ^ (K + 1) := by rw [pow_succ]

/-- **`gap_chain`** (Lemma 12.23 (i), in the form counted by group indices): if the proportion of uniform words without `P` is at most
`η < 1`, there is `n₀` depending only on `a` and `η` such that, for groups of size `g = n₁ + a` with `n₁ ≥ n₀` and for every `β₀`,
the probability that all groups with indices in `[j, j + K)` miss is at most `((1 + η)/2)^K` (`(j + K) g ≤ k`). With `c := (1 - η)/2`
this is `(1 - c)^K`. -/
theorem gap_chain (P : Word → Prop) (a : ℕ) (η : ℚ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hP : MissFrac P a η) :
    ∃ n₀ : ℕ, ∀ n₁ ≥ n₀, ∀ (β₀ : List Bool) (k j K : ℕ), (j + K) * (n₁ + a) ≤ k →
      Prσ β₀ k (AllMiss P β₀.length n₁ a j K) ≤ ((1 + η) / 2) ^ K := by
  set τ : ℚ := (1 - η) / 4 with hτ
  have hτ0 : 0 < τ := by rw [hτ]; linarith
  obtain ⟨n₀, hn₀⟩ := hKeyTop a τ hτ0
  refine ⟨n₀, fun n₁ hn₁ β₀ k j K hk => ?_⟩
  have hkey : KeyAt a τ n₀ := hn₀
  have e : (1 + η) / 2 = 2 * τ + η := by rw [hτ]; ring
  rw [e, prσ_eq_sum]
  exact chain_le P a τ η n₀ hkey hP (by rw [← e]; linarith) n₁ hn₁ β₀ j K k hk

/-- `gap_chain` in the form with `c`: `∃ n₀ c, 0 < c ≤ 1`, and the probability is at most `(1 - c)^K`. -/
theorem gap_chain' (P : Word → Prop) (a : ℕ) (η : ℚ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hP : MissFrac P a η) :
    ∃ n₀ : ℕ, ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ ∀ n₁ ≥ n₀, ∀ (β₀ : List Bool) (k j K : ℕ),
      (j + K) * (n₁ + a) ≤ k →
      Prσ β₀ k (AllMiss P β₀.length n₁ a j K) ≤ (1 - c) ^ K := by
  obtain ⟨n₀, h⟩ := gap_chain P a η hη0 hη1 hP
  refine ⟨n₀, (1 - η) / 2, by linarith, by linarith, fun n₁ hn₁ β₀ k j K hk => ?_⟩
  rw [show 1 - (1 - η) / 2 = (1 + η) / 2 by ring]
  exact h n₁ hn₁ β₀ k j K hk

/-! ## §4 The property "the cut word contains the word `u`" -/

/-- The `N`-digit expansion of a number whose low `ℓ` digits are `v` contains `bitsMSB ℓ v` (`v < 2^ℓ`, `ℓ ≤ N`). -/
theorem infix_of_mod {ℓ N v w : ℕ} (hv : v < 2 ^ ℓ) (hw : w < 2 ^ (N - ℓ)) (hN : ℓ ≤ N) :
    bitsMSB ℓ v <:+: bitsMSB N (v + 2 ^ ℓ * w) := by
  have h := bitsMSB_add_mul (N - ℓ) ℓ w v hw hv
  rw [Nat.sub_add_cancel hN] at h
  rw [h]
  exact (List.suffix_append _ _).isInfix

/-- At most `2^N - 2^{N-ℓ}` uniform words of `N` digits do not contain `bitsMSB ℓ v`. -/
theorem infix_miss_card {ℓ N v : ℕ} (hv : v < 2 ^ ℓ) (hN : ℓ ≤ N) :
    ((range (2 ^ N)).filter (fun u => ¬ (bitsMSB ℓ v <:+: bitsMSB N u))).card ≤ 2 ^ N - 2 ^ (N - ℓ) := by
  have hpow : 2 ^ N = 2 ^ ℓ * 2 ^ (N - ℓ) := by rw [← pow_add, Nat.add_sub_cancel' hN]
  have hge : 2 ^ (N - ℓ) ≤ ((range (2 ^ N)).filter (fun u => bitsMSB ℓ v <:+: bitsMSB N u)).card := by
    have himg : ((range (2 ^ (N - ℓ))).image (fun w => v + 2 ^ ℓ * w)) ⊆
        (range (2 ^ N)).filter (fun u => bitsMSB ℓ v <:+: bitsMSB N u) := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
      have hw' := mem_range.mp hw
      rw [mem_filter, mem_range]
      refine ⟨?_, infix_of_mod hv hw' hN⟩
      have : 2 ^ ℓ * (w + 1) ≤ 2 ^ ℓ * 2 ^ (N - ℓ) := Nat.mul_le_mul_left _ hw'
      rw [mul_add, mul_one] at this
      omega
    have hinj : Set.InjOn (fun w => v + 2 ^ ℓ * w) (range (2 ^ (N - ℓ)) : Set ℕ) := by
      intro w₁ _ w₂ _ h
      simp only at h
      have : 2 ^ ℓ * w₁ = 2 ^ ℓ * w₂ := by omega
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    calc 2 ^ (N - ℓ) = (range (2 ^ (N - ℓ))).card := (card_range _).symm
      _ = ((range (2 ^ (N - ℓ))).image (fun w => v + 2 ^ ℓ * w)).card := (card_image_of_injOn hinj).symm
      _ ≤ _ := card_le_card himg
  have hsum := card_filter_add_card_filter_not (s := range (2 ^ N))
    (fun u => bitsMSB ℓ v <:+: bitsMSB N u)
  rw [card_range] at hsum
  omega

/-- The miss proportion of the property "the cut word contains `bitsMSB ℓ v`" is at most `1 - 2^{-ℓ}` (`ℓ ≤ 8a`). -/
theorem missFrac_infix {ℓ v a : ℕ} (hv : v < 2 ^ ℓ) (ha : ℓ ≤ 8 * a) :
    MissFrac (fun w => bitsMSB ℓ v <:+: w) a (1 - 1 / 2 ^ ℓ) := by
  intro γ hγ
  simp only
  set N := (parityOf γ).length with hN
  have hlen : ℓ ≤ N := by
    have := (parityOf_length_bounds γ).1
    rw [hγ] at this
    omega
  have hc := infix_miss_card (N := N) hv hlen
  have hpow : (2 : ℚ) ^ N = 2 ^ ℓ * 2 ^ (N - ℓ) := by rw [← pow_add, Nat.add_sub_cancel' hlen]
  have hle : 2 ^ (N - ℓ) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
  have hcq : (((range (2 ^ N)).filter (fun u => ¬ (bitsMSB ℓ v <:+: bitsMSB N u))).card : ℚ) ≤
      ((2 ^ N - 2 ^ (N - ℓ) : ℕ) : ℚ) := by exact_mod_cast hc
  rw [Nat.cast_sub hle] at hcq
  push_cast at hcq
  calc _ ≤ (2 : ℚ) ^ N - 2 ^ (N - ℓ) := by convert hcq using 3
    _ = (1 - 1 / 2 ^ ℓ) * 2 ^ N := by
        rw [hpow]
        field_simp

/-- **`gap_chain_infix`**: for the property "the word of the target cut contains `bitsMSB ℓ v`" (`v < 2^ℓ`, `ℓ ≤ 8a`),
`c = 2^{-ℓ-1}` (the second statement of Lemma 12.23 (i)). -/
theorem gap_chain_infix (ℓ v a : ℕ) (hv : v < 2 ^ ℓ) (ha : ℓ ≤ 8 * a) :
    ∃ n₀ : ℕ, ∀ n₁ ≥ n₀, ∀ (β₀ : List Bool) (k j K : ℕ), (j + K) * (n₁ + a) ≤ k →
      Prσ β₀ k (AllMiss (fun w => bitsMSB ℓ v <:+: w) β₀.length n₁ a j K) ≤
        (1 - 1 / 2 ^ (ℓ + 1)) ^ K := by
  have hp : (0 : ℚ) < 1 / 2 ^ ℓ := by positivity
  have hp1 : (1 : ℚ) / 2 ^ ℓ ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  obtain ⟨n₀, h⟩ := gap_chain _ a (1 - 1 / 2 ^ ℓ) (by linarith) (by linarith)
    (missFrac_infix hv ha)
  refine ⟨n₀, fun n₁ hn₁ β₀ k j K hk => ?_⟩
  have e : 1 - 1 / (2 : ℚ) ^ (ℓ + 1) = (1 + (1 - 1 / 2 ^ ℓ)) / 2 := by rw [pow_succ]; field_simp; ring
  rw [e]
  exact h n₁ hn₁ β₀ k j K hk

/-! ## §5 Runs of misses (an abstraction added after internal review) -/

/-- The indices `[i - A, i]` contain `K` consecutive groups that all miss (an abstraction of the event that occurs when a detour of long range
starts at the position of group `i`; the connection to detours is made downstream, in `W3h*.lean` and `W3hMain.lean`). -/
def RunMiss (P : Word → Prop) (b₀ n₁ a i A K : ℕ) (β : List Bool) : Prop :=
  ∃ j, i ≤ j + A ∧ j + K ≤ i + 1 ∧ AllMiss P b₀ n₁ a j K β

/-- An event that never occurs has probability 0. -/
theorem prσ_false (β₀ : List Bool) (k : ℕ) (E : List Bool → Prop) (h : ∀ β, ¬ E β) :
    Prσ β₀ k E = 0 := by
  unfold Prσ
  refine sum_eq_zero (fun β hβ => ?_)
  exact absurd (mem_filter.mp hβ).2 (h _)

/-- **`run_le`**: from the chain bound `ρ^K` (`hchain`), the probability that the indices `[i - A, i]` contain `K` consecutive groups that all
miss is at most `(A + 1) ρ^K` (`(i + 1) g ≤ k`; a union bound over the starting index `j`). -/
theorem run_le (P : Word → Prop) (a n₁ : ℕ) (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hchain : ∀ (β₀ : List Bool) (k j K : ℕ), (j + K) * (n₁ + a) ≤ k →
      Prσ β₀ k (AllMiss P β₀.length n₁ a j K) ≤ ρ ^ K)
    (β₀ : List Bool) (k i A K : ℕ) (hk : (i + 1) * (n₁ + a) ≤ k) :
    Prσ β₀ k (RunMiss P β₀.length n₁ a i A K) ≤ (A + 1) * ρ ^ K := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    rw [pow_zero, mul_one]
    have hA : (0 : ℚ) ≤ A := Nat.cast_nonneg _
    linarith [prσ_le_one β₀ k (RunMiss P β₀.length n₁ a i A 0)]
  · have hsub : Prσ β₀ k (RunMiss P β₀.length n₁ a i A K) ≤
        Prσ β₀ k (fun β => ∃ j ∈ Icc (i - A) i, j + K ≤ i + 1 ∧ AllMiss P β₀.length n₁ a j K β) := by
      refine Prσ_mono β₀ k (fun β _ hβ => ?_)
      obtain ⟨j, h1, h2, h3⟩ := hβ
      exact ⟨j, mem_Icc.mpr ⟨by omega, by omega⟩, h2, h3⟩
    refine le_trans hsub (le_trans (prσ_exists_le β₀ k _ _) ?_)
    have hterm : ∀ j ∈ Icc (i - A) i,
        Prσ β₀ k (fun β => j + K ≤ i + 1 ∧ AllMiss P β₀.length n₁ a j K β) ≤ ρ ^ K := by
      intro j _
      by_cases hj : j + K ≤ i + 1
      · refine le_trans (Prσ_mono β₀ k (fun β _ hβ => hβ.2)) (hchain β₀ k j K ?_)
        exact le_trans (Nat.mul_le_mul_right _ hj) hk
      · rw [prσ_false β₀ k _ (fun β hβ => hj hβ.1)]
        positivity
    calc ∑ j ∈ Icc (i - A) i, Prσ β₀ k (fun β => j + K ≤ i + 1 ∧ AllMiss P β₀.length n₁ a j K β)
        ≤ ∑ j ∈ Icc (i - A) i, ρ ^ K := sum_le_sum hterm
      _ = ((Icc (i - A) i).card : ℚ) * ρ ^ K := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (A + 1) * ρ ^ K := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [Nat.card_Icc]
          have : i + 1 - (i - A) ≤ A + 1 := by omega
          exact_mod_cast this

/-- **`gap_run`** (added after internal review): `gap_chain'` and `run_le` combined. -/
theorem gap_run (P : Word → Prop) (a : ℕ) (η : ℚ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hP : MissFrac P a η) :
    ∃ n₀ : ℕ, ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ ∀ n₁ ≥ n₀, ∀ (β₀ : List Bool) (k i A K : ℕ),
      (i + 1) * (n₁ + a) ≤ k →
      Prσ β₀ k (RunMiss P β₀.length n₁ a i A K) ≤ (A + 1) * (1 - c) ^ K := by
  obtain ⟨n₀, c, hc0, hc1, h⟩ := gap_chain' P a η hη0 hη1 hP
  exact ⟨n₀, c, hc0, hc1, fun n₁ hn₁ β₀ k i A K hk =>
    run_le P a n₁ (1 - c) (by linarith) (h n₁ hn₁) β₀ k i A K hk⟩

/-! ## §6 Expectations per group -/

/-- **Expectation per group**: for weights `w R ≥ 0` and windows `A R`, `K R` for each range `R ∈ S`,
`E[Σ_R w R 1[RunMiss i (A R) (K R)]] ≤ Σ_R w R (A R + 1) ρ^{K R}`. -/
theorem run_expect (P : Word → Prop) (a n₁ : ℕ) (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hchain : ∀ (β₀ : List Bool) (k j K : ℕ), (j + K) * (n₁ + a) ≤ k →
      Prσ β₀ k (AllMiss P β₀.length n₁ a j K) ≤ ρ ^ K)
    (β₀ : List Bool) (k i : ℕ) (hk : (i + 1) * (n₁ + a) ≤ k) (S : Finset ℕ) (w : ℕ → ℚ)
    (hw : ∀ R, 0 ≤ w R) (A K : ℕ → ℕ) :
    ∑ β ∈ blockChoices k, wtβ β * ∑ R ∈ S,
      w R * (if RunMiss P β₀.length n₁ a i (A R) (K R) (β₀ ++ β) then 1 else 0) ≤
      ∑ R ∈ S, w R * ((A R + 1) * ρ ^ K R) := by
  rw [expect_ind β₀ k S w (fun R => RunMiss P β₀.length n₁ a i (A R) (K R))]
  refine sum_le_sum (fun R _ => mul_le_mul_of_nonneg_left ?_ (hw R))
  exact run_le P a n₁ ρ hρ hchain β₀ k i (A R) (K R) hk

/-- Summed over a set `I` of groups: the expectation is at most `|I| Σ_R w R (A R + 1) ρ^{K R}`. -/
theorem run_expect_groups (P : Word → Prop) (a n₁ : ℕ) (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hchain : ∀ (β₀ : List Bool) (k j K : ℕ), (j + K) * (n₁ + a) ≤ k →
      Prσ β₀ k (AllMiss P β₀.length n₁ a j K) ≤ ρ ^ K)
    (β₀ : List Bool) (k : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, (i + 1) * (n₁ + a) ≤ k)
    (S : Finset ℕ) (w : ℕ → ℚ) (hw : ∀ R, 0 ≤ w R) (A K : ℕ → ℕ) :
    ∑ β ∈ blockChoices k, wtβ β * ∑ i ∈ I, ∑ R ∈ S,
      w R * (if RunMiss P β₀.length n₁ a i (A R) (K R) (β₀ ++ β) then 1 else 0) ≤
      I.card * ∑ R ∈ S, w R * ((A R + 1) * ρ ^ K R) := by
  have e : ∑ β ∈ blockChoices k, wtβ β * ∑ i ∈ I, ∑ R ∈ S,
      w R * (if RunMiss P β₀.length n₁ a i (A R) (K R) (β₀ ++ β) then 1 else 0) =
      ∑ i ∈ I, ∑ β ∈ blockChoices k, wtβ β * ∑ R ∈ S,
        w R * (if RunMiss P β₀.length n₁ a i (A R) (K R) (β₀ ++ β) then 1 else 0) := by
    rw [sum_comm]
    refine sum_congr rfl (fun β _ => ?_)
    rw [mul_sum]
  rw [e]
  calc ∑ i ∈ I, ∑ β ∈ blockChoices k, wtβ β * ∑ R ∈ S,
        w R * (if RunMiss P β₀.length n₁ a i (A R) (K R) (β₀ ++ β) then 1 else 0)
      ≤ ∑ i ∈ I, ∑ R ∈ S, w R * ((A R + 1) * ρ ^ K R) :=
        sum_le_sum (fun i hi => run_expect P a n₁ ρ hρ hchain β₀ k i (hI i hi) S w hw A K)
    _ = I.card * ∑ R ∈ S, w R * ((A R + 1) * ρ ^ K R) := by rw [sum_const, nsmul_eq_mul]

end Collatz.Arctic.NatQ5.W3b
