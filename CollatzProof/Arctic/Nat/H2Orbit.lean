/-
# Lemma 11.7: frequencies of aligned segments in the binary expansion of a reduced fraction

Lemma 11.7 in the form `win_freq` used by Theorem 11.8 (**aligned segments**).
(Section 11.2.)

Let `N/D` be in lowest terms with `D = 3^α D''` (`3 ∤ D''`, `D'' ∣ 2^L - 1`), `κ, L ≥ 1` and `c := 1 + v_3(κL)`. For the windows
`x_i := dig N D (κ i) κ` of `κ` digits from position `κ i` of the expansion, and every word `x` of length `κ`,
\[
  \#\{i < n : x_i = x\} \le (n + P)\,(2^{-\kappa} + 3^{c-\alpha}),\qquad P := 2L\cdot 3^{\alpha - c}
\]
(`win_count`); hence `Σ_{i<n} f(x_i) ≤ (n + P)(2^{-κ} + 3^{c-α}) Σ_{|x|=κ} f(x)` for `f ≥ 0` (`win_freq`).

**The form of the proof** (different from an earlier argument): there, "the orbit `S` is a union of residue classes of `3^{c'-a}ℤ/ℤ`" was shown with the Chinese remainder theorem and
the uniqueness of subgroups of `(ℤ/3^a)^×`, and the proportion over one period was counted. Here neither the period nor the Chinese remainder theorem is used.
Since `g := 4^{κL} = 2^{κ·2L}` satisfies `g ≡ 1 (mod 3^c D'')` and `v_3(g - 1) = c` (LTE), on the group of indices `i = i_0 + 2L(Kz + t)`
(`K := 3^{α-c}`, `t < K`) the map `t ↦ 2^{κ i} N mod D = (g^t B) mod D` is injective (`pow_modEq_inj`), and
all values are congruent to `B` modulo `3^c D''`. The points of one class modulo `3^c D''` are spaced `3^c D''` apart, so at most `⌊(K-1)/2^κ⌋ + 1` of them
fall into a window of length `D/2^κ` (`card_ap_window`). The `2L (⌊n/(2LK)⌋ + 1)` groups cover `[0, n)`.
If `c > α` the bound is trivial (`3^{c-α} ≥ 1`). The hypothesis `c ≤ α` is not needed.
-/
import CollatzProof.Arctic.Nat.H2Bin

namespace Collatz.Arctic.NatQ5.W2a

open Collatz.Arctic Collatz.Arctic.NatQ5

/-! ## §1 The number of points of one residue class in a window -/

/-- **The spacing bound**: if `D = K Q_0` (`K, Q_0 ≥ 1`) and all points `r` of `S` satisfy `r ≡ b (mod Q_0)` and `⌊2^κ r/D⌋ = v`, then
`|S| ≤ ⌊(K - 1)/2^κ⌋ + 1`. -/
theorem card_ap_window {D Q0 K κ v b : ℕ} (hD : D = K * Q0) (hQ0 : 0 < Q0) (hK : 0 < K) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r % Q0 = b % Q0 ∧ 2 ^ κ * r / D = v) : S.card ≤ (K - 1) / 2 ^ κ + 1 := by
  rcases S.eq_empty_or_nonempty with hemp | hne
  · simp [hemp]
  have hDpos : 0 < D := by rw [hD]; positivity
  have hP : 0 < 2 ^ κ := by positivity
  set r0 := S.min' hne with hr0
  have hr0S : r0 ∈ S := Finset.min'_mem S hne
  -- A point `r` is `r = r0 + Q0 j` with `2^κ j < K`
  have key : ∀ r ∈ S, ∃ j, r = r0 + Q0 * j ∧ 2 ^ κ * j < K := by
    intro r hr
    have hle : r0 ≤ r := Finset.min'_le S r hr
    obtain ⟨hm, hv⟩ := hS r hr
    obtain ⟨hm0, hv0⟩ := hS r0 hr0S
    have hmod : r0 ≡ r [MOD Q0] := by unfold Nat.ModEq; rw [hm, hm0]
    obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hle).1 hmod
    refine ⟨j, by omega, ?_⟩
    have h1 : 2 ^ κ * r < D * (v + 1) := by
      have := Nat.lt_mul_div_succ (2 ^ κ * r) hDpos; rwa [hv] at this
    have h2 : v * D ≤ 2 ^ κ * r0 := by
      have := Nat.div_mul_le_self (2 ^ κ * r0) D; rwa [hv0] at this
    have hrj : 2 ^ κ * r = 2 ^ κ * r0 + 2 ^ κ * (Q0 * j) := by
      rw [show r = r0 + Q0 * j by omega]; ring
    have h3 : 2 ^ κ * (Q0 * j) < D := by nlinarith
    rw [hD] at h3
    have : (2 ^ κ * j) * Q0 < K * Q0 := by linarith
    exact Nat.lt_of_mul_lt_mul_right this
  calc S.card ≤ (Finset.range ((K - 1) / 2 ^ κ + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun r => (r - r0) / Q0) ?_ ?_
        · intro r hr
          obtain ⟨j, hrj, hjK⟩ := key r (Finset.mem_coe.1 hr)
          refine Finset.mem_coe.2 (Finset.mem_range.2 ?_)
          have : (r - r0) / Q0 = j := by
            rw [show r - r0 = Q0 * j by omega, Nat.mul_div_cancel_left _ hQ0]
          show (r - r0) / Q0 < _
          rw [this, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hP]
          rw [mul_comm]; omega
        · intro r hr r' hr' he
          obtain ⟨j, hrj, _⟩ := key r (Finset.mem_coe.1 hr)
          obtain ⟨j', hrj', _⟩ := key r' (Finset.mem_coe.1 hr')
          simp only at he
          rw [show r - r0 = Q0 * j by omega, show r' - r0 = Q0 * j' by omega,
            Nat.mul_div_cancel_left _ hQ0, Nat.mul_div_cancel_left _ hQ0] at he
          rw [hrj, hrj', he]
    _ = (K - 1) / 2 ^ κ + 1 := Finset.card_range _

/-! ## §2 The count on one group `i = i_0 + 2L(Kz + t)` (`t < K`) -/

/-- The value of the window (the value of the `κ` digits from position `κ i` of the expansion) `⌊2^κ (2^{κ i} N mod D)/D⌋`. -/
def winVal (N D κ i : ℕ) : ℕ := 2 ^ κ * (2 ^ (κ * i) * N % D) / D

/-- For `g := 4^{κL}`, `v_3(g - 1) = 1 + v_3(κL)`. -/
theorem v3_g (κ L : ℕ) (hκ : 1 ≤ κ) (hL : 1 ≤ L) :
    padicValNat 3 (4 ^ (κ * L) - 1) = 1 + padicValNat 3 (κ * L) :=
  v3_four_pow_sub_one (by positivity)

/-- **The count on one group**: if `c := 1 + v_3(κL) ≤ α` and `K := 3^{α-c}`, then for all `i_0, z, v`,
`#{t < K : winVal(i_0 + 2L(Kz + t)) = v} ≤ ⌊(K - 1)/2^κ⌋ + 1`. -/
theorem group_count {N D α D'' L κ c K : ℕ} (hND : N.Coprime D) (hα : D = 3 ^ α * D'') (h3 : ¬ 3 ∣ D'')
    (hL : D'' ∣ 2 ^ L - 1) (hL1 : 1 ≤ L) (hκ : 1 ≤ κ) (hc : c = 1 + padicValNat 3 (κ * L)) (hcα : c ≤ α)
    (hK : K = 3 ^ (α - c)) (i0 z v : ℕ) :
    ((Finset.range K).filter (fun t => winVal N D κ (i0 + 2 * L * (K * z + t)) = v)).card ≤
      (K - 1) / 2 ^ κ + 1 := by
  set g := 4 ^ (κ * L) with hg
  have hg1 : 1 < g := by rw [hg]; exact Nat.one_lt_pow (by positivity) (by norm_num)
  have hgv : padicValNat 3 (g - 1) = c := by rw [hg, hc]; exact v3_g κ L hκ hL1
  have hc1 : 1 ≤ c := by omega
  set B := 2 ^ (κ * (i0 + 2 * L * K * z)) * N with hB
  have hD''pos : 0 < D'' := by
    rcases Nat.eq_zero_or_pos D'' with h0 | h0
    · exfalso; rw [h0] at hL
      have : 2 ≤ 2 ^ L := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
      have := Nat.eq_zero_of_zero_dvd hL; omega
    · exact h0
  set Q0 := 3 ^ c * D'' with hQ0
  have hQ0pos : 0 < Q0 := by rw [hQ0]; positivity
  have hKpos : 0 < K := by rw [hK]; positivity
  have hDKQ : D = K * Q0 := by
    rw [hα, hK, hQ0, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hcα]
  have hDpos : 0 < D := by rw [hDKQ]; positivity
  -- `B` is prime to 3
  have h3D : 3 ∣ D := by rw [hα]; exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
  have hB3 : ¬ 3 ∣ B := by
    rw [hB]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hd with h2 | hN
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
    · have : 3 ∣ Nat.gcd N D := Nat.dvd_gcd hN h3D
      rw [hND] at this; omega
  -- `g ≡ 1 (mod Q0)`
  have hgQ : g ≡ 1 [MOD Q0] := by
    have h1 : 3 ^ c ∣ g - 1 := hgv ▸ pow_padicValNat_dvd
    have h2 : D'' ∣ g - 1 := by
      have : g = (2 ^ L) ^ (2 * κ) := by
        rw [hg, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
      rw [this]
      exact hL.trans (Nat.sub_one_dvd_pow_sub_one _ _)
    have hcop : Nat.Coprime (3 ^ c) D'' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
    exact ((Nat.modEq_iff_dvd' hg1.le).2 (hcop.mul_dvd_of_dvd_of_dvd h1 h2)).symm
  -- Decomposing the exponent of the index
  have hexp : ∀ t, 2 ^ (κ * (i0 + 2 * L * (K * z + t))) * N = g ^ t * B := by
    intro t
    have e : κ * (i0 + 2 * L * (K * z + t)) = κ * (i0 + 2 * L * K * z) + 2 * (κ * L * t) := by ring
    have h4 : (2 : ℕ) ^ (2 * (κ * L * t)) = g ^ t := by
      rw [pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, hg, ← pow_mul]
    rw [e, pow_add, h4, hB]
    ring
  set F := (Finset.range K).filter (fun t => winVal N D κ (i0 + 2 * L * (K * z + t)) = v) with hF
  let φ : ℕ → ℕ := fun t => g ^ t * B % D
  have hinj : Set.InjOn φ F := by
    intro t ht t' ht' he
    have ht1 := (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).1
    have ht1' := (Finset.mem_filter.1 (Finset.mem_coe.1 ht')).1
    rw [Finset.mem_range] at ht1 ht1'
    have hmD : g ^ t * B ≡ g ^ t' * B [MOD D] := he
    have h3α : 3 ^ (c + (α - c)) ∣ D := by
      rw [Nat.add_sub_cancel' hcα, hα]; exact Dvd.intro _ rfl
    have hm3 := Nat.ModEq.of_dvd h3α hmD
    rw [hK] at ht1 ht1'
    exact pow_modEq_inj hg1 hgv hc1 hB3 ht1 ht1' hm3
  have hcardF : F.card = (F.image φ).card := (Finset.card_image_of_injOn hinj).symm
  rw [hcardF]
  refine card_ap_window (b := B) (v := v) hDKQ hQ0pos hKpos _ ?_
  intro r hr
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hr
  have htv := (Finset.mem_filter.1 ht).2
  refine ⟨?_, ?_⟩
  · have hQD : Q0 ∣ D := by rw [hDKQ]; exact Dvd.intro_left _ rfl
    show g ^ t * B % D % Q0 = B % Q0
    rw [Nat.mod_mod_of_dvd _ hQD]
    have : g ^ t * B ≡ 1 ^ t * B [MOD Q0] := (hgQ.pow t).mul_right B
    rw [one_pow, one_mul] at this
    exact this
  · unfold winVal at htv
    rw [hexp t] at htv
    exact htv

/-! ## §3 Covering `[0, n)` by groups -/

/-- **The count as a natural number**: if `c ≤ α`, then
`#{i < n : winVal(i) = v} ≤ 2L (⌊n/(2LK)⌋ + 1)(⌊(K-1)/2^κ⌋ + 1)` (`K = 3^{α-c}`). -/
theorem win_count_nat {N D α D'' L κ c K : ℕ} (hND : N.Coprime D) (hα : D = 3 ^ α * D'') (h3 : ¬ 3 ∣ D'')
    (hL : D'' ∣ 2 ^ L - 1) (hL1 : 1 ≤ L) (hκ : 1 ≤ κ) (hc : c = 1 + padicValNat 3 (κ * L)) (hcα : c ≤ α)
    (hK : K = 3 ^ (α - c)) (n v : ℕ) :
    ((Finset.range n).filter (fun i => winVal N D κ i = v)).card ≤
      2 * L * (n / (2 * L * K) + 1) * ((K - 1) / 2 ^ κ + 1) := by
  have hKpos : 0 < K := by rw [hK]; positivity
  have h2L : 0 < 2 * L := by omega
  set Z := n / (2 * L * K) + 1 with hZ
  let G : ℕ × ℕ → Finset ℕ := fun x =>
    ((Finset.range K).filter (fun t => winVal N D κ (x.1 + 2 * L * (K * x.2 + t)) = v)).image
      (fun t => x.1 + 2 * L * (K * x.2 + t))
  have hsub : (Finset.range n).filter (fun i => winVal N D κ i = v) ⊆
      (Finset.range (2 * L) ×ˢ Finset.range Z).biUnion G := by
    intro i hi
    obtain ⟨hin, hiv⟩ := Finset.mem_filter.1 hi
    rw [Finset.mem_range] at hin
    rw [Finset.mem_biUnion]
    set i0 := i % (2 * L)
    set j := i / (2 * L)
    have hi_dec : i0 + 2 * L * j = i := Nat.mod_add_div i (2 * L)
    have hj_dec : K * (j / K) + j % K = j := Nat.div_add_mod j K
    refine ⟨(i0, j / K), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      refine ⟨Nat.mod_lt _ h2L, ?_⟩
      have : j / K ≤ n / (2 * L * K) := by
        rw [Nat.div_div_eq_div_mul]
        exact Nat.div_le_div_right hin.le
      omega
    · refine Finset.mem_image.2 ⟨j % K, ?_, ?_⟩
      · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hKpos), ?_⟩
        simp only
        rw [hj_dec, hi_dec]; exact hiv
      · simp only
        rw [hj_dec, hi_dec]
  calc ((Finset.range n).filter (fun i => winVal N D κ i = v)).card
      ≤ ((Finset.range (2 * L) ×ˢ Finset.range Z).biUnion G).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ Finset.range (2 * L) ×ˢ Finset.range Z, (G x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Finset.range (2 * L) ×ˢ Finset.range Z, ((K - 1) / 2 ^ κ + 1) := by
        refine Finset.sum_le_sum fun x _ => ?_
        exact (Finset.card_image_le).trans (group_count hND hα h3 hL hL1 hκ hc hcα hK x.1 x.2 v)
    _ = 2 * L * Z * ((K - 1) / 2 ^ κ + 1) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range, smul_eq_mul]

/-- `(3 : ℝ)^{(c:ℤ) - α} = 1/3^{α - c}` (`c ≤ α`). -/
theorem zpow_three_sub {c α : ℕ} (h : c ≤ α) : (3 : ℝ) ^ ((c : ℤ) - α) = ((3 : ℝ) ^ (α - c))⁻¹ := by
  rw [show ((c : ℤ) - α) = -((α - c : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring, zpow_neg, zpow_natCast]

/-- A sum over the words of length `|z|` that picks out `z` only. -/
theorem wsum_single (z : List (Fin 2)) (F : List (Fin 2) → ℝ) :
    Rigid.wsum z.length (fun x => if x = z then F x else 0) = F z := by
  have : (fun x => if x = z then F x else 0) = fun x => F z * (if x = z then (1 : ℝ) else 0) := by
    funext x; split_ifs with h
    · subst h; ring
    · ring
  rw [this, Rigid.wsum_mul_left, Rigid.wsum_indicator, mul_one]

/-- Exchanging `wsum` and a finite sum. -/
theorem wsum_finset_sum {ι : Type*} (s : Finset ι) (n : ℕ) (F : ι → List (Fin 2) → ℝ) :
    Rigid.wsum n (fun w => ∑ i ∈ s, F i w) = ∑ i ∈ s, Rigid.wsum n (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Rigid.wsum_const, mul_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Rigid.wsum_add, ih]

end Collatz.Arctic.NatQ5.W2a

namespace Collatz.Arctic.NatQ5

open Collatz.Arctic W2a

/-! ## §4 The frequency bound (main theorem) -/

/-- **Lemma 11.7, the counting form**: if `N/D` is in lowest terms, `D = 3^α D''` (`3 ∤ D''`, `D'' ∣ 2^L - 1`), `κ, L ≥ 1`,
`c := 1 + v_3(κL)` and `P := 2L·3^{α-c}`, then for all `n, v`,
`#{i < n : ⌊2^κ (2^{κ i} N mod D)/D⌋ = v} ≤ (n + P)(2^{-κ} + 3^{c-α})`. -/
theorem win_count {N D α D'' L κ : ℕ} (hND : N.Coprime D) (hα : D = 3 ^ α * D'') (h3 : ¬ 3 ∣ D'')
    (hL : D'' ∣ 2 ^ L - 1) (hL1 : 1 ≤ L) (hκ : 1 ≤ κ) (n v : ℕ) :
    (((Finset.range n).filter (fun i => winVal N D κ i = v)).card : ℝ) ≤
      ((n : ℝ) + 2 * L * 3 ^ (α - (1 + padicValNat 3 (κ * L)))) *
        (((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (((1 + padicValNat 3 (κ * L) : ℕ) : ℤ) - α)) := by
  set c := 1 + padicValNat 3 (κ * L) with hc
  have h2κ : (0 : ℝ) < 2 ^ κ := by positivity
  rcases Nat.lt_or_ge α c with hlt | hcα
  · -- The trivial case: `3^{c-α} ≥ 1`
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((c : ℤ) - α) := one_le_zpow₀ (by norm_num) (by omega)
    have hcard : (((Finset.range n).filter (fun i => winVal N D κ i = v)).card : ℝ) ≤ n := by
      have := Finset.card_filter_le (Finset.range n) (fun i => winVal N D κ i = v)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hP : (0 : ℝ) ≤ 2 * L * 3 ^ (α - c) := by positivity
    have hinv : (0 : ℝ) ≤ ((2 : ℝ) ^ κ)⁻¹ := by positivity
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith
  · set K := 3 ^ (α - c) with hK
    have hKpos : 0 < K := by positivity
    have hnat := win_count_nat hND hα h3 hL hL1 hκ hc hcα hK n v
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
    rw [zpow_three_sub hcα]
    have hcast : (((Finset.range n).filter (fun i => winVal N D κ i = v)).card : ℝ) ≤
        (2 * L : ℝ) * (((n / (2 * L * K) : ℕ) : ℝ) + 1) * ((((K - 1) / 2 ^ κ : ℕ) : ℝ) + 1) := by
      exact_mod_cast hnat
    have hd1 : (((n / (2 * L * K) : ℕ) : ℝ)) ≤ (n : ℝ) / (2 * L * K) := by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := 2 * L * K)
      simpa using this
    have hd2 : ((((K - 1) / 2 ^ κ : ℕ) : ℝ)) ≤ (K : ℝ) / 2 ^ κ := by
      have h := Nat.cast_div_le (α := ℝ) (m := K - 1) (n := 2 ^ κ)
      have h' : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
      push_cast at h
      calc ((((K - 1) / 2 ^ κ : ℕ) : ℝ)) ≤ ((K - 1 : ℕ) : ℝ) / 2 ^ κ := by exact_mod_cast h
        _ ≤ (K : ℝ) / 2 ^ κ := by gcongr
    have hA : (0 : ℝ) ≤ (((n / (2 * L * K) : ℕ) : ℝ)) + 1 := by positivity
    have hB : (0 : ℝ) ≤ ((((K - 1) / 2 ^ κ : ℕ) : ℝ)) + 1 := by positivity
    calc _ ≤ (2 * L : ℝ) * (((n / (2 * L * K) : ℕ) : ℝ) + 1) * ((((K - 1) / 2 ^ κ : ℕ) : ℝ) + 1) := hcast
      _ ≤ (2 * L : ℝ) * ((n : ℝ) / (2 * L * K) + 1) * ((K : ℝ) / 2 ^ κ + 1) := by
          gcongr
      _ = ((n : ℝ) + 2 * L * K) * (((2 : ℝ) ^ κ)⁻¹ + ((K : ℕ) : ℝ)⁻¹) := by
          field_simp
      _ = _ := by simp only [hK, Nat.cast_pow, Nat.cast_ofNat]

/-- **Lemma 11.7** (aligned segments): under the hypotheses above, for `f ≥ 0` on the words of length `κ`,
\[
  \sum_{i<n} f(\mathrm{dig}\,N\,D\,(\kappa i)\,\kappa) \le (n + P)(2^{-\kappa} + 3^{c-\alpha}) \sum_{\lvert x\rvert = \kappa} f(x),
  \qquad P = 2L\cdot 3^{\alpha-c},\ c = 1 + v_3(\kappa L) .
\]
`Σ_{|x|=κ}` is `Rigid.wsum κ f` of Appendix D (`2^κ bAvg_κ` for `f = log⁺‖D_x‖`). -/
theorem win_freq {N D α D'' L κ : ℕ} (hND : N.Coprime D) (hα : D = 3 ^ α * D'') (h3 : ¬ 3 ∣ D'')
    (hL : D'' ∣ 2 ^ L - 1) (hL1 : 1 ≤ L) (hκ : 1 ≤ κ) (f : List (Fin 2) → ℝ)
    (hf : ∀ x : List (Fin 2), x.length = κ → 0 ≤ f x) (n : ℕ) :
    ∑ i ∈ Finset.range n, f (dig N D (κ * i) κ) ≤
      ((n : ℝ) + 2 * L * 3 ^ (α - (1 + padicValNat 3 (κ * L)))) *
        (((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (((1 + padicValNat 3 (κ * L) : ℕ) : ℤ) - α)) * Rigid.wsum κ f := by
  set Bnd := ((n : ℝ) + 2 * L * 3 ^ (α - (1 + padicValNat 3 (κ * L)))) *
        (((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (((1 + padicValNat 3 (κ * L) : ℕ) : ℤ) - α)) with hBnd
  have hD : 0 < D := by
    rw [hα]
    have : 0 < D'' := by
      rcases Nat.eq_zero_or_pos D'' with h0 | h0
      · exfalso; rw [h0] at hL
        have : 2 ≤ 2 ^ L := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
        have := Nat.eq_zero_of_zero_dvd hL; omega
      · exact h0
    positivity
  set x : ℕ → List (Fin 2) := fun i => dig N D (κ * i) κ with hx
  have hxlen : ∀ i, (x i).length = κ := fun i => dig_length _ _ _ _
  -- The count as a sum
  have hsum : ∑ i ∈ Finset.range n, f (x i) =
      Rigid.wsum κ (fun y => f y * (((Finset.range n).filter (fun i => x i = y)).card : ℝ)) := by
    have h1 : ∀ i, f (x i) = Rigid.wsum κ (fun y => if y = x i then f y else 0) := by
      intro i
      have := wsum_single (x i) f
      rw [hxlen i] at this
      exact this.symm
    rw [Finset.sum_congr rfl (fun i _ => h1 i), ← wsum_finset_sum]
    refine Rigid.wsum_congr fun y _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm,
      Finset.filter_congr (fun i _ => @eq_comm _ y (x i))]
  rw [hsum]
  -- An upper bound on the count of each word
  have hcnt : ∀ y : List (Fin 2), y.length = κ →
      (((Finset.range n).filter (fun i => x i = y)).card : ℝ) ≤ Bnd := by
    intro y hy
    have hsub : (Finset.range n).filter (fun i => x i = y) ⊆
        (Finset.range n).filter (fun i => winVal N D κ i = valW 0 y) := by
      intro i hi
      obtain ⟨hin, hxy⟩ := Finset.mem_filter.1 hi
      refine Finset.mem_filter.2 ⟨hin, ?_⟩
      have hlt : winVal N D κ i < 2 ^ κ := two_pow_mul_mod_div_lt κ _ D hD
      have : dig N D (κ * i) κ = bitsF κ (winVal N D κ i) := rfl
      rw [← hxy, hx]
      simp only
      rw [this, valW_bitsF κ _ hlt]
    calc (((Finset.range n).filter (fun i => x i = y)).card : ℝ)
        ≤ (((Finset.range n).filter (fun i => winVal N D κ i = valW 0 y)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ Bnd := win_count hND hα h3 hL hL1 hκ n (valW 0 y)
  calc Rigid.wsum κ (fun y => f y * (((Finset.range n).filter (fun i => x i = y)).card : ℝ))
      ≤ Rigid.wsum κ (fun y => Bnd * f y) := by
        refine Rigid.wsum_mono fun y hy => ?_
        rw [mul_comm Bnd]
        exact mul_le_mul_of_nonneg_left (hcnt y hy) (hf y hy)
    _ = Bnd * Rigid.wsum κ f := Rigid.wsum_mul_left κ Bnd f

/-- The form with `∃ P ≥ 1`. -/
theorem win_freq_exists {N D α D'' L κ : ℕ} (hND : N.Coprime D) (hα : D = 3 ^ α * D'') (h3 : ¬ 3 ∣ D'')
    (hL : D'' ∣ 2 ^ L - 1) (hL1 : 1 ≤ L) (hκ : 1 ≤ κ) (f : List (Fin 2) → ℝ)
    (hf : ∀ x : List (Fin 2), x.length = κ → 0 ≤ f x) :
    ∃ P : ℕ, 1 ≤ P ∧ ∀ n : ℕ, ∑ i ∈ Finset.range n, f (dig N D (κ * i) κ) ≤
      ((n : ℝ) + P) * (((2 : ℝ) ^ κ)⁻¹ + (3 : ℝ) ^ (((1 + padicValNat 3 (κ * L) : ℕ) : ℤ) - α)) *
        Rigid.wsum κ f := by
  refine ⟨2 * L * 3 ^ (α - (1 + padicValNat 3 (κ * L))), ?_, fun n => ?_⟩
  · have : 1 ≤ 3 ^ (α - (1 + padicValNat 3 (κ * L))) := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  · have := win_freq hND hα h3 hL hL1 hκ f hf n
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact this

end Collatz.Arctic.NatQ5
