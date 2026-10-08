/-
# Section 11.2: words and numbers, and facts on powers of 3

Arithmetic preparation independent of interpretations (Section 11.2),
used by the backward chains (`H2Chain.lean`, Lemma 11.5) and the frequencies of aligned segments
(`H2Orbit.lean`, Lemma 11.7).

* **Binary representations of fixed length** (§1): `bitsF m x` (the `m` digits of `x < 2^m`, most significant first). `valW 0 (bitsF m x) = x`
  (`valW_bitsF`) and `bitsF |w| (valW 0 w) = w` (`bitsF_valW`).
* **`binWord` and `valW`** (§2): `binWord (valW 1 w) = w` (`binWord_valW`), the bounds on the length
  `2^{|bin'(n)|} ≤ n < 2^{|bin'(n)|+1}` (`binWord_length_bounds`), and **the splitting of a word into three parts**
  `bin'(U 2^{h+ℓ} + Θ 2^h + V) = bin'(U) ++ bitsF ℓ Θ ++ bitsF h V` (`binWord_split`).
* **Cutting out windows** (§3): `dig N D p k` (the `k` digits of the binary expansion of `N/D` from position `p`, that is, the first `k` digits of
  `2^p N/D mod 1`). `dig_add`, the decomposition into aligned segments `dig_blocks`, and `bitsF ℓ ⌊2^ℓ N/D⌋ = dig N D 0 ℓ` (`bitsF_floor`).
* **Facts on powers of 3** (§4, Mathlib only): `v_3(4^o - 1) = 1 + v_3(o)` (`v3_four_pow_sub_one`, the lifting of the exponent
  `padicValNat.pow_sub_pow`); if `v_3(g - 1) = c ≥ 1`, then `t ↦ g^t y mod 3^{c+k}` is injective on `t < 3^k` (`pow_modEq_inj`) and
  covers the class `y + 3^c ℤ` (`pow_cover`); existence of `e < 2·3^k` with `3^{k+1} ∣ 2^e y + 1` (`exists_two_pow_mul_add_one_dvd`);
  `ord_{3^t} 2 = 2·3^{t-1}` (`three_pow_dvd_two_pow_sub_one_iff`, `orderOf_two_three_pow`).

Auxiliary declarations are in the namespace `Collatz.Arctic.NatQ5.W2a`. `sorry`, `axiom` and `native_decide` are not used.
-/
import CollatzProof.Arctic.Nat.Lift

namespace Collatz.Arctic.NatQ5.W2a

open Collatz.Arctic Collatz.Arctic.NatQ5

/-! ## §1 Binary representations of fixed length -/

/-- The `m`-digit binary representation of `x` (most significant first; `valW 0 (bitsF m x) = x` if `x < 2^m`). -/
def bitsF : ℕ → ℕ → List (Fin 2)
  | 0, _ => []
  | m + 1, x => ⟨x / 2 ^ m % 2, Nat.mod_lt _ two_pos⟩ :: bitsF m (x % 2 ^ m)

@[simp] theorem bitsF_length (m x : ℕ) : (bitsF m x).length = m := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => simp [bitsF, ih]

theorem valW_append (r : ℕ) (u v : List (Fin 2)) : valW r (u ++ v) = valW (valW r u) v := by
  induction u generalizing r with
  | nil => rfl
  | cons b u ih => simp only [List.cons_append, valW]; exact ih _

theorem valW_cons (r : ℕ) (b : Fin 2) (w : List (Fin 2)) : valW r (b :: w) = valW (2 * r + b) w := rfl

theorem valW_lt (w : List (Fin 2)) : valW 0 w < 2 ^ w.length := by
  induction w with
  | nil => simp [valW]
  | cons b w ih =>
    rw [valW_cons, valW_eq, List.length_cons, pow_succ]
    have hb : ((b : ℕ)) ≤ 1 := Nat.le_of_lt_succ b.isLt
    have : (2 * 0 + (b : ℕ)) * 2 ^ w.length ≤ 1 * 2 ^ w.length := Nat.mul_le_mul_right _ (by omega)
    omega

/-- `valW 1 w = 2^{|w|} + valW 0 w`. -/
theorem valW_one (w : List (Fin 2)) : valW 1 w = 2 ^ w.length + valW 0 w := by
  rw [valW_eq, one_mul]

theorem valW_bitsF (m x : ℕ) (hx : x < 2 ^ m) : valW 0 (bitsF m x) = x := by
  induction m generalizing x with
  | zero => simp at hx; subst hx; rfl
  | succ m ih =>
    simp only [bitsF]
    rw [valW_cons, valW_eq, bitsF_length, ih _ (Nat.mod_lt _ (by positivity))]
    have hq : x / 2 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hx; omega
    have h1 : x / 2 ^ m % 2 = x / 2 ^ m := Nat.mod_eq_of_lt hq
    simp only [mul_zero, zero_add, h1]
    rw [mul_comm]
    exact Nat.div_add_mod x (2 ^ m)

theorem bitsF_valW (w : List (Fin 2)) : bitsF w.length (valW 0 w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.length_cons]
    simp only [bitsF]
    have hv : valW 0 (b :: w) = (b : ℕ) * 2 ^ w.length + valW 0 w := by
      rw [valW_cons, valW_eq]; simp
    have hlt := valW_lt w
    have hpos : 0 < 2 ^ w.length := by positivity
    have hdiv : valW 0 (b :: w) / 2 ^ w.length = b := by
      rw [hv, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]
    have hmod : valW 0 (b :: w) % 2 ^ w.length = valW 0 w := by
      rw [hv, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    rw [hmod, ih]
    congr 1
    exact Fin.ext (by simp only [hdiv]; exact Nat.mod_eq_of_lt b.isLt)

/-- Two representations of fixed length side by side. -/
theorem bitsF_add (a b x y : ℕ) (hx : x < 2 ^ a) (hy : y < 2 ^ b) :
    bitsF (a + b) (x * 2 ^ b + y) = bitsF a x ++ bitsF b y := by
  have hlen : (bitsF a x ++ bitsF b y).length = a + b := by simp
  have hval : valW 0 (bitsF a x ++ bitsF b y) = x * 2 ^ b + y := by
    rw [valW_append, valW_eq, valW_bitsF a x hx, bitsF_length, valW_bitsF b y hy]
  have := bitsF_valW (bitsF a x ++ bitsF b y)
  rwa [hlen, hval] at this

/-- The representation of fixed length is injective (`x, y < 2^m`). -/
theorem bitsF_inj {m x y : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ m) (h : bitsF m x = bitsF m y) : x = y := by
  rw [← valW_bitsF m x hx, ← valW_bitsF m y hy, h]

/-! ## §2 `binWord` and `valW` -/

/-- Bounds on the length of `bin'(n)` for `n ≥ 1`: `2^{|bin'(n)|} ≤ n < 2^{|bin'(n)|+1}`. -/
theorem binWord_length_bounds (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (binWord n).length ≤ n ∧ n < 2 ^ ((binWord n).length + 1) := by
  have h := valW_binWord n hn
  rw [valW_one] at h
  have hlt := valW_lt (binWord n)
  rw [pow_succ]
  omega

/-- **`binWord (valW 1 w) = w`**: `bin'` of the value of a word with a leading 1 is the word itself. -/
theorem binWord_valW (w : List (Fin 2)) : binWord (valW 1 w) = w := by
  set n := valW 1 w with hn
  have hn1 : 1 ≤ n := by rw [hn, valW_one]; have := Nat.one_le_two_pow (n := w.length); omega
  obtain ⟨hlo, hhi⟩ := binWord_length_bounds n hn1
  have hnw : n = 2 ^ w.length + valW 0 w := by rw [hn, valW_one]
  have hltw := valW_lt w
  -- The lengths agree
  have hlen : (binWord n).length = w.length := by
    rcases lt_trichotomy (binWord n).length w.length with h | h | h
    · exfalso
      have : 2 ^ ((binWord n).length + 1) ≤ 2 ^ w.length := Nat.pow_le_pow_right (by norm_num) h
      omega
    · exact h
    · exfalso
      have : 2 ^ (w.length + 1) ≤ 2 ^ (binWord n).length := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ] at this
      omega
  have hv := valW_binWord n hn1
  rw [valW_one, hlen] at hv
  have hv0 : valW 0 (binWord n) = valW 0 w := by omega
  have := bitsF_valW (binWord n)
  rw [hlen, hv0, bitsF_valW] at this
  exact this.symm

/-- `2^{|x|} ≤ valW 1 x`. -/
theorem two_pow_le_valW_one (x : List (Fin 2)) : 2 ^ x.length ≤ valW 1 x := by
  rw [valW_one]; omega

/-- **Splitting a word into three parts**: if `U ≥ 1`, `Θ < 2^ℓ` and `V < 2^h`, then
`bin'(U 2^{h+ℓ} + Θ 2^h + V) = bin'(U) ++ bitsF ℓ Θ ++ bitsF h V`. -/
theorem binWord_split (U Θ V h ℓ : ℕ) (hU : 1 ≤ U) (hΘ : Θ < 2 ^ ℓ) (hV : V < 2 ^ h) :
    binWord (U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V) = binWord U ++ bitsF ℓ Θ ++ bitsF h V := by
  have hval : valW 1 (binWord U ++ bitsF ℓ Θ ++ bitsF h V) = U * 2 ^ (h + ℓ) + Θ * 2 ^ h + V := by
    rw [valW_append, valW_append, valW_binWord U hU, valW_eq (valW U _), valW_eq U, bitsF_length,
      bitsF_length, valW_bitsF ℓ Θ hΘ, valW_bitsF h V hV, pow_add]
    ring
  rw [← hval, binWord_valW]

/-! ## §3 Cutting out windows -/

/-- The `k` digits of the binary expansion of `N/D` from position `p`: the first `k` digits of `2^p N/D mod 1`
(the window of length `κ` at position `p` is `dig N D p κ`). -/
def dig (N D p k : ℕ) : List (Fin 2) := bitsF k (2 ^ k * (2 ^ p * N % D) / D)

@[simp] theorem dig_length (N D p k : ℕ) : (dig N D p k).length = k := bitsF_length _ _

/-- `2^k (r mod D)/D < 2^k`. -/
theorem two_pow_mul_mod_div_lt (k a D : ℕ) (hD : 0 < D) : 2 ^ k * (a % D) / D < 2 ^ k := by
  rw [Nat.div_lt_iff_lt_mul hD]
  exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hD) (by positivity)

theorem dig_add (N D p a b : ℕ) (hD : 0 < D) :
    dig N D p (a + b) = dig N D p a ++ dig N D (p + a) b := by
  unfold dig
  set r := 2 ^ p * N % D with hr
  have hrD : r < D := Nat.mod_lt _ hD
  set q := 2 ^ a * r / D with hq
  set r' := 2 ^ a * r % D with hr'
  have hqa : q < 2 ^ a := by
    rw [hq, Nat.div_lt_iff_lt_mul hD]; exact Nat.mul_lt_mul_of_pos_left hrD (by positivity)
  have hr'D : r' < D := Nat.mod_lt _ hD
  have hsplit : 2 ^ a * r = D * q + r' := (Nat.div_add_mod _ _).symm
  have hmain : 2 ^ (a + b) * r / D = q * 2 ^ b + 2 ^ b * r' / D := by
    have : 2 ^ (a + b) * r = D * (q * 2 ^ b) + 2 ^ b * r' := by
      rw [pow_add, mul_comm (2 ^ a) (2 ^ b), mul_assoc, hsplit]; ring
    rw [this, Nat.mul_add_div hD]
  have hlast : 2 ^ (p + a) * N % D = r' := by
    rw [hr', hr, Nat.mul_mod_mod, pow_add]
    ring_nf
  have hy : 2 ^ b * r' / D < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul hD]; exact Nat.mul_lt_mul_of_pos_left hr'D (by positivity)
  rw [hmain, bitsF_add a b q _ hqa hy, hlast]

/-- **Decomposition into aligned segments**: the `κ q + r` digits from position `p` are `q` windows of length `κ` and a rest of length `r`. -/
theorem dig_blocks (N D p κ q r : ℕ) (hD : 0 < D) :
    dig N D p (κ * q + r) =
      ((List.range q).map (fun i => dig N D (p + κ * i) κ)).flatten ++ dig N D (p + κ * q) r := by
  induction q generalizing r with
  | zero => simp
  | succ q ih =>
    have e : κ * (q + 1) + r = κ * q + (κ + r) := by ring
    rw [e, ih, dig_add N D (p + κ * q) κ r hD, List.range_succ, List.map_append, List.flatten_append,
      List.map_singleton, List.flatten_singleton, List.append_assoc]
    congr 3
    ring

/-- The decomposition from position 0 (the form of the windows `dig N D (κ i) κ` in `win_freq`). -/
theorem dig_zero_blocks (N D κ q r : ℕ) (hD : 0 < D) :
    dig N D 0 (κ * q + r) =
      ((List.range q).map (fun i => dig N D (κ * i) κ)).flatten ++ dig N D (κ * q) r := by
  have := dig_blocks N D 0 κ q r hD
  simpa using this

/-- If `N < D`, then `bitsF ℓ ⌊2^ℓ N/D⌋` is the `ℓ` digits from position 0. -/
theorem bitsF_floor (N D ℓ : ℕ) (hND : N < D) : bitsF ℓ (2 ^ ℓ * N / D) = dig N D 0 ℓ := by
  unfold dig
  rw [pow_zero, one_mul, Nat.mod_eq_of_lt hND]

/-! ## §4 Facts on powers of 3 (Mathlib only) -/

theorem not_three_dvd_of_three_dvd_sub_one {g : ℕ} (hg : 1 ≤ g) (h : 3 ∣ g - 1) : ¬ 3 ∣ g := by
  omega

/-- The lifting of the exponent (LTE): if `3 ∣ g - 1`, then `v_3(g^s - 1) = v_3(g - 1) + v_3(s)` (`s ≠ 0`). -/
theorem v3_pow_sub_one {g : ℕ} (hg : 1 < g) (h3 : 3 ∣ g - 1) {s : ℕ} (hs : s ≠ 0) :
    padicValNat 3 (g ^ s - 1) = padicValNat 3 (g - 1) + padicValNat 3 s := by
  have := padicValNat.pow_sub_pow (p := 3) (x := g) (y := 1) (by decide) hg (by simpa using h3)
    (not_three_dvd_of_three_dvd_sub_one hg.le h3) hs
  simpa using this

/-- **`v_3(4^o - 1) = 1 + v_3(o)`** (`o ≠ 0`). -/
theorem v3_four_pow_sub_one {o : ℕ} (ho : o ≠ 0) : padicValNat 3 (4 ^ o - 1) = 1 + padicValNat 3 o := by
  rw [v3_pow_sub_one (by norm_num) (by norm_num) ho]
  norm_num

theorem modEq_one_of_v3 {g c : ℕ} (hg : 1 ≤ g) (hc : padicValNat 3 (g - 1) = c) : g ≡ 1 [MOD 3 ^ c] := by
  have h : 3 ^ c ∣ g - 1 := hc ▸ pow_padicValNat_dvd
  exact ((Nat.modEq_iff_dvd' hg).2 h).symm

/-- **Injectivity**: if `v_3(g - 1) = c ≥ 1` and `3 ∤ y`, then `t ↦ g^t y mod 3^{c+k}` is injective on `t < 3^k`. -/
theorem pow_modEq_inj {g c k y : ℕ} (hg : 1 < g) (hc : padicValNat 3 (g - 1) = c) (hc1 : 1 ≤ c)
    (hy : ¬ 3 ∣ y) {t t' : ℕ} (ht : t < 3 ^ k) (ht' : t' < 3 ^ k)
    (h : g ^ t * y ≡ g ^ t' * y [MOD 3 ^ (c + k)]) : t = t' := by
  have h3 : 3 ∣ g - 1 := by
    have : 3 ^ c ∣ g - 1 := hc ▸ pow_padicValNat_dvd
    exact (dvd_pow_self 3 (by omega)).trans this
  have hg3 : ¬ 3 ∣ g := not_three_dvd_of_three_dvd_sub_one hg.le h3
  have hcopy : Nat.Coprime (3 ^ (c + k)) y :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hy)
  have h' : g ^ t ≡ g ^ t' [MOD 3 ^ (c + k)] := Nat.ModEq.cancel_right_of_coprime hcopy h
  -- The difference from the smaller to the larger
  have key : ∀ {a b : ℕ}, a < b → b < 3 ^ k → ¬ g ^ a ≡ g ^ b [MOD 3 ^ (c + k)] := by
    intro a b hab hb hm
    set s := b - a with hs
    have hs0 : s ≠ 0 := by omega
    have hb' : b = a + s := by omega
    have hm2 : g ^ a * 1 ≡ g ^ a * g ^ s [MOD 3 ^ (c + k)] := by
      rw [mul_one, ← pow_add, ← hb']; exact hm
    have hcopg : Nat.Coprime (3 ^ (c + k)) (g ^ a) :=
      Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hg3)
    have hm' : 1 ≡ g ^ s [MOD 3 ^ (c + k)] := by
      exact Nat.ModEq.cancel_left_of_coprime hcopg hm2
    have hgs : 1 ≤ g ^ s := Nat.one_le_pow _ _ (by omega)
    have hdvd : 3 ^ (c + k) ∣ g ^ s - 1 := (Nat.modEq_iff_dvd' hgs).1 hm'
    have hgs1 : g ^ s - 1 ≠ 0 := by
      have : g ≤ g ^ s := Nat.le_self_pow hs0 g
      omega
    have hle := (padicValNat_dvd_iff_le hgs1).1 hdvd
    rw [v3_pow_sub_one hg h3 hs0, hc] at hle
    have hk : 3 ^ k ∣ s := (padicValNat_dvd_iff_le hs0).2 (by omega)
    have := Nat.le_of_dvd (by omega) hk
    omega
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h' (key hlt ht')
  · exact heq
  · exact absurd h'.symm (key hgt ht)

/-- **Covering**: if `v_3(g - 1) = c ≥ 1` and `3 ∤ y`, then for every `x ≡ y (mod 3^c)` there is `t < 3^k` with
`g^t y ≡ x (mod 3^{c+k})`. For `y = 1`: "the powers of `g` cover `1 + 3^c ℤ` modulo `3^{c+k}`". -/
theorem pow_cover {g c : ℕ} (hg : 1 < g) (hc : padicValNat 3 (g - 1) = c) (hc1 : 1 ≤ c) (k : ℕ)
    {y : ℕ} (hy : ¬ 3 ∣ y) {x : ℕ} (hx : x ≡ y [MOD 3 ^ c]) :
    ∃ t < 3 ^ k, g ^ t * y ≡ x [MOD 3 ^ (c + k)] := by
  have hpos : 0 < 3 ^ (c + k) := by positivity
  have hpc : 0 < 3 ^ c := by positivity
  have hcdvd : 3 ^ c ∣ 3 ^ (c + k) := pow_dvd_pow 3 (Nat.le_add_right c k)
  have hg1 := modEq_one_of_v3 hg.le hc
  set tgt : Finset ℕ := (Finset.range (3 ^ (c + k))).filter (fun z => z % 3 ^ c = y % 3 ^ c) with htgt
  let f : (t : ℕ) → t ∈ Finset.range (3 ^ k) → ℕ := fun t _ => g ^ t * y % 3 ^ (c + k)
  have hmaps : ∀ t (ht : t ∈ Finset.range (3 ^ k)), f t ht ∈ tgt := by
    intro t _
    simp only [htgt, Finset.mem_filter, Finset.mem_range, f]
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    rw [Nat.mod_mod_of_dvd _ hcdvd]
    have : g ^ t * y ≡ 1 ^ t * y [MOD 3 ^ c] := (hg1.pow t).mul_right y
    rw [one_pow, one_mul] at this
    exact this
  have hinj : ∀ t₁ t₂ (h₁ : t₁ ∈ Finset.range (3 ^ k)) (h₂ : t₂ ∈ Finset.range (3 ^ k)),
      f t₁ h₁ = f t₂ h₂ → t₁ = t₂ := by
    intro t₁ t₂ h₁ h₂ he
    exact pow_modEq_inj hg hc hc1 hy (Finset.mem_range.1 h₁) (Finset.mem_range.1 h₂) he
  have hcard : tgt.card ≤ (Finset.range (3 ^ k)).card := by
    refine Finset.card_le_card_of_injOn (fun z => z / 3 ^ c) ?_ ?_
    · intro z hz
      have hz' := Finset.mem_coe.1 hz
      rw [htgt, Finset.mem_filter, Finset.mem_range] at hz'
      refine Finset.mem_coe.2 (Finset.mem_range.2 ?_)
      rw [Nat.div_lt_iff_lt_mul hpc, ← pow_add, Nat.add_comm k c]
      exact hz'.1
    · intro z₁ hz₁ z₂ hz₂ he
      have hz₁' := Finset.mem_coe.1 hz₁
      have hz₂' := Finset.mem_coe.1 hz₂
      rw [htgt, Finset.mem_filter, Finset.mem_range] at hz₁' hz₂'
      simp only at he
      have e1 := Nat.div_add_mod z₁ (3 ^ c)
      have e2 := Nat.div_add_mod z₂ (3 ^ c)
      rw [he, hz₁'.2] at e1
      rw [hz₂'.2] at e2
      omega
  have hxt : x % 3 ^ (c + k) ∈ tgt := by
    simp only [htgt, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt _ hpos, by rw [Nat.mod_mod_of_dvd _ hcdvd]; exact hx⟩
  obtain ⟨t, ht, he⟩ := Finset.surj_on_of_inj_on_of_card_le f hmaps hinj hcard _ hxt
  exact ⟨t, Finset.mem_range.1 ht, he.symm⟩

/-- **`e < 2·3^k` with `3^{k+1} ∣ 2^e y + 1`** (`3 ∤ y`; the form in which 2 being a primitive root modulo `3^{k+1}` is used). -/
theorem exists_two_pow_mul_add_one_dvd (k y : ℕ) (hy : ¬ 3 ∣ y) :
    ∃ e < 2 * 3 ^ k, 3 ^ (k + 1) ∣ 2 ^ e * y + 1 := by
  have hc4 : padicValNat 3 (4 - 1) = 1 := by norm_num
  have hpk : 0 < 3 ^ (k + 1) := by positivity
  -- The core in the case `y ≡ 2 (mod 3)`
  have core : ∀ y', ¬ 3 ∣ y' → y' % 3 = 2 → ∃ t < 3 ^ k, 3 ^ (k + 1) ∣ 4 ^ t * y' + 1 := by
    intro y' hy' h2
    have hx : 3 ^ (k + 1) - 1 ≡ y' [MOD 3 ^ 1] := by
      have h1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      have : 3 ^ (k + 1) % 3 = 0 := by rw [pow_succ]; simp
      unfold Nat.ModEq
      rw [pow_one]
      omega
    obtain ⟨t, ht, hm⟩ := pow_cover (g := 4) (by norm_num) hc4 le_rfl k hy' hx
    refine ⟨t, ht, ?_⟩
    rw [Nat.add_comm 1 k] at hm
    have h1 : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    have : (4 ^ t * y' + 1) % 3 ^ (k + 1) = 0 := by
      rw [Nat.add_mod, hm, Nat.mod_eq_of_lt (by omega : 3 ^ (k + 1) - 1 < 3 ^ (k + 1))]
      have h1' : 1 % 3 ^ (k + 1) = 1 := Nat.mod_eq_of_lt (by
        have : 3 ≤ 3 ^ (k + 1) := by
          calc 3 = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
      rw [h1', Nat.sub_add_cancel h1, Nat.mod_self]
    exact Nat.dvd_of_mod_eq_zero this
  have hy3 : y % 3 = 1 ∨ y % 3 = 2 := by omega
  rcases hy3 with h1 | h2
  · obtain ⟨t, ht, hd⟩ := core (2 * y) (by omega) (by omega)
    refine ⟨2 * t + 1, by omega, ?_⟩
    have : 2 ^ (2 * t + 1) * y = 4 ^ t * (2 * y) := by
      rw [pow_succ, pow_mul]; norm_num; ring
    rwa [this]
  · obtain ⟨t, ht, hd⟩ := core y hy h2
    refine ⟨2 * t, by omega, ?_⟩
    have : 2 ^ (2 * t) * y = 4 ^ t * y := by rw [pow_mul]; norm_num
    rwa [this]

theorem two_pow_mod_three (s : ℕ) : 2 ^ s % 3 = if s % 2 = 0 then 1 else 2 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

/-- `3^t ∣ 2^s - 1 ⟺ 2·3^{t-1} ∣ s` (`t ≥ 1`). -/
theorem three_pow_dvd_two_pow_sub_one_iff (t s : ℕ) (ht : 1 ≤ t) :
    3 ^ t ∣ 2 ^ s - 1 ↔ 2 * 3 ^ (t - 1) ∣ s := by
  constructor
  · intro h
    have h3 : 3 ∣ 2 ^ s - 1 := (dvd_pow_self 3 (by omega)).trans h
    have hs2 : s % 2 = 0 := by
      have := two_pow_mod_three s
      have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      split_ifs at this with hh
      · exact hh
      · omega
    obtain ⟨s', rfl⟩ : ∃ s', s = 2 * s' := ⟨s / 2, by omega⟩
    rcases Nat.eq_zero_or_pos s' with h0 | hpos
    · subst h0; simp
    · rw [pow_mul] at h
      norm_num at h
      have hne : 4 ^ s' - 1 ≠ 0 := by
        have : 4 ≤ 4 ^ s' := Nat.le_self_pow (by omega) 4
        omega
      have hle := (padicValNat_dvd_iff_le hne).1 h
      rw [v3_four_pow_sub_one (by omega)] at hle
      have : 3 ^ (t - 1) ∣ s' := (padicValNat_dvd_iff_le (by omega)).2 (by omega)
      exact Nat.mul_dvd_mul_left 2 this
  · rintro ⟨q, rfl⟩
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; simp
    · rw [mul_assoc, pow_mul]
      norm_num
      have hne : 4 ^ (3 ^ (t - 1) * q) - 1 ≠ 0 := by
        have : 4 ≤ 4 ^ (3 ^ (t - 1) * q) := Nat.le_self_pow (by positivity) 4
        omega
      refine (padicValNat_dvd_iff_le hne).2 ?_
      rw [v3_four_pow_sub_one (by positivity), padicValNat.mul (by positivity) (by omega),
        padicValNat.prime_pow]
      omega

/-- **`ord_{3^t} 2 = 2·3^{t-1}`** (`t ≥ 1`). -/
theorem orderOf_two_three_pow (t : ℕ) (ht : 1 ≤ t) : orderOf (2 : ZMod (3 ^ t)) = 2 * 3 ^ (t - 1) := by
  have key : ∀ s, (2 : ZMod (3 ^ t)) ^ s = 1 ↔ 2 * 3 ^ (t - 1) ∣ s := by
    intro s
    rw [← three_pow_dvd_two_pow_sub_one_iff t s ht]
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have : ((2 ^ s : ℕ) : ZMod (3 ^ t)) = ((1 : ℕ) : ZMod (3 ^ t)) ↔ 3 ^ t ∣ 2 ^ s - 1 := by
      rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' h1]
    simpa using this
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one ((key _).2 dvd_rfl)
  · exact (key _).1 (pow_orderOf_eq_one _)

end Collatz.Arctic.NatQ5.W2a
