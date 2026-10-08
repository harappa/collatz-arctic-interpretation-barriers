/-
Generic layer: the digits of the end point of the point family.

Adapted from `FamilyDigits.lean` for $T$ (the splitting of the digits of the end point in Theorem 6.8, an application of Lemma 6.4). The point family is
`Gen/Family.lean` (the form taking a model `BM` as an argument). We only replace the end constant `terrasC (parityOf β)` by `BM.C β` and its upper bound
`terrasC_lt` by `BM.C_lt`; the argument is the same as in the source (it uses only the shape `x₁ = c + 3^A t`, `c < 3^A`).
The shape-only lemmas `fam_binTail_divmod`, `fam_bitsMSB_three`, `fam_three_pow_odd` are used from the source as they are.

`ϖ := x₁ mod 2^n`, `h := ⌊x₁ / 2^n⌋`.
* `fam_binTail_X1`: `bin'(x₁) = bin'(h) · ϖ` (`n` digits). `fam_bitsMSB_varpi`: `ϖ = top K digits · middle · r_{β₀}`.
* `fam_mid_bijOn`, `fam_mid_card` (Lemma 6.4 (i)), `fam_end_tv` (Lemma 6.4 (ii)).
* `fam_h_low`, `fam_h_high`: the length of the uncontrolled upper part.
-/
import CollatzProof.Arctic.Gen.Family
import CollatzProof.Arctic.FamilyDigits

namespace Collatz.Arctic.Gen

open Collatz.Arctic

variable {BM : BlockModel}

/-- `h ≥ ⌊3^A τ / 2^K⌋` (`h := ⌊x₁ / 2^n⌋`). -/
theorem fam_h_ge_div {β₀ β : List Bool} {n K : ℕ} (τ u : ℕ) (hKn : K ≤ n) :
    3 ^ terrasA (parityOf β) * τ / 2 ^ K ≤ famX1 BM β₀ β n K τ u / 2 ^ n := by
  have e : 2 ^ n = 2 ^ K * 2 ^ (n - K) := fam_pow_split n K hKn
  have h1 : 3 ^ terrasA (parityOf β) * τ * 2 ^ (n - K) ≤ famX1 BM β₀ β n K τ u := by
    unfold famX1 famT
    have : 3 ^ terrasA (parityOf β) * (τ * 2 ^ (n - K)) ≤
        3 ^ terrasA (parityOf β) *
          (τ * 2 ^ (n - K) + 2 ^ (parityOf β₀).length * u + famRho BM β₀ β) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [← mul_assoc] at this
    omega
  calc 3 ^ terrasA (parityOf β) * τ / 2 ^ K
      = 3 ^ terrasA (parityOf β) * τ * 2 ^ (n - K) / 2 ^ n := by
        rw [e, Nat.mul_div_mul_right _ _ (by positivity)]
    _ ≤ _ := Nat.div_le_div_right h1

/-- `h · 2^K < 3^A (τ + 1)`. -/
theorem fam_h_lt {β₀ β : List Bool} {n K τ u : ℕ} (hKn : K + (parityOf β₀).length ≤ n)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    famX1 BM β₀ β n K τ u / 2 ^ n * 2 ^ K < 3 ^ terrasA (parityOf β) * (τ + 1) := by
  have e : 2 ^ n = 2 ^ K * 2 ^ (n - K) := fam_pow_split n K (by omega)
  have hl := fam_low_lt (BM := BM) (β := β) hKn hu
  have hc := BM.C_lt β
  -- `x₁ < 3^A (τ + 1) 2^{n-K}`
  have hx : famX1 BM β₀ β n K τ u < 3 ^ terrasA (parityOf β) * (τ + 1) * 2 ^ (n - K) := by
    unfold famX1 famT
    have : 3 ^ terrasA (parityOf β) * (τ * 2 ^ (n - K) + 2 ^ (parityOf β₀).length * u
        + famRho BM β₀ β + 1) ≤ 3 ^ terrasA (parityOf β) * ((τ + 1) * 2 ^ (n - K)) :=
      Nat.mul_le_mul_left _ (by rw [add_mul, one_mul]; omega)
    rw [mul_add, mul_one, ← mul_assoc] at this
    omega
  have hdm : famX1 BM β₀ β n K τ u / 2 ^ n * 2 ^ K * 2 ^ (n - K) ≤ famX1 BM β₀ β n K τ u := by
    rw [mul_assoc, ← e]; exact Nat.div_mul_le_self _ _
  exact Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt hdm hx)

/-- `h ≥ ⌊3^A / 2⌋` (`τ ≥ 2^{K-1}`). -/
theorem fam_h_ge_half {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) :
    3 ^ terrasA (parityOf β) / 2 ≤ famX1 BM β₀ β n K τ u / 2 ^ n := by
  refine le_trans ?_ (fam_h_ge_div τ u hKn)
  have e : 2 ^ K = 2 ^ (K - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  calc 3 ^ terrasA (parityOf β) / 2
      = 3 ^ terrasA (parityOf β) * 2 ^ (K - 1) / 2 ^ K := by
        rw [e, mul_comm (2 ^ (K - 1)) 2, Nat.mul_div_mul_right _ _ (by positivity)]
    _ ≤ 3 ^ terrasA (parityOf β) * τ / 2 ^ K :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ hτ1)

/-- If `A ≥ 1` then `h ≥ 1`. -/
theorem fam_h_pos {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hA : 1 ≤ terrasA (parityOf β)) :
    1 ≤ famX1 BM β₀ β n K τ u / 2 ^ n := by
  refine le_trans ?_ (fam_h_ge_half u hK hKn hτ1)
  have : 3 ≤ 3 ^ terrasA (parityOf β) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hA
  omega

/-- **(4) Digits of the end point**: `bin'(x₁) = bin'(h) · ϖ (n digits)`. -/
theorem fam_binTail_X1 {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hA : 1 ≤ terrasA (parityOf β)) :
    binTail (famX1 BM β₀ β n K τ u)
      = binTail (famX1 BM β₀ β n K τ u / 2 ^ n) ++ bitsMSB n (famX1 BM β₀ β n K τ u % 2 ^ n) := by
  apply fam_binTail_divmod
  have h := fam_h_pos (BM := BM) (β₀ := β₀) u hK hKn hτ1 hA
  rwa [Nat.one_le_div_iff (by positivity)] at h

/-- **(4)**: the `n` digits of `ϖ` = the top `K` digits · the middle `n-K-s'` digits · the `s'` digits of the shared `r_{β₀}`. -/
theorem fam_bitsMSB_varpi {β₀ β : List Bool} {n K : ℕ} (τ u : ℕ)
    (hKn : K + (parityOf β₀).length ≤ n) :
    bitsMSB n (famX1 BM β₀ β n K τ u % 2 ^ n)
      = bitsMSB K (famX1 BM β₀ β n K τ u % 2 ^ n / 2 ^ (n - K))
        ++ bitsMSB (n - K - (parityOf β₀).length)
            (famX1 BM β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)
        ++ bitsMSB (parityOf β₀).length (BM.R β₀) := by
  rw [fam_bitsMSB_three n K _ _ hKn (Nat.mod_lt _ (by positivity)),
    Nat.mod_mod_of_dvd (famX1 BM β₀ β n K τ u)
      (Nat.pow_dvd_pow 2 (by omega : (parityOf β₀).length ≤ n)),
    fam_X1_mod τ u hKn]

/-- **(4)**: the middle bits of `ϖ` have the form of Lemma 6.4 (`z = c_β`, `Q = 3^A`, `T0 = τ`, `w = s'`, `ρ = famRho`). -/
theorem fam_mid_eq (β₀ β : List Bool) (n K τ u : ℕ) :
    famX1 BM β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length
      = (BM.C β + 3 ^ terrasA (parityOf β) *
          (τ * 2 ^ (n - K) + 2 ^ (parityOf β₀).length * u + famRho BM β₀ β))
          % 2 ^ (n - K) / 2 ^ (parityOf β₀).length := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.sub_le n K))]
  rfl

/-- **(4)**: `h` has the form of Lemma 6.4 (ii). -/
theorem fam_h_eq (β₀ β : List Bool) (n K τ u : ℕ) :
    famX1 BM β₀ β n K τ u / 2 ^ n
      = (BM.C β + 3 ^ terrasA (parityOf β) *
          (τ * 2 ^ (n - K) + 2 ^ (parityOf β₀).length * u + famRho BM β₀ β)) / 2 ^ n := rfl

/-- **(4), Lemma 6.4 (i)**: the middle bits are a bijection of `u ∈ [0, 2^{n-K-s'})`. -/
theorem fam_mid_bijOn (β₀ β : List Bool) {n K : ℕ} (τ : ℕ) (hKn : K + (parityOf β₀).length ≤ n) :
    Set.BijOn (fun u => famX1 BM β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)
      ↑(Finset.range (2 ^ (n - K - (parityOf β₀).length)))
      ↑(Finset.range (2 ^ (n - K - (parityOf β₀).length))) := by
  simp only [fam_mid_eq]
  exact EndDigits.mid_bits_bijOn _ _ τ _ n K _ (fam_three_pow_odd _) hKn

/-- **(4), the counting form of Lemma 6.4 (i)**. -/
theorem fam_mid_card (β₀ β : List Bool) {n K : ℕ} (τ : ℕ) (hKn : K + (parityOf β₀).length ≤ n)
    (v : ℕ) (hv : v < 2 ^ (n - K - (parityOf β₀).length)) :
    (Finset.filter
      (fun u => famX1 BM β₀ β n K τ u % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length = v)
      (Finset.range (2 ^ (n - K - (parityOf β₀).length)))).card = 1 := by
  simp only [fam_mid_eq]
  exact EndDigits.mid_bits_card _ _ τ _ n K _ (fam_three_pow_odd _) hKn v hv

/-- **(4), Lemma 6.4 (ii)**: the law of `h mod 2^b` is close to uniform (`2^{b+Δ+K} ≤ 3^A`). -/
theorem fam_end_tv (β₀ β : List Bool) {n K : ℕ} (τ b Δ : ℕ) (hKn : K + (parityOf β₀).length ≤ n)
    (hb : 2 ^ (b + Δ + K) ≤ 3 ^ terrasA (parityOf β)) :
    ∑ j ∈ Finset.range (2 ^ b),
      |((Finset.filter (fun u => famX1 BM β₀ β n K τ u / 2 ^ n % 2 ^ b = j)
          (Finset.range (2 ^ (n - K - (parityOf β₀).length)))).card : ℚ)
          / 2 ^ (n - K - (parityOf β₀).length) - 1 / 2 ^ b|
      ≤ 3 / 2 ^ Δ + 2 ^ ((parityOf β₀).length + 2) * (3 ^ terrasA (parityOf β) : ℕ) / 2 ^ n := by
  simp only [fam_h_eq]
  exact EndDigits.end_digits_tv_sharp _ _ τ _ n K _ b Δ hKn hb

/-- **(4)**: if `2^{b+Δ+K} ≤ 3^A` then `2^b ≤ h`, and moreover `K + Δ - 1 ≤ lenT ⌊h/2^b⌋`. -/
theorem fam_h_low {β₀ β : List Bool} {n K τ : ℕ} (u b Δ : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hb : 2 ^ (b + Δ + K) ≤ 3 ^ terrasA (parityOf β)) :
    2 ^ (b + (Δ + K - 1)) ≤ famX1 BM β₀ β n K τ u / 2 ^ n
      ∧ K + Δ - 1 ≤ lenT (famX1 BM β₀ β n K τ u / 2 ^ n / 2 ^ b) := by
  have h := fam_h_ge_half (BM := BM) (β₀ := β₀) (β := β) u hK hKn hτ1
  have e : 2 ^ (b + Δ + K) = 2 ^ (b + (Δ + K - 1)) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [e] at hb
  have h1 : 2 ^ (b + (Δ + K - 1)) ≤ famX1 BM β₀ β n K τ u / 2 ^ n :=
    le_trans (by rw [Nat.le_div_iff_mul_le (by norm_num)]; exact hb) h
  refine ⟨h1, ?_⟩
  apply fam_le_lenT
  rw [Nat.le_div_iff_mul_le (by positivity), ← pow_add, add_comm,
    show K + Δ - 1 = Δ + K - 1 by omega]
  exact h1

/-- **(4)**: if `3^A < 2^{b+K+Δ+1}` then `lenT ⌊h/2^b⌋ ≤ K + Δ` (the length of the uncontrolled upper part). -/
theorem fam_h_high {β₀ β : List Bool} {n K τ u : ℕ} (b Δ : ℕ)
    (hKn : K + (parityOf β₀).length ≤ n) (hτ2 : τ < 2 ^ K)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length))
    (hb : 3 ^ terrasA (parityOf β) < 2 ^ (b + (K + Δ + 1))) :
    lenT (famX1 BM β₀ β n K τ u / 2 ^ n / 2 ^ b) ≤ K + Δ := by
  have h1 := fam_h_lt (BM := BM) (β := β) (τ := τ) hKn hu
  have h2 : 3 ^ terrasA (parityOf β) * (τ + 1) ≤ 3 ^ terrasA (parityOf β) * 2 ^ K :=
    Nat.mul_le_mul_left _ hτ2
  have hh : famX1 BM β₀ β n K τ u / 2 ^ n < 3 ^ terrasA (parityOf β) :=
    Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le h1 h2)
  have h3 : famX1 BM β₀ β n K τ u / 2 ^ n / 2 ^ b < 2 ^ (K + Δ + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, add_comm]
    exact lt_trans hh hb
  rcases Nat.eq_zero_or_pos (famX1 BM β₀ β n K τ u / 2 ^ n / 2 ^ b) with h0 | hp
  · rw [h0, fam_lenT_eq_log]; simp
  · have := fam_lenT_lt hp.ne' h3
    omega

end Collatz.Arctic.Gen
