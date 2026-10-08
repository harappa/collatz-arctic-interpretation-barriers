/-
Generic layer: the deterministic part of the point family of a block model.

Adapted from `Family.lean` for $T$ (the point family of the model of `T`, Section 6.1). Taking a model `BM : BlockModel` (`Gen/Model.lean`)
as an argument, we replace the residue `terrasR (parityOf β)` by `BM.R β`, the end constant `terrasC (parityOf β)` by `BM.C β`, and the iterate
`T^[(parityOf β).length]` by `BM.f^[BM.steps β]`. The names are the same as in the source and are distinguished by the namespace `Collatz.Arctic.Gen`
(lemmas depending only on the shape, such as `fam_s_le`, `fam_lenT_eq_log`, `fam_three_pow_le`, are used from the source as they are).

**Number of bits and number of steps**: `m := (parityOf β).length` is the number of bits (`2^m`, `bitsMSB`), and the number of steps of the orbit is `BM.steps β`
(used only by `fam_iter` and `fam_orbit_dom`). The two numbers agree for $T$ but differ for $H$.

The choice of blocks `β` (the whole, including the first `β₀`), the shared part `σ₀ := parityOf β₀`, `s' := |σ₀|` (`β₀ <+: β`).
* `famRho BM β₀ β`: the `ρ < 2^{s'}` with `c_β + 3^A ρ ≡ r_{β₀} (mod 2^{s'})`.
* `famT BM β₀ β n K τ u := τ 2^{n-K} + 2^{s'} u + ρ`, `famX0 := r_β + 2^m t`, `famX1 := c_β + 3^A t`.
* `famRtop`: the upper digits `r'` of the residue (`r_β = r_{β₀} + 2^{s'} r'`).

What we show (the properties of the point family, Section 6.1; items (1)–(5) of the source):
* (1) `fam_iter`: `x₁ = f^[steps β] x₀`. `fam_orbit_dom`: the points `x₀, …, f^[steps β - 1] x₀` lie in the domain.
* (2) `fam_X1_mod`: `x₁ ≡ r_{β₀} (mod 2^{s'})`.
* (3) `fam_binTail_X0`: the digits of the starting point are `bin'(τ)`, `u`, `ρ`, `r'`, `r_{β₀}` in this order. `fam_lenT_X0`: `lenT x₀ = n + m - 1`.
* (5) `fam_lenT_expand`, `fam_lenT_X1_lt_two`, `fam_X0_ge`: expansion of the length, an upper bound for it, and a lower bound for the starting point.
-/
import CollatzProof.Arctic.Gen.Model

namespace Collatz.Arctic.Gen

open Collatz.Arctic

variable (BM : BlockModel)

/-! ## Definition of the family -/

/-- The low `s'` bits `ρ < 2^{s'}`: `c_β + 3^A ρ ≡ r_{β₀} (mod 2^{s'})`. -/
def famRho (β₀ β : List Bool) : ℕ :=
  ((((BM.R β₀ : ℕ) : ZMod (2 ^ (parityOf β₀).length))
      - ((BM.C β : ℕ) : ZMod (2 ^ (parityOf β₀).length)))
    * ((3 : ZMod (2 ^ (parityOf β₀).length)) ^ terrasA (parityOf β))⁻¹).val

/-- `t := τ 2^{n-K} + 2^{s'} u + ρ`. -/
def famT (β₀ β : List Bool) (n K τ u : ℕ) : ℕ :=
  τ * 2 ^ (n - K) + 2 ^ (parityOf β₀).length * u + famRho BM β₀ β

/-- Starting point `x₀ := r_β + 2^m t` (`m` is the number of bits). -/
def famX0 (β₀ β : List Bool) (n K τ u : ℕ) : ℕ :=
  BM.R β + 2 ^ (parityOf β).length * famT BM β₀ β n K τ u

/-- End point `x₁ := c_β + 3^A t`. -/
def famX1 (β₀ β : List Bool) (n K τ u : ℕ) : ℕ :=
  BM.C β + 3 ^ terrasA (parityOf β) * famT BM β₀ β n K τ u

/-- The upper digits `r'` of the residue (`r_β = r_{β₀} + 2^{s'} r'`). -/
def famRtop (β₀ β : List Bool) : ℕ := BM.R β / 2 ^ (parityOf β₀).length

variable {BM}

/-! ## `ρ` -/

theorem fam_rho_lt (β₀ β : List Bool) : famRho BM β₀ β < 2 ^ (parityOf β₀).length := by
  unfold famRho
  exact ZMod.val_lt _

theorem fam_rho_spec (β₀ β : List Bool) :
    (BM.C β + 3 ^ terrasA (parityOf β) * famRho BM β₀ β) % 2 ^ (parityOf β₀).length = BM.R β₀ := by
  set s := (parityOf β₀).length with hs
  have hlt : BM.R β₀ < 2 ^ s := BM.R_lt _
  conv_rhs => rw [← Nat.mod_eq_of_lt hlt]
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  unfold famRho
  rw [ZMod.natCast_zmod_val]
  have hcop : Nat.Coprime (3 ^ terrasA (parityOf β)) (2 ^ s) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have hu := ZMod.coe_mul_inv_eq_one _ hcop
  push_cast at hu
  linear_combination ((BM.R β₀ : ZMod (2 ^ s)) - (BM.C β : ZMod (2 ^ s))) * hu

/-! ## The shared part -/

/-- Sharing: `r_β ≡ r_{β₀} (mod 2^{s'})` (the model's `R_prefix`). -/
theorem fam_terrasR_mod {β₀ β : List Bool} (hpre : β₀ <+: β) :
    BM.R β % 2 ^ (parityOf β₀).length = BM.R β₀ := by
  obtain ⟨r, rfl⟩ := hpre
  exact BM.R_prefix β₀ r

/-- `r_β = r_{β₀} + 2^{s'} r'`. -/
theorem fam_terrasR_split {β₀ β : List Bool} (hpre : β₀ <+: β) :
    BM.R β = BM.R β₀ + 2 ^ (parityOf β₀).length * famRtop BM β₀ β := by
  have h := Nat.mod_add_div (BM.R β) (2 ^ (parityOf β₀).length)
  rw [fam_terrasR_mod hpre] at h
  unfold famRtop; omega

theorem fam_rtop_lt {β₀ β : List Bool} (hpre : β₀ <+: β) :
    famRtop BM β₀ β < 2 ^ ((parityOf β).length - (parityOf β₀).length) := by
  unfold famRtop
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
    Nat.sub_add_cancel (fam_s_le hpre)]
  exact BM.R_lt _

/-! ## The size of `t` -/

/-- The lower part `2^{s'} u + ρ < 2^{n-K}`. -/
lemma fam_low_lt {β₀ β : List Bool} {n K u : ℕ} (hKn : K + (parityOf β₀).length ≤ n)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    2 ^ (parityOf β₀).length * u + famRho BM β₀ β < 2 ^ (n - K) := by
  have hρ := fam_rho_lt (BM := BM) β₀ β
  have e := fam_pow_split (n - K) (parityOf β₀).length (by omega)
  rw [e]
  have : 2 ^ (parityOf β₀).length * (u + 1) ≤
      2 ^ (parityOf β₀).length * 2 ^ (n - K - (parityOf β₀).length) :=
    Nat.mul_le_mul_left _ hu
  rw [mul_add, mul_one] at this
  omega

theorem fam_T_ge {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) : 2 ^ (n - 1) ≤ famT BM β₀ β n K τ u := by
  unfold famT
  have : 2 ^ (n - 1) = 2 ^ (K - 1) * 2 ^ (n - K) := by rw [← pow_add]; congr 1; omega
  rw [this]
  have := Nat.mul_le_mul_right (2 ^ (n - K)) hτ1
  omega

theorem fam_T_lt {β₀ β : List Bool} {n K τ u : ℕ} (hKn : K + (parityOf β₀).length ≤ n)
    (hτ2 : τ < 2 ^ K) (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    famT BM β₀ β n K τ u < 2 ^ n := by
  unfold famT
  have hl := fam_low_lt (BM := BM) (β := β) hKn hu
  have : 2 ^ n = 2 ^ K * 2 ^ (n - K) := fam_pow_split n K (by omega)
  rw [this]
  have := Nat.mul_le_mul_right (2 ^ (n - K)) (Nat.succ_le_of_lt hτ2)
  rw [Nat.succ_mul] at this
  omega

theorem fam_T_pos {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hτ : 1 ≤ τ) :
    1 ≤ famT BM β₀ β n K τ u := by
  unfold famT
  have : 1 ≤ τ * 2 ^ (n - K) := Nat.mul_le_mul hτ Nat.one_le_two_pow
  omega

/-! ## (1) The orbit (number of steps `BM.steps β`) -/

/-- **(1)**: `x₁ = f^[steps β] x₀` (the iterate is the number of steps). -/
theorem fam_iter (β₀ β : List Bool) (n K τ u : ℕ) :
    famX1 BM β₀ β n K τ u = BM.f^[BM.steps β] (famX0 BM β₀ β n K τ u) :=
  (BM.iter _ _).symm

/-- **(1)**: the points `x₀, …, f^[steps β - 1] x₀` of the orbit lie in the domain. -/
theorem fam_orbit_dom (β₀ β : List Bool) {n K τ : ℕ} (u : ℕ) (hτ : 1 ≤ τ) :
    ∀ i < BM.steps β, BM.dom (BM.f^[i] (famX0 BM β₀ β n K τ u)) :=
  BM.orbit_dom _ _ (fam_T_pos u hτ)

/-! ## (2) Shared low bits -/

theorem fam_X1_mod {β₀ β : List Bool} {n K : ℕ} (τ u : ℕ) (hKn : K + (parityOf β₀).length ≤ n) :
    famX1 BM β₀ β n K τ u % 2 ^ (parityOf β₀).length = BM.R β₀ := by
  unfold famX1 famT
  have e := fam_pow_split (n - K) (parityOf β₀).length (by omega)
  have : BM.C β + 3 ^ terrasA (parityOf β) *
      (τ * 2 ^ (n - K) + 2 ^ (parityOf β₀).length * u + famRho BM β₀ β)
      = (BM.C β + 3 ^ terrasA (parityOf β) * famRho BM β₀ β)
        + 2 ^ (parityOf β₀).length * (3 ^ terrasA (parityOf β) *
          (τ * 2 ^ (n - K - (parityOf β₀).length) + u)) := by
    rw [e]; ring
  rw [this, Nat.add_mul_mod_self_left, fam_rho_spec]

/-! ## (3) The digits of the starting point -/

/-- **(3) Digits of the starting point**: `bin'(x₀) = bin'(τ) · u (n-K-s' digits) · ρ (s' digits) · r' (m-s' digits) · r_{β₀} (s' digits)`. -/
theorem fam_binTail_X0 {β₀ β : List Bool} (hpre : β₀ <+: β) {n K τ u : ℕ}
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    binTail (famX0 BM β₀ β n K τ u)
      = binTail τ ++ bitsMSB (n - K - (parityOf β₀).length) u
        ++ bitsMSB (parityOf β₀).length (famRho BM β₀ β)
        ++ bitsMSB ((parityOf β).length - (parityOf β₀).length) (famRtop BM β₀ β)
        ++ bitsMSB (parityOf β₀).length (BM.R β₀) := by
  set s := (parityOf β₀).length with hs
  set m := (parityOf β).length with hm
  have hsm : s ≤ m := fam_s_le hpre
  unfold famX0
  rw [binTail_add_mul m _ _ (fam_T_pos u hτ) (BM.R_lt _)]
  -- the residue part
  have hr : bitsMSB m (BM.R β)
      = bitsMSB (m - s) (famRtop BM β₀ β) ++ bitsMSB s (BM.R β₀) := by
    rw [fam_terrasR_split hpre]
    have := bitsMSB_add_mul (m - s) s (famRtop BM β₀ β) (BM.R β₀)
      (fam_rtop_lt hpre) (BM.R_lt _)
    rwa [Nat.sub_add_cancel hsm] at this
  -- the `t` part
  have ht : famT BM β₀ β n K τ u = famRho BM β₀ β + 2 ^ s * (u + 2 ^ (n - K - s) * τ) := by
    unfold famT
    rw [fam_pow_split (n - K) s (by omega)]; ring
  have hpos : 1 ≤ u + 2 ^ (n - K - s) * τ :=
    le_trans (Nat.mul_le_mul Nat.one_le_two_pow hτ) (Nat.le_add_left _ _)
  rw [hr, ht, binTail_add_mul s _ _ hpos (fam_rho_lt β₀ β), binTail_add_mul _ _ _ hτ hu]
  simp only [List.append_assoc]

/-- **(3)**: `lenT x₀ = n + m - 1`. -/
theorem fam_lenT_X0 (β₀ β : List Bool) {n K τ u : ℕ} (hK : 1 ≤ K)
    (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ) (hτ2 : τ < 2 ^ K)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    lenT (famX0 BM β₀ β n K τ u) = n + (parityOf β).length - 1 := by
  have h1 := fam_T_ge (BM := BM) (β₀ := β₀) (β := β) (n := n) u hK (by omega) hτ1
  have h2 := fam_T_lt (BM := BM) (β := β) hKn hτ2 hu
  have hr := BM.R_lt β
  unfold famX0
  generalize (parityOf β).length = m at hr ⊢
  generalize famT BM β₀ β n K τ u = t at h1 h2 ⊢
  apply fam_lenT_of_bounds
  · have : 2 ^ (n + m - 1) = 2 ^ m * 2 ^ (n - 1) := by rw [← pow_add]; congr 1; omega
    rw [this]
    have := Nat.mul_le_mul_left (2 ^ m) h1
    omega
  · have : 2 ^ (n + m - 1 + 1) = 2 ^ m * 2 ^ n := by rw [← pow_add]; congr 1; omega
    rw [this]
    have := Nat.mul_le_mul_left (2 ^ m) (Nat.succ_le_of_lt h2)
    rw [Nat.mul_succ] at this
    omega

/-! ## (5) Expansion of the length -/

/-- `3^A 2^{n-1} ≤ x₁`. -/
lemma fam_X1_ge {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) :
    3 ^ terrasA (parityOf β) * 2 ^ (n - 1) ≤ famX1 BM β₀ β n K τ u := by
  unfold famX1
  have := Nat.mul_le_mul_left (3 ^ terrasA (parityOf β))
    (fam_T_ge (BM := BM) (β₀ := β₀) (β := β) u hK hKn hτ1)
  omega

/-- `x₁ < 2^n 3^A`. -/
lemma fam_X1_lt {β₀ β : List Bool} {n K τ u : ℕ} (hKn : K + (parityOf β₀).length ≤ n)
    (hτ2 : τ < 2 ^ K) (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    famX1 BM β₀ β n K τ u < 2 ^ n * 3 ^ terrasA (parityOf β) := by
  unfold famX1
  have hc := BM.C_lt β
  have := Nat.mul_le_mul_left (3 ^ terrasA (parityOf β))
    (Nat.succ_le_of_lt (fam_T_lt (BM := BM) (β := β) hKn hτ2 hu))
  rw [Nat.mul_succ] at this
  rw [mul_comm (2 ^ n)]
  omega

/-- **(5) Lower bound for the length**: if `2^{m+j} ≤ 3^A` then `lenT x₁ ≥ n + m - 1 + j`. -/
theorem fam_lenT_X1_ge (β₀ β : List Bool) {n K τ : ℕ} (u j : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hexp : 2 ^ ((parityOf β).length + j) ≤ 3 ^ terrasA (parityOf β)) :
    n + (parityOf β).length - 1 + j ≤ lenT (famX1 BM β₀ β n K τ u) := by
  apply fam_le_lenT
  have h := fam_X1_ge (BM := BM) (β₀ := β₀) (β := β) u hK hKn hτ1
  have : 2 ^ (n + (parityOf β).length - 1 + j) = 2 ^ ((parityOf β).length + j) * 2 ^ (n - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  exact le_trans (Nat.mul_le_mul_right _ hexp) h

/-- **(5) Expansion**: if `2^{m+j} ≤ 3^A` then `lenT x₁ ≥ lenT x₀ + j`. -/
theorem fam_lenT_expand (β₀ β : List Bool) {n K τ u : ℕ} (j : ℕ) (hK : 1 ≤ K)
    (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ) (hτ2 : τ < 2 ^ K)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length))
    (hexp : 2 ^ ((parityOf β).length + j) ≤ 3 ^ terrasA (parityOf β)) :
    lenT (famX0 BM β₀ β n K τ u) + j ≤ lenT (famX1 BM β₀ β n K τ u) := by
  rw [fam_lenT_X0 β₀ β hK hKn hτ1 hτ2 hu]
  exact fam_lenT_X1_ge β₀ β u j hK (by omega) hτ1 hexp

/-- **(5) Upper bound for the length**: if `3^A ≤ 2^e` then `lenT x₁ < n + e`. -/
theorem fam_lenT_X1_lt (β₀ β : List Bool) {n K τ u : ℕ} (e : ℕ)
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ) (hτ2 : τ < 2 ^ K)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) (he : 3 ^ terrasA (parityOf β) ≤ 2 ^ e) :
    lenT (famX1 BM β₀ β n K τ u) < n + e := by
  have hpos : famX1 BM β₀ β n K τ u ≠ 0 := by
    have := fam_T_pos (BM := BM) (β₀ := β₀) (β := β) (n := n) (K := K) u hτ
    have : 1 * 1 ≤ 3 ^ terrasA (parityOf β) * famT BM β₀ β n K τ u :=
      Nat.mul_le_mul (Nat.one_le_pow _ _ (by norm_num)) this
    unfold famX1; omega
  apply fam_lenT_lt hpos
  rw [pow_add]
  exact lt_of_lt_of_le (fam_X1_lt hKn hτ2 hu) (Nat.mul_le_mul_left _ he)

/-- **(5) Upper bound for the length**: `lenT x₁ < n + 2m`. -/
theorem fam_lenT_X1_lt_two (β₀ β : List Bool) {n K τ u : ℕ}
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ) (hτ2 : τ < 2 ^ K)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    lenT (famX1 BM β₀ β n K τ u) < n + 2 * (parityOf β).length :=
  fam_lenT_X1_lt β₀ β _ hKn hτ hτ2 hu (fam_three_pow_le _ _ (fam_terrasA_le_length _))

/-- Lower bound `2^{n+m-1} ≤ x₀` for the starting point (`x₀` can be taken `≥ N`). -/
theorem fam_X0_ge (β₀ β : List Bool) {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) :
    2 ^ (n + (parityOf β).length - 1) ≤ famX0 BM β₀ β n K τ u := by
  have h1 := fam_T_ge (BM := BM) (β₀ := β₀) (β := β) (n := n) u hK hKn hτ1
  unfold famX0
  generalize (parityOf β).length = m
  generalize famT BM β₀ β n K τ u = t at h1 ⊢
  have : 2 ^ (n + m - 1) = 2 ^ m * 2 ^ (n - 1) := by rw [← pow_add]; congr 1; omega
  rw [this]
  have := Nat.mul_le_mul_left (2 ^ m) h1
  omega

end Collatz.Arctic.Gen
