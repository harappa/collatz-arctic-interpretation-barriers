/-
The deterministic part of the point family of the block model of `T` (Lemma 6.1, Section 6.1; the point family in the proof of Theorem 6.8).
The digits of the end point are in `FamilyDigits.lean`, the numbers of uses of the dynamic rules in `FamilyUses.lean`,
and the law of large numbers for the expansion in `FamilyExp.lean`.

A block sequence `β` (the whole sequence, including the initial part `β₀`; `σ := parityOf β`, `m := |σ|`, `a := a_σ`) and the shared part
`σ₀ := parityOf β₀`, `s' := |σ₀|` (`β₀ <+: β`). The point family of Section 6.1:
* `famRho β₀ β`: the `ρ < 2^{s'}` with `c_σ + 3^a ρ ≡ r_{σ₀} (mod 2^{s'})` (that is, `t ≡ 3^{-a}(r_{σ₀} - c_σ)`;
  `3^a` is invertible modulo `2^{s'}`).
* `famT β₀ β n K τ u := τ 2^{n-K} + 2^{s'} u + ρ` (`τ` is the top window of `K` bits, `2^{K-1} ≤ τ < 2^K`;
  `u < 2^{n-K-s'}` are the free bits; `K + s' ≤ n`).
* `famX0 := r_σ + 2^m t` (starting point `x₀`), `famX1 := c_σ + 3^a t` (end point `x₁ = x_σ`).
* `famRtop`: the top digits `r'` of the Terras part (`r_σ = r_{σ₀} + 2^{s'} r'`).

Results:
* (1) `fam_iter`, `fam_orbit_two_le`: `x₁ = T^m x₀`, and the points `x₀, …, T^{m-1} x₀` of the segment are at least 2.
* (2) `fam_X0_mod`, `fam_X1_mod`: `x₀ ≡ x₁ ≡ r_{σ₀} (mod 2^{s'})` (the shared low `s'` bits).
* (3) `fam_binTail_X0`: the digits of the starting point are `bin'(τ)`, `u`, `ρ`, `r'`, `r_{σ₀}` in this order (the input to the partition `𝒫`
  of Lemma 6.5 at the starting point in Theorem 6.8). `fam_lenT_X0`: `lenT x₀ = n + m - 1`. `fam_binTail_tau_length`: `bin'(τ)` has `K - 1` digits.
* (5) `fam_lenT_expand`: if `2^{m+j} ≤ 3^a` then `lenT x₁ ≥ lenT x₀ + j`. `fam_lenT_X1_lt`, `fam_lenT_X1_lt_two`:
  upper bounds `lenT x₁ < n + e` (`3^a ≤ 2^e`) and `lenT x₁ < n + 2m`.
* Auxiliary: `fam_lenT_eq_log` (`lenT x = ⌊log₂ x⌋`), `fam_parityOf_counts` (`X'` has 8 steps, 5 odd and 3 even;
  `Y'` has 11, 7, 4).
-/
import CollatzProof.Arctic.CoreHyp
import CollatzProof.Arctic.AutoStatement

namespace Collatz.Arctic

/-! ## Definition of the family -/

/-- The low `s'` bits `ρ < 2^{s'}`: `c_σ + 3^a ρ ≡ r_{σ₀} (mod 2^{s'})` (`σ = parityOf β`, `σ₀ = parityOf β₀`). -/
def famRho (β₀ β : List Bool) : ℕ :=
  ((((terrasR (parityOf β₀) : ℕ) : ZMod (2 ^ (parityOf β₀).length))
      - ((terrasC (parityOf β) : ℕ) : ZMod (2 ^ (parityOf β₀).length)))
    * ((3 : ZMod (2 ^ (parityOf β₀).length)) ^ terrasA (parityOf β))⁻¹).val

/-- `t := τ 2^{n-K} + 2^{s'} u + ρ`. -/
def famT (β₀ β : List Bool) (n K τ u : ℕ) : ℕ :=
  τ * 2 ^ (n - K) + 2 ^ (parityOf β₀).length * u + famRho β₀ β

/-- Starting point `x₀ := r_σ + 2^m t`. -/
def famX0 (β₀ β : List Bool) (n K τ u : ℕ) : ℕ :=
  terrasR (parityOf β) + 2 ^ (parityOf β).length * famT β₀ β n K τ u

/-- End point `x₁ := c_σ + 3^a t`. -/
def famX1 (β₀ β : List Bool) (n K τ u : ℕ) : ℕ :=
  terrasC (parityOf β) + 3 ^ terrasA (parityOf β) * famT β₀ β n K τ u

/-- The top digits `r'` of the Terras part (`r_σ = r_{σ₀} + 2^{s'} r'`). -/
def famRtop (β₀ β : List Bool) : ℕ := terrasR (parityOf β) / 2 ^ (parityOf β₀).length

/-! ## `ρ` -/

theorem fam_rho_lt (β₀ β : List Bool) : famRho β₀ β < 2 ^ (parityOf β₀).length := by
  unfold famRho
  exact ZMod.val_lt _

theorem fam_rho_spec (β₀ β : List Bool) :
    (terrasC (parityOf β) + 3 ^ terrasA (parityOf β) * famRho β₀ β) % 2 ^ (parityOf β₀).length
      = terrasR (parityOf β₀) := by
  set s := (parityOf β₀).length with hs
  have hlt : terrasR (parityOf β₀) < 2 ^ s := terrasR_lt _
  conv_rhs => rw [← Nat.mod_eq_of_lt hlt]
  rw [← ZMod.natCast_eq_natCast_iff']
  push_cast
  unfold famRho
  rw [ZMod.natCast_zmod_val]
  have hcop : Nat.Coprime (3 ^ terrasA (parityOf β)) (2 ^ s) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have hu := ZMod.coe_mul_inv_eq_one _ hcop
  push_cast at hu

  linear_combination ((terrasR (parityOf β₀) : ZMod (2 ^ s)) - (terrasC (parityOf β) : ZMod (2 ^ s))) * hu

/-! ## The shared part -/

lemma fam_parityOf_append (β₁ β₂ : List Bool) :
    parityOf (β₁ ++ β₂) = parityOf β₁ ++ parityOf β₂ := by
  simp [parityOf, List.flatMap_append]

lemma fam_pow_split (a b : ℕ) (h : b ≤ a) : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by
  rw [← pow_add, Nat.add_sub_cancel' h]

theorem fam_s_le {β₀ β : List Bool} (hpre : β₀ <+: β) :
    (parityOf β₀).length ≤ (parityOf β).length := by
  obtain ⟨r, rfl⟩ := hpre
  rw [fam_parityOf_append, List.length_append]; omega

/-- Sharing: `r_σ ≡ r_{σ₀} (mod 2^{s'})`. -/
theorem fam_terrasR_mod {β₀ β : List Bool} (hpre : β₀ <+: β) :
    terrasR (parityOf β) % 2 ^ (parityOf β₀).length = terrasR (parityOf β₀) := by
  obtain ⟨r, rfl⟩ := hpre
  obtain ⟨r', _, hR⟩ := terrasR_append (parityOf β₀) (parityOf r)
  rw [fam_parityOf_append, hR, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (terrasR_lt _)]

/-- `r_σ = r_{σ₀} + 2^{s'} r'`. -/
theorem fam_terrasR_split {β₀ β : List Bool} (hpre : β₀ <+: β) :
    terrasR (parityOf β) = terrasR (parityOf β₀) + 2 ^ (parityOf β₀).length * famRtop β₀ β := by
  have h := Nat.mod_add_div (terrasR (parityOf β)) (2 ^ (parityOf β₀).length)
  rw [fam_terrasR_mod hpre] at h
  unfold famRtop; omega

theorem fam_rtop_lt {β₀ β : List Bool} (hpre : β₀ <+: β) :
    famRtop β₀ β < 2 ^ ((parityOf β).length - (parityOf β₀).length) := by
  unfold famRtop
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
    Nat.sub_add_cancel (fam_s_le hpre)]
  exact terrasR_lt _

/-! ## The size of `t` -/

/-- The low part `2^{s'} u + ρ < 2^{n-K}`. -/
lemma fam_low_lt {β₀ β : List Bool} {n K u : ℕ} (hKn : K + (parityOf β₀).length ≤ n)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    2 ^ (parityOf β₀).length * u + famRho β₀ β < 2 ^ (n - K) := by
  have hρ := fam_rho_lt β₀ β
  have e := fam_pow_split (n - K) (parityOf β₀).length (by omega)
  rw [e]
  have : 2 ^ (parityOf β₀).length * (u + 1) ≤
      2 ^ (parityOf β₀).length * 2 ^ (n - K - (parityOf β₀).length) :=
    Nat.mul_le_mul_left _ hu
  rw [mul_add, mul_one] at this
  omega

theorem fam_T_ge {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) : 2 ^ (n - 1) ≤ famT β₀ β n K τ u := by
  unfold famT
  have : 2 ^ (n - 1) = 2 ^ (K - 1) * 2 ^ (n - K) := by rw [← pow_add]; congr 1; omega
  rw [this]
  have := Nat.mul_le_mul_right (2 ^ (n - K)) hτ1
  omega

theorem fam_T_lt {β₀ β : List Bool} {n K τ u : ℕ} (hKn : K + (parityOf β₀).length ≤ n)
    (hτ2 : τ < 2 ^ K) (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    famT β₀ β n K τ u < 2 ^ n := by
  unfold famT
  have hl := fam_low_lt (β := β) hKn hu
  have : 2 ^ n = 2 ^ K * 2 ^ (n - K) := fam_pow_split n K (by omega)
  rw [this]
  have := Nat.mul_le_mul_right (2 ^ (n - K)) (Nat.succ_le_of_lt hτ2)
  rw [Nat.succ_mul] at this
  omega

theorem fam_T_pos {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hτ : 1 ≤ τ) :
    1 ≤ famT β₀ β n K τ u := by
  unfold famT
  have : 1 ≤ τ * 2 ^ (n - K) := Nat.mul_le_mul hτ Nat.one_le_two_pow
  omega

/-! ## (1) The orbit -/

/-- **(1)**: `x₁ = T^m x₀`. -/
theorem fam_iter (β₀ β : List Bool) (n K τ u : ℕ) :
    famX1 β₀ β n K τ u = T^[(parityOf β).length] (famX0 β₀ β n K τ u) :=
  (terras_iter _ _).symm

/-- **(1)**: the points `x₀, …, T^{m-1} x₀` of the orbit segment are at least 2. -/
theorem fam_orbit_two_le (β₀ β : List Bool) {n K τ : ℕ} (u : ℕ) (hτ : 1 ≤ τ) :
    ∀ i < (parityOf β).length, 2 ≤ T^[i] (famX0 β₀ β n K τ u) :=
  terras_orbit_two_le _ _ (fam_T_pos u hτ)

/-! ## (2) The shared low bits -/

theorem fam_X0_mod {β₀ β : List Bool} (hpre : β₀ <+: β) (n K τ u : ℕ) :
    famX0 β₀ β n K τ u % 2 ^ (parityOf β₀).length = terrasR (parityOf β₀) := by
  unfold famX0
  rw [fam_pow_split _ _ (fam_s_le hpre), mul_assoc, Nat.add_mul_mod_self_left,
    fam_terrasR_mod hpre]

theorem fam_X1_mod {β₀ β : List Bool} {n K : ℕ} (τ u : ℕ) (hKn : K + (parityOf β₀).length ≤ n) :
    famX1 β₀ β n K τ u % 2 ^ (parityOf β₀).length = terrasR (parityOf β₀) := by
  unfold famX1 famT
  have e := fam_pow_split (n - K) (parityOf β₀).length (by omega)
  have : terrasC (parityOf β) + 3 ^ terrasA (parityOf β) *
      (τ * 2 ^ (n - K) + 2 ^ (parityOf β₀).length * u + famRho β₀ β)
      = (terrasC (parityOf β) + 3 ^ terrasA (parityOf β) * famRho β₀ β)
        + 2 ^ (parityOf β₀).length * (3 ^ terrasA (parityOf β) *
          (τ * 2 ^ (n - K - (parityOf β₀).length) + u)) := by
    rw [e]; ring
  rw [this, Nat.add_mul_mod_self_left, fam_rho_spec]

theorem fam_X0_X1_mod {β₀ β : List Bool} (hpre : β₀ <+: β) {n K : ℕ} (τ u : ℕ)
    (hKn : K + (parityOf β₀).length ≤ n) :
    famX0 β₀ β n K τ u % 2 ^ (parityOf β₀).length
      = famX1 β₀ β n K τ u % 2 ^ (parityOf β₀).length := by
  rw [fam_X0_mod hpre, fam_X1_mod τ u hKn]

/-! ## Length and `log` -/

/-- `lenT x = ⌊log₂ x⌋` (also for `x = 0`). -/
theorem fam_lenT_eq_log (x : ℕ) : lenT x = Nat.log 2 x := by
  unfold lenT binTail
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [List.length_map, List.length_drop, List.length_reverse,
      Nat.length_digits 2 x (by norm_num) hx.ne']
    omega

lemma fam_lenT_of_bounds {x e : ℕ} (h1 : 2 ^ e ≤ x) (h2 : x < 2 ^ (e + 1)) : lenT x = e := by
  rw [fam_lenT_eq_log]; exact Nat.log_eq_of_pow_le_of_lt_pow h1 h2

lemma fam_le_lenT {x e : ℕ} (h : 2 ^ e ≤ x) : e ≤ lenT x := by
  rw [fam_lenT_eq_log]; exact Nat.le_log_of_pow_le (by norm_num) h

lemma fam_lenT_lt {x e : ℕ} (hx : x ≠ 0) (h : x < 2 ^ e) : lenT x < e := by
  rw [fam_lenT_eq_log]; exact Nat.log_lt_of_lt_pow hx h

/-- The `binTail` of the top window `τ` (`2^{K-1} ≤ τ < 2^K`) has `K - 1` digits. -/
theorem fam_binTail_tau_length {K τ : ℕ} (hK : 1 ≤ K) (hτ1 : 2 ^ (K - 1) ≤ τ) (hτ2 : τ < 2 ^ K) :
    (binTail τ).length = K - 1 :=
  fam_lenT_of_bounds hτ1 (by rwa [Nat.sub_add_cancel hK])

/-! ## (3) The digits of the starting point -/

/-- **(3) The digits of the starting point**: `bin'(x₀) = bin'(τ) · u (n-K-s' digits) · ρ (s' digits) · r' (m-s' digits) · r_{σ₀} (s' digits)`. -/
theorem fam_binTail_X0 {β₀ β : List Bool} (hpre : β₀ <+: β) {n K τ u : ℕ}
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    binTail (famX0 β₀ β n K τ u)
      = binTail τ ++ bitsMSB (n - K - (parityOf β₀).length) u
        ++ bitsMSB (parityOf β₀).length (famRho β₀ β)
        ++ bitsMSB ((parityOf β).length - (parityOf β₀).length) (famRtop β₀ β)
        ++ bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) := by
  set s := (parityOf β₀).length with hs
  set m := (parityOf β).length with hm
  have hsm : s ≤ m := fam_s_le hpre
  unfold famX0
  rw [binTail_add_mul m _ _ (fam_T_pos u hτ) (terrasR_lt _)]
  -- the Terras part
  have hr : bitsMSB m (terrasR (parityOf β))
      = bitsMSB (m - s) (famRtop β₀ β) ++ bitsMSB s (terrasR (parityOf β₀)) := by
    rw [fam_terrasR_split hpre]
    have := bitsMSB_add_mul (m - s) s (famRtop β₀ β) (terrasR (parityOf β₀))
      (fam_rtop_lt hpre) (terrasR_lt _)
    rwa [Nat.sub_add_cancel hsm] at this
  -- the part `t`
  have ht : famT β₀ β n K τ u = famRho β₀ β + 2 ^ s * (u + 2 ^ (n - K - s) * τ) := by
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
    lenT (famX0 β₀ β n K τ u) = n + (parityOf β).length - 1 := by
  have h1 := fam_T_ge (β₀ := β₀) (β := β) (n := n) u hK (by omega) hτ1
  have h2 := fam_T_lt (β := β) hKn hτ2 hu
  have hr := terrasR_lt (parityOf β)
  unfold famX0
  generalize (parityOf β).length = m at hr ⊢
  generalize famT β₀ β n K τ u = t at h1 h2 ⊢
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

/-- `3^a 2^{n-1} ≤ x₁`. -/
lemma fam_X1_ge {β₀ β : List Bool} {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) :
    3 ^ terrasA (parityOf β) * 2 ^ (n - 1) ≤ famX1 β₀ β n K τ u := by
  unfold famX1
  have := Nat.mul_le_mul_left (3 ^ terrasA (parityOf β)) (fam_T_ge (β₀ := β₀) (β := β) u hK hKn hτ1)
  omega

/-- `x₁ < 2^n 3^a`. -/
lemma fam_X1_lt {β₀ β : List Bool} {n K τ u : ℕ} (hKn : K + (parityOf β₀).length ≤ n)
    (hτ2 : τ < 2 ^ K) (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    famX1 β₀ β n K τ u < 2 ^ n * 3 ^ terrasA (parityOf β) := by
  unfold famX1
  have hc := terrasC_lt (parityOf β)
  have := Nat.mul_le_mul_left (3 ^ terrasA (parityOf β)) (Nat.succ_le_of_lt (fam_T_lt (β := β) hKn hτ2 hu))
  rw [Nat.mul_succ] at this
  rw [mul_comm (2 ^ n)]
  omega

/-- **(5) Lower bound on the length**: if `2^{m+j} ≤ 3^a` then `lenT x₁ ≥ n + m - 1 + j`. -/
theorem fam_lenT_X1_ge (β₀ β : List Bool) {n K τ : ℕ} (u j : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) (hexp : 2 ^ ((parityOf β).length + j) ≤ 3 ^ terrasA (parityOf β)) :
    n + (parityOf β).length - 1 + j ≤ lenT (famX1 β₀ β n K τ u) := by
  apply fam_le_lenT
  have h := fam_X1_ge (β₀ := β₀) (β := β) u hK hKn hτ1
  have : 2 ^ (n + (parityOf β).length - 1 + j) = 2 ^ ((parityOf β).length + j) * 2 ^ (n - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  exact le_trans (Nat.mul_le_mul_right _ hexp) h

/-- **(5) Expansion**: if `2^{m+j} ≤ 3^a` then `lenT x₁ ≥ lenT x₀ + j`. -/
theorem fam_lenT_expand (β₀ β : List Bool) {n K τ u : ℕ} (j : ℕ) (hK : 1 ≤ K)
    (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ) (hτ2 : τ < 2 ^ K)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length))
    (hexp : 2 ^ ((parityOf β).length + j) ≤ 3 ^ terrasA (parityOf β)) :
    lenT (famX0 β₀ β n K τ u) + j ≤ lenT (famX1 β₀ β n K τ u) := by
  rw [fam_lenT_X0 β₀ β hK hKn hτ1 hτ2 hu]
  exact fam_lenT_X1_ge β₀ β u j hK (by omega) hτ1 hexp

/-- **(5) Upper bound on the length**: if `3^a ≤ 2^e` then `lenT x₁ < n + e`. -/
theorem fam_lenT_X1_lt (β₀ β : List Bool) {n K τ u : ℕ} (e : ℕ)
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ) (hτ2 : τ < 2 ^ K)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) (he : 3 ^ terrasA (parityOf β) ≤ 2 ^ e) :
    lenT (famX1 β₀ β n K τ u) < n + e := by
  have hpos : famX1 β₀ β n K τ u ≠ 0 := by
    have := fam_T_pos (β₀ := β₀) (β := β) (n := n) (K := K) u hτ
    have : 1 * 1 ≤ 3 ^ terrasA (parityOf β) * famT β₀ β n K τ u :=
      Nat.mul_le_mul (Nat.one_le_pow _ _ (by norm_num)) this
    unfold famX1; omega
  apply fam_lenT_lt hpos
  rw [pow_add]
  exact lt_of_lt_of_le (fam_X1_lt hKn hτ2 hu) (Nat.mul_le_mul_left _ he)

lemma fam_three_pow_le (A m : ℕ) (h : A ≤ m) : 3 ^ A ≤ 2 ^ (2 * m) := by
  rw [pow_mul]
  calc 3 ^ A ≤ 4 ^ A := Nat.pow_le_pow_left (by norm_num) _
    _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) h
    _ = (2 ^ 2) ^ m := by norm_num

lemma fam_terrasA_le_length (σ : List Bool) : terrasA σ ≤ σ.length := by
  rw [terrasA_eq]; exact List.count_le_length

/-- **(5) Upper bound on the length**: `lenT x₁ < n + 2m`. -/
theorem fam_lenT_X1_lt_two (β₀ β : List Bool) {n K τ u : ℕ}
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ) (hτ2 : τ < 2 ^ K)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    lenT (famX1 β₀ β n K τ u) < n + 2 * (parityOf β).length :=
  fam_lenT_X1_lt β₀ β _ hKn hτ hτ2 hu (fam_three_pow_le _ _ (fam_terrasA_le_length _))

/-- Lower bound on the starting point, `2^{n+m-1} ≤ x₀` (`x₀` can be taken at least `N`). -/
theorem fam_X0_ge (β₀ β : List Bool) {n K τ : ℕ} (u : ℕ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hτ1 : 2 ^ (K - 1) ≤ τ) :
    2 ^ (n + (parityOf β).length - 1) ≤ famX0 β₀ β n K τ u := by
  have h1 := fam_T_ge (β₀ := β₀) (β := β) (n := n) u hK hKn hτ1
  unfold famX0
  generalize (parityOf β).length = m
  generalize famT β₀ β n K τ u = t at h1 ⊢
  have : 2 ^ (n + m - 1) = 2 ^ m * 2 ^ (n - 1) := by rw [← pow_add]; congr 1; omega
  rw [this]
  have := Nat.mul_le_mul_left (2 ^ m) h1
  omega

/-! ## Counting blocks -/

/-- The length, odd steps and even steps of `parityOf` of a block sequence (`X'`: 8, 5, 3; `Y'`: 11, 7, 4). -/
theorem fam_parityOf_counts (β : List Bool) :
    (parityOf β).length = 8 * β.count true + 11 * β.count false ∧
    (parityOf β).count true = 5 * β.count true + 7 * β.count false ∧
    (parityOf β).count false = 3 * β.count true + 4 * β.count false := by
  induction β with
  | nil => simp [parityOf]
  | cons x β ih =>
    have e : parityOf (x :: β) = (if x then blkX else blkY) ++ parityOf β := by
      simp [parityOf]
    rw [e, List.length_append, List.count_append, List.count_append]
    obtain ⟨h1, h2, h3⟩ := ih
    cases x <;> simp [blkX, blkY, h1, h2, h3] <;> omega

theorem fam_length_eq_count (β : List Bool) : β.length = β.count true + β.count false := by
  induction β with
  | nil => simp
  | cons x β ih =>
    rw [List.length_cons, List.count_cons, List.count_cons, ih]
    cases x <;> simp <;> omega

/-- Each block has at least 5 odd steps: `a_σ ≥ 5 |β|` (so `a ≥ 1` if `β ≠ []`). -/
theorem fam_terrasA_ge (β : List Bool) : 5 * β.length ≤ terrasA (parityOf β) := by
  rw [terrasA_eq, (fam_parityOf_counts β).2.1, fam_length_eq_count]
  omega

end Collatz.Arctic
