/-
# Lemma D.6: partial sums of a geometric sequence cover the residues modulo `3^M`

The statement: let `μ ≥ 2` be an integer prime to 3 and `M ≥ 1`. If `r ≥ R_cov(M)`,
then for every `t ∈ ℤ/3^M` there is `J ⊆ \{0, …, r-1\}` with `Σ_{m∈J} μ^m ≡ t (mod 3^M)`, where `R_cov(M) = O(μ²M²)`.

The Lean form (`cover`): the residues are covered if `r ≥ 8 μ² M²`. This is of the same order as `R_cov(M) = B ⌈M ln 3/(-ln κ_μ)⌉` of an earlier argument (`B = ⌊M log_μ 3⌋ + 1`,
`κ_μ = cos(π/(2μ))`), with the constants chosen again in an elementary way:
* the length of an interval of indices is `B := 2M` (the run lemma works because `μ^{2M} ≥ 4^M > 3^M`);
* the factor per interval is `κ := 1 - 1/(2μ²)` (`cos(π/μ) ≤ 1 - 2/μ²` from Jordan's inequality `sin x ≥ 2x/π`, and
  `|1 + e^{iθ}|² = 2 + 2cos θ`);
* the number of intervals is `T := 4μ²M` (`κ^{2μ²} ≤ 1/2` by Bernoulli's inequality, so `κ^T ≤ 4^{-M}`).
The proof is the Fourier argument of the paper: `3^M N(t) = Σ_ν e(-νt/3^M) Π_{m<r}(1 + e(νμ^m/3^M))` (`ZMod.stdAddChar` and
`AddChar.sum_mulShift`); by the run lemma the terms with `ν ≠ 0` are at most `2^r κ^T`, and `(3^M - 1) 4^{-M} < 1`.
-/
import Mathlib

namespace Collatz.Arctic.NatQ5.Rigid

open Complex Finset

/-! ## §1 Real inequalities -/

/-- The `2μ²`th power of `κ := 1 - 1/(2μ²)` is at most `1/2` (Bernoulli). -/
theorem kappa_pow_le (μ : ℕ) (hμ : 1 ≤ μ) :
    (1 - 1 / (2 * (μ : ℝ) ^ 2)) ^ (2 * μ ^ 2) ≤ 1 / 2 := by
  set a : ℝ := 1 / (2 * (μ : ℝ) ^ 2) with ha
  have hμ' : (1 : ℝ) ≤ μ := by exact_mod_cast hμ
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one (by positivity)]; nlinarith
  set n := 2 * μ ^ 2 with hn
  have hna : (n : ℝ) * a = 1 := by
    rw [hn, ha]; push_cast; field_simp
  have h1 : 2 ≤ (1 + a) ^ n := by
    have := one_add_mul_le_pow (a := a) (by linarith) n
    linarith
  have h2 : (1 - a) ^ n * (1 + a) ^ n ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h3 : 0 ≤ (1 - a) ^ n := pow_nonneg (by linarith) _
  have h4 : 0 < (1 + a) ^ n := by positivity
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-- `cos(π/μ) ≤ 1 - 2/μ²` (`μ ≥ 2`, Jordan's inequality). -/
theorem cos_pi_div_le (μ : ℕ) (hμ : 2 ≤ μ) : Real.cos (Real.pi / μ) ≤ 1 - 2 / (μ : ℝ) ^ 2 := by
  have hμ' : (2 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hμ0 : (0 : ℝ) < μ := by linarith
  set u := Real.pi / (2 * μ) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ≤ Real.pi / 2 := by
    rw [hu, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hsin : 1 / (μ : ℝ) ≤ Real.sin u := by
    have := Real.mul_le_sin hu0 hu2
    have e : 2 / Real.pi * u = 1 / μ := by
      rw [hu]; field_simp
    linarith
  have hcos : Real.cos (Real.pi / μ) = 1 - 2 * Real.sin u ^ 2 := by
    have e : Real.pi / μ = 2 * u := by rw [hu]; field_simp
    rw [e, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hcos]
  have h1 : (1 / (μ : ℝ)) ^ 2 ≤ Real.sin u ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin 2
  have e2 : 2 / (μ : ℝ) ^ 2 = 2 * (1 / (μ : ℝ)) ^ 2 := by field_simp
  rw [e2]
  linarith

/-- If `cos θ ≤ 1 - 2/μ²`, then `‖1 + e^{iθ}‖ ≤ 2(1 - 1/(2μ²))`. -/
theorem norm_one_add_exp_le {μ : ℝ} (hμ : 1 ≤ μ) {θ : ℝ} (h : Real.cos θ ≤ 1 - 2 / μ ^ 2) :
    ‖1 + exp (θ * I)‖ ≤ 2 * (1 - 1 / (2 * μ ^ 2)) := by
  have hsq : ‖1 + exp (θ * I)‖ ^ 2 = 2 + 2 * Real.cos θ := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.add_im,
      Complex.one_im, Complex.exp_ofReal_mul_I_im, zero_add]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hμ2 : (1 : ℝ) ≤ μ ^ 2 := by nlinarith
  have hrhs : 0 ≤ 2 * (1 - 1 / (2 * μ ^ 2)) := by
    have : 1 / (2 * μ ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  refine (sq_le_sq₀ (norm_nonneg _) hrhs).mp ?_
  rw [hsq]
  have e : (2 * (1 - 1 / (2 * μ ^ 2))) ^ 2 = 4 - 4 / μ ^ 2 + 1 / μ ^ 4 := by
    field_simp; ring
  rw [e]
  have : 0 ≤ 1 / μ ^ 4 := by positivity
  have e2 : 2 * (1 - 2 / μ ^ 2) = 2 - 4 / μ ^ 2 := by ring
  nlinarith

/-! ## §2 The run lemma -/

section Run

variable {q : ℕ} [NeZero q] (μ : ℕ)

/-- Multiplying a small representative by `μ` gives a representative again. -/
theorem valMinAbs_mul_of_small {x : ZMod q} (h : 2 * μ * |x.valMinAbs| < q) :
    ((μ : ZMod q) * x).valMinAbs = μ * x.valMinAbs := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨by simp [ZMod.coe_valMinAbs], ?_⟩
  have h1 : |(μ : ℤ) * x.valMinAbs * 2| < q := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ μ)]
    simp only [abs_two]; linarith
  rw [abs_lt] at h1
  exact ⟨h1.1, h1.2.le⟩

end Run

/-- **The run lemma**: if `q ≤ μ^B` (`B ≥ 1`), `μ` is a unit modulo `q` and `ν ≠ 0`, then for every `a` there is `i < B` such that
the representative of `ν μ^{a+i}` has absolute value at least `q/(2μ)`. -/
theorem run_far {q : ℕ} [NeZero q] {μ B : ℕ} (hB : 1 ≤ B) (hqB : q ≤ μ ^ B) (hu : IsUnit (μ : ZMod q))
    {ν : ZMod q} (hν : ν ≠ 0) (a : ℕ) :
    ∃ i < B, (q : ℤ) ≤ 2 * μ * |(ν * (μ : ZMod q) ^ (a + i)).valMinAbs| := by
  by_contra hc
  push Not at hc
  set v : ℕ → ℤ := fun i => (ν * (μ : ZMod q) ^ (a + i)).valMinAbs with hv
  have hstep : ∀ i, i < B → v (i + 1) = μ * v i := by
    intro i hi
    have e : ν * (μ : ZMod q) ^ (a + (i + 1)) = (μ : ZMod q) * (ν * (μ : ZMod q) ^ (a + i)) := by
      rw [← add_assoc, pow_succ]; ring
    simp only [hv]
    rw [e]
    exact valMinAbs_mul_of_small μ (hc i hi)
  have habs : ∀ i, i < B → |v i| = (μ : ℤ) ^ i * |v 0| := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [hstep i (by omega), abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ μ), ih (by omega),
        pow_succ]
      ring
  have hv0 : v 0 ≠ 0 := by
    simp only [hv, add_zero]
    rw [Ne, ZMod.valMinAbs_eq_zero]
    intro h0
    apply hν
    have hu' : IsUnit ((μ : ZMod q) ^ a) := hu.pow a
    exact (hu'.mul_left_eq_zero).mp h0
  have hlast := hc (B - 1) (by omega)
  rw [show (ν * (μ : ZMod q) ^ (a + (B - 1))).valMinAbs = v (B - 1) from rfl,
    habs (B - 1) (by omega)] at hlast
  have h1 : (1 : ℤ) ≤ |v 0| := Int.one_le_abs hv0
  have h2 : (μ : ℤ) ^ B ≤ 2 * μ * ((μ : ℤ) ^ (B - 1) * |v 0|) := by
    have e : (μ : ℤ) ^ B = μ * μ ^ (B - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]
    have : (0 : ℤ) ≤ μ * μ ^ (B - 1) := by positivity
    nlinarith
  have h3 : (q : ℤ) ≤ (μ : ℤ) ^ B := by exact_mod_cast hqB
  linarith

/-! ## §3 Bounding the product -/

theorem prod_window_le {f : ℕ → ℝ} {κ : ℝ} (hf0 : ∀ m, 0 ≤ f m) (hf2 : ∀ m, f m ≤ 2) (hκ0 : 0 ≤ κ)
    {B T : ℕ} (hwin : ∀ j < T, ∃ i < B, f (j * B + i) ≤ 2 * κ) (e : ℕ) :
    ∏ m ∈ range (T * B + e), f m ≤ 2 ^ (T * B + e) * κ ^ T := by
  have hblocks : ∀ T' ≤ T, ∏ m ∈ range (T' * B), f m ≤ 2 ^ (T' * B) * κ ^ T' := by
    intro T'
    induction T' with
    | zero => intro _; simp
    | succ T' ih =>
      intro hT'
      rw [Nat.succ_mul, prod_range_add]
      obtain ⟨i0, hi0, hfi0⟩ := hwin T' (by omega)
      have hwinP : ∏ x ∈ range B, f (T' * B + x) ≤ 2 ^ B * κ := by
        rw [← mul_prod_erase _ _ (mem_range.mpr hi0)]
        have hrest : ∏ x ∈ (range B).erase i0, f (T' * B + x) ≤ 2 ^ (B - 1) := by
          have := prod_le_prod₀ (s := (range B).erase i0) (f := fun x => f (T' * B + x))
            (g := fun _ => (2 : ℝ)) (fun x _ => hf0 _) (fun x _ => hf2 _)
          rwa [prod_const, card_erase_of_mem (mem_range.mpr hi0), card_range] at this
        calc f (T' * B + i0) * ∏ x ∈ (range B).erase i0, f (T' * B + x)
            ≤ (2 * κ) * 2 ^ (B - 1) :=
              mul_le_mul hfi0 hrest (prod_nonneg fun x _ => hf0 _) (by positivity)
          _ = 2 ^ B * κ := by
              rw [show B = B - 1 + 1 by omega, pow_succ]; simp; ring
      calc (∏ m ∈ range (T' * B), f m) * ∏ x ∈ range B, f (T' * B + x)
          ≤ (2 ^ (T' * B) * κ ^ T') * (2 ^ B * κ) :=
            mul_le_mul (ih (by omega)) hwinP (prod_nonneg fun x _ => hf0 _) (by positivity)
        _ = 2 ^ (T' * B + B) * κ ^ (T' + 1) := by rw [pow_add, pow_succ]; ring
  rw [prod_range_add]
  have htail : ∏ x ∈ range e, f (T * B + x) ≤ 2 ^ e := by
    have := prod_le_prod₀ (s := range e) (f := fun x => f (T * B + x)) (g := fun _ => (2 : ℝ))
      (fun x _ => hf0 _) (fun x _ => hf2 _)
    rwa [prod_const, card_range] at this
  calc (∏ m ∈ range (T * B), f m) * ∏ x ∈ range e, f (T * B + x)
      ≤ (2 ^ (T * B) * κ ^ T) * 2 ^ e :=
        mul_le_mul (hblocks T le_rfl) htail (prod_nonneg fun x _ => hf0 _) (by positivity)
    _ = 2 ^ (T * B + e) * κ ^ T := by rw [pow_add]; ring

/-! ## §4 Lemma D.6 -/

theorem addChar_map_sum {q : ℕ} (ψ : AddChar (ZMod q) ℂ) {ι : Type*} (s : Finset ι) (f : ι → ZMod q) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The body of Lemma D.6 (with the modulus `q = 3^M` as a variable). -/
theorem cover_aux {μ M q : ℕ} (hμ : 2 ≤ μ) (hμ3 : Nat.Coprime μ 3) (hM : 1 ≤ M) (hq : q = 3 ^ M) {r : ℕ}
    (hr : 8 * μ ^ 2 * M ^ 2 ≤ r) (t : ZMod q) :
    ∃ J ⊆ range r, ∑ m ∈ J, (μ : ZMod q) ^ m = t := by
  classical
  have hqpos : 0 < q := by rw [hq]; positivity
  have : NeZero q := ⟨hqpos.ne'⟩
  have hu : IsUnit (μ : ZMod q) := by
    rw [hq]; exact (ZMod.unitOfCoprime μ (Nat.Coprime.pow_right M hμ3)).isUnit
  have hqB : q ≤ μ ^ (2 * M) := by
    rw [hq, pow_mul]
    exact Nat.pow_le_pow_left (by nlinarith : 3 ≤ μ ^ 2) M
  set ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar with hψ
  have hprim : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar q
  by_contra hno
  push Not at hno
  set s : Finset ℕ → ZMod q := fun J => ∑ m ∈ J, (μ : ZMod q) ^ m
  set F : ZMod q → ℂ := fun ν => ψ (-(ν * t)) * ∏ m ∈ range r, (1 + ψ (ν * (μ : ZMod q) ^ m))
  -- The Fourier identity: `Σ_ν F ν = q N(t) = 0`
  have hzero : ∑ ν, F ν = 0 := by
    have h1 : ∀ ν, F ν = ∑ J ∈ (range r).powerset, ψ (ν * (s J - t)) := by
      intro ν
      simp only [F, prod_one_add, mul_sum]
      refine sum_congr rfl fun J _ => ?_
      rw [← addChar_map_sum, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [s, mul_sum, mul_sub]
      ring
    simp_rw [h1]
    rw [sum_comm]
    refine sum_eq_zero fun J hJ => ?_
    rw [AddChar.sum_mulShift _ hprim, ite_eq_right (sub_ne_zero.mpr (hno J (mem_powerset.mp hJ))),
      Nat.cast_zero]
  -- The term `ν = 0`
  have hF0 : F 0 = 2 ^ r := by
    simp only [F, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul]
    rw [prod_const, card_range]; norm_num
  -- Bounding the terms `ν ≠ 0`
  set κ : ℝ := 1 - 1 / (2 * (μ : ℝ) ^ 2)
  have hμR : (2 : ℝ) ≤ μ := by exact_mod_cast hμ
  have hκ0 : 0 ≤ κ := by
    have : 1 / (2 * (μ : ℝ) ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have hnormψ : ∀ x, ‖ψ x‖ = 1 := by
    intro x
    rw [hψ, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  have hfar : ∀ x : ZMod q, (q : ℤ) ≤ 2 * μ * |x.valMinAbs| → ‖1 + ψ x‖ ≤ 2 * κ := by
    intro x hx
    set v := x.valMinAbs
    have hψx : ψ x = exp ((2 * Real.pi * v / q : ℝ) * I) := by
      rw [← ZMod.coe_valMinAbs x, hψ, ZMod.stdAddChar_coe]
      congr 1; push_cast; ring
    rw [hψx]
    refine norm_one_add_exp_le (by linarith) ?_
    have hmem := x.valMinAbs_mem_Ioc
    have hvq : |v| * 2 ≤ (q : ℤ) := by
      have : |v * 2| ≤ (q : ℤ) := abs_le.mpr ⟨hmem.1.le, hmem.2⟩
      rwa [abs_mul, abs_two] at this
    have hvqR : |(v : ℝ)| * 2 ≤ q := by
      have := (Int.cast_le (R := ℝ)).mpr hvq
      push_cast at this; exact this
    have hvμR : (q : ℝ) ≤ 2 * μ * |(v : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).mpr hx
      push_cast at this; exact this
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hpi := Real.pi_pos
    have habsθ : |2 * Real.pi * v / q| = 2 * Real.pi * |(v : ℝ)| / q := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
        abs_of_pos hqR]
    have hlo : Real.pi / μ ≤ |2 * Real.pi * v / q| := by
      rw [habsθ, div_le_div_iff₀ (by positivity) hqR]
      nlinarith
    have hhi : |2 * Real.pi * v / q| ≤ Real.pi := by
      rw [habsθ, div_le_iff₀ hqR]
      nlinarith
    calc Real.cos (2 * Real.pi * v / q) = Real.cos |2 * Real.pi * v / q| := (Real.cos_abs _).symm
      _ ≤ Real.cos (Real.pi / μ) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hhi hlo
      _ ≤ 1 - 2 / (μ : ℝ) ^ 2 := cos_pi_div_le μ hμ
  have hbound : ∀ ν : ZMod q, ν ≠ 0 → ‖F ν‖ ≤ 2 ^ r * κ ^ (4 * μ ^ 2 * M) := by
    intro ν hν
    have hwin : ∀ j < 4 * μ ^ 2 * M, ∃ i < 2 * M,
        ‖1 + ψ (ν * (μ : ZMod q) ^ (j * (2 * M) + i))‖ ≤ 2 * κ := by
      intro j _
      obtain ⟨i, hi, hfar'⟩ := run_far (by omega) hqB hu hν (j * (2 * M))
      exact ⟨i, hi, hfar _ hfar'⟩
    have hr' : r = 4 * μ ^ 2 * M * (2 * M) + (r - 4 * μ ^ 2 * M * (2 * M)) := by
      have : 4 * μ ^ 2 * M * (2 * M) = 8 * μ ^ 2 * M ^ 2 := by ring
      omega
    have hprod := prod_window_le (f := fun m => ‖1 + ψ (ν * (μ : ZMod q) ^ m)‖)
      (fun m => norm_nonneg _)
      (fun m => (norm_add_le _ _).trans (by rw [norm_one, hnormψ]; norm_num)) hκ0 hwin
      (r - 4 * μ ^ 2 * M * (2 * M))
    rw [← hr'] at hprod
    simp only [F, norm_mul, hnormψ, one_mul, norm_prod]
    exact hprod
  -- Contradiction
  have hκT : κ ^ (4 * μ ^ 2 * M) ≤ (1 / 4) ^ M := by
    have e : 4 * μ ^ 2 * M = (2 * μ ^ 2) * (2 * M) := by ring
    rw [e, pow_mul]
    calc (κ ^ (2 * μ ^ 2)) ^ (2 * M) ≤ (1 / 2 : ℝ) ^ (2 * M) :=
          pow_le_pow_left₀ (pow_nonneg hκ0 _) (kappa_pow_le μ (by omega)) _
      _ = (1 / 4) ^ M := by rw [pow_mul]; norm_num
  have hsplit : F 0 = -∑ ν ∈ univ.erase 0, F ν := by
    rw [← add_sum_erase _ _ (mem_univ (0 : ZMod q))] at hzero
    linear_combination hzero
  have hle : (2 : ℝ) ^ r ≤ ((q : ℝ) - 1) * (2 ^ r * (1 / 4) ^ M) := by
    have h1 : ‖F 0‖ = 2 ^ r := by rw [hF0]; simp
    have h2 : ‖F 0‖ ≤ ∑ ν ∈ univ.erase 0, ‖F ν‖ := by
      rw [hsplit, norm_neg]; exact norm_sum_le _ _
    have h3 : ∑ ν ∈ univ.erase (0 : ZMod q), ‖F ν‖ ≤
        ∑ _ν ∈ univ.erase (0 : ZMod q), 2 ^ r * (1 / 4 : ℝ) ^ M :=
      sum_le_sum fun ν hν => (hbound ν (ne_of_mem_erase hν)).trans
        (mul_le_mul_of_nonneg_left hκT (by positivity))
    rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, ZMod.card, nsmul_eq_mul] at h3
    have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at h3
    linarith
  have hq4 : ((q : ℝ) - 1) * (1 / 4) ^ M < 1 := by
    have h34 : (3 : ℝ) ^ M < 4 ^ M := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have : (q : ℝ) = 3 ^ M := by rw [hq]; push_cast; ring
    rw [this, one_div_pow, mul_one_div, div_lt_one (by positivity)]
    linarith
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  nlinarith

/-- **Lemma D.6**: if `μ ≥ 2` is prime to 3, `M ≥ 1` and `r ≥ 8μ²M²`, then every residue class modulo `3^M` is a partial sum of `μ^0, …, μ^{r-1}`. -/
theorem cover {μ M : ℕ} (hμ : 2 ≤ μ) (hμ3 : Nat.Coprime μ 3) (hM : 1 ≤ M) {r : ℕ}
    (hr : 8 * μ ^ 2 * M ^ 2 ≤ r) (t : ZMod (3 ^ M)) :
    ∃ J ⊆ range r, ∑ m ∈ J, (μ : ZMod (3 ^ M)) ^ m = t :=
  cover_aux hμ hμ3 hM rfl hr t

end Collatz.Arctic.NatQ5.Rigid
