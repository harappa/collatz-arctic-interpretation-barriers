/-
Probabilistic ingredients (part 2) of Theorem B.7 (KEY) in the swap argument: the law of `w` and the number of mixed coins.

* `km_nine_dvd`, `km_nine_pow`: `9^{2^{V-3}} = 1` modulo `2^V` (`V ≥ 3`) (the identity `9^{2^i} = 1 + 2^{i+3}u_i` from the proof of `SpecNine`).
* `km_i9_*`: powers of `9^{-1} = (3^{-1})^2`. `(9^{-1})^Y` depends only on `Y mod 2^{V-3}`.
* `km_val_mod_one`, `km_i3_pow_odd`, `km_i9_pow_mod8`: `3^{-a}` is odd and `9^{-y} ≡ 1 (mod 8)` (ring homomorphism to modulus `2^k`).
* `km_coset`, `km_coset_avg`: **how `SpecNine` is used** (order of 9). `y ↦ 9^{-y}` is a bijection from `range 2^{V-3}` onto the residue class
  `{w ≡ 1 (mod 8)}`.
* `km_w_bound`: **step (c) of the proof of Theorem B.7**. For the number `Y` of `Y'` in the early part, the expectation of a function (`0 ≤ Φ ≤ B`) of `w = 9^{-Y}`
  is at most the average over the residue class `+ B · 2(1 - N(3/10)^N)^{⌊n/N⌋}` (`N = 2^{V-3}`, the Doeblin bound `SpecDoeblin`).
  As in the paper, the factor `3^{-(a(β₀) + 5n_e)}` is absorbed into `ω_j`, so that
  `w = 9^{-Y}` (the residue class is `1 mod 8` independently of `β₀`).
* `km_coin_avg`: `E 2^{-M} = (79/100)^I` in **step (d) of the proof of Theorem B.7** (the coins are independent, and a coin is mixed with probability 21/50).
-/
import CollatzProof.Arctic.KeyMain
import CollatzProof.Arctic.KeySpec

namespace Collatz.Arctic

open Finset

/-! ### The law of `w` (use of `SpecNine` and `SpecDoeblin`) -/

/-- `9^{2^i} ≡ 1 (mod 2^{i+3})`. -/
lemma km_nine_dvd (i : ℕ) : (2 : ℤ) ^ (i + 3) ∣ 9 ^ (2 ^ i) - 1 := by
  induction i with
  | zero => norm_num
  | succ i ih =>
    have h2 : (2 : ℤ) ∣ 9 ^ (2 ^ i) + 1 := by
      have : (2 : ℤ) ∣ 9 ^ (2 ^ i) - 1 := dvd_trans (dvd_pow_self 2 (by omega)) ih
      have h' : (9 : ℤ) ^ (2 ^ i) + 1 = (9 ^ (2 ^ i) - 1) + 2 := by ring
      rw [h']; exact dvd_add this (dvd_refl 2)
    have e : (9 : ℤ) ^ (2 ^ (i + 1)) - 1 = (9 ^ (2 ^ i) - 1) * (9 ^ (2 ^ i) + 1) := by
      rw [pow_succ, pow_mul]; ring
    rw [e, show i + 1 + 3 = (i + 3) + 1 by ring, pow_succ]
    exact mul_dvd_mul ih h2

/-- `9^{2^{V-3}} = 1` modulo `2^V` (`V ≥ 3`). -/
lemma km_nine_pow (V : ℕ) (hV : 3 ≤ V) : (9 : ZMod (2 ^ V)) ^ (2 ^ (V - 3)) = 1 := by
  have h := km_nine_dvd (V - 3)
  rw [Nat.sub_add_cancel hV] at h
  have h2 : (((9 : ℤ) ^ (2 ^ (V - 3)) - 1 : ℤ) : ZMod (2 ^ V)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  push_cast at h2
  linear_combination h2

lemma km_nine_inv (V : ℕ) : (9 : ZMod (2 ^ V)) * ((3 : ZMod (2 ^ V))⁻¹) ^ 2 = 1 := by
  have h := km_three_inv V
  linear_combination (3 * (3 : ZMod (2 ^ V))⁻¹ + 1) * h

lemma km_i9_pow_N (V : ℕ) (hV : 3 ≤ V) : (((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ (2 ^ (V - 3)) = 1 := by
  calc (((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ (2 ^ (V - 3))
      = (((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ (2 ^ (V - 3)) * (9 : ZMod (2 ^ V)) ^ (2 ^ (V - 3)) := by
        rw [km_nine_pow V hV, mul_one]
    _ = ((9 : ZMod (2 ^ V)) * ((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ (2 ^ (V - 3)) := by ring
    _ = 1 := by rw [km_nine_inv, one_pow]

lemma km_i9_mod (V : ℕ) (hV : 3 ≤ V) (Y : ℕ) :
    (((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ Y = (((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ (Y % 2 ^ (V - 3)) := by
  conv_lhs => rw [← Nat.div_add_mod Y (2 ^ (V - 3))]
  rw [pow_add, pow_mul, km_i9_pow_N V hV, one_pow, one_mul]

/-- If an element `x` reduces to 1 modulo `2^k` (`k ≤ V`), its inverse `y` (`x y = 1`) has `val` equal to 1 modulo `2^k`. -/
lemma km_val_mod_one (V k : ℕ) (hk : k ≤ V) (h1k : 1 ≤ k) (x y : ZMod (2 ^ V)) (hxy : x * y = 1)
    (hx : ZMod.castHom (pow_dvd_pow 2 hk) (ZMod (2 ^ k)) x = 1) : y.val % 2 ^ k = 1 := by
  have h := congrArg (ZMod.castHom (pow_dvd_pow 2 hk) (ZMod (2 ^ k))) hxy
  rw [map_mul, map_one, hx, one_mul] at h
  have h2 : (ZMod.castHom (pow_dvd_pow 2 hk) (ZMod (2 ^ k)) y).val = y.val % 2 ^ k := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [← h2, h, ZMod.val_one'']
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h1k
  omega

/-- `(3^{-1})^a` is odd. -/
lemma km_i3_pow_odd (V : ℕ) (hV : 1 ≤ V) (a : ℕ) : (((3 : ZMod (2 ^ V))⁻¹) ^ a).val % 2 = 1 := by
  have h := km_val_mod_one V 1 hV le_rfl ((3 : ZMod (2 ^ V)) ^ a) (((3 : ZMod (2 ^ V))⁻¹) ^ a)
    (by rw [← mul_pow, km_three_inv, one_pow])
    (by rw [map_pow, map_ofNat, show (3 : ZMod (2 ^ 1)) = 1 by decide, one_pow])
  simpa using h

/-- `(9^{-1})^y ≡ 1 (mod 8)`. -/
lemma km_i9_pow_mod8 (V : ℕ) (hV : 3 ≤ V) (y : ℕ) :
    ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ y).val % 8 = 1 := by
  have h := km_val_mod_one V 3 hV (by norm_num) ((9 : ZMod (2 ^ V)) ^ y)
    ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ y)
    (by rw [← mul_pow, km_nine_inv, one_pow])
    (by rw [map_pow, map_ofNat, show (9 : ZMod (2 ^ 3)) = 1 by decide, one_pow])
  simpa using h

/-- **How `SpecNine` is used**: `y ↦ 9^{-y}` is a bijection from `range 2^{V-3}` onto the residue class `{w ≡ 1 (mod 8)}`. -/
theorem km_coset (hN : SpecNine) (V : ℕ) (hV : 3 ≤ V) :
    Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1) =
      (Finset.range (2 ^ (V - 3))).image (fun y => (((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ y) ∧
    Set.InjOn (fun y => (((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ y) ↑(Finset.range (2 ^ (V - 3))) := by
  set i9 := ((3 : ZMod (2 ^ V))⁻¹) ^ 2 with hi9
  have hB := hN V hV
  have h9 : ∀ a : ℕ, (9 : ZMod (2 ^ V)) ^ a * i9 ^ a = 1 := by
    intro a; rw [← mul_pow, hi9, km_nine_inv, one_pow]
  have hval : ∀ a : ℕ, ((9 : ZMod (2 ^ V)) ^ a).val = 9 ^ a % 2 ^ V := by
    intro a
    have : (9 : ZMod (2 ^ V)) ^ a = ((9 ^ a : ℕ) : ZMod (2 ^ V)) := by push_cast; rfl
    rw [this, ZMod.val_natCast]
  have hinj : Set.InjOn (fun y => i9 ^ y) ↑(Finset.range (2 ^ (V - 3))) := by
    intro a ha b hb hab
    simp only at hab
    have e9 : (9 : ZMod (2 ^ V)) ^ a = 9 ^ b := by
      calc (9 : ZMod (2 ^ V)) ^ a = 9 ^ a * (9 ^ b * i9 ^ b) := by rw [h9, mul_one]
        _ = 9 ^ b * (9 ^ a * i9 ^ a) := by rw [hab]; ring
        _ = 9 ^ b := by rw [h9, mul_one]
    have := congrArg ZMod.val e9
    rw [hval, hval] at this
    exact hB.injOn ha hb this
  refine ⟨?_, hinj⟩
  have hsub : (Finset.range (2 ^ (V - 3))).image (fun y => i9 ^ y) ⊆
      Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1) := by
    intro w hw
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact km_i9_pow_mod8 V hV y
  have hcardG : (Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1)).card ≤ 2 ^ (V - 3) := by
    rw [← Finset.card_image_of_injective _ (ZMod.val_injective (2 ^ V))]
    calc ((Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1)).image ZMod.val).card
        ≤ ((Finset.range (2 ^ (V - 3))).image (fun y : ℕ => 9 ^ y % 2 ^ V)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          obtain ⟨y, hy, hyx⟩ := hB.surjOn ⟨ZMod.val_lt w, hw⟩
          exact Finset.mem_image.mpr ⟨y, hy, hyx⟩
      _ ≤ (Finset.range (2 ^ (V - 3))).card := Finset.card_image_le
      _ = 2 ^ (V - 3) := Finset.card_range _
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  exact hcardG

/-- The average over the residue class is the average over `y < 2^{V-3}`. -/
theorem km_coset_avg (hN : SpecNine) (V : ℕ) (hV : 3 ≤ V) (Φ : ZMod (2 ^ V) → ℝ) :
    (∑ w ∈ Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1), Φ w) /
        ((Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1)).card : ℝ) =
      (1 / (2 ^ (V - 3) : ℕ)) * ∑ y ∈ Finset.range (2 ^ (V - 3)), Φ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ y) := by
  obtain ⟨hG, hinj⟩ := km_coset hN V hV
  rw [hG, Finset.sum_image hinj, Finset.card_image_of_injOn hinj, Finset.card_range]
  ring

/-- **Step (c) of the proof of Theorem B.7**: for the number `Y` of `Y'` in the early part, the expectation of a function of `9^{-Y}` is within
`B · 2(1 - N(3/10)^N)^{⌊n/N⌋}` (`N = 2^{V-3}`) of the average over the residue class. -/
theorem km_w_bound (hN : SpecNine) (hD : SpecDoeblin) (V : ℕ) (hV : 3 ≤ V) (Φ : ZMod (2 ^ V) → ℝ)
    (B : ℝ) (hΦ0 : ∀ w, 0 ≤ Φ w) (hΦB : ∀ w, Φ w ≤ B) (n : ℕ) :
    ∑ β ∈ blockChoices n, (wtβ β : ℝ) * Φ ((((3 : ZMod (2 ^ V))⁻¹) ^ 2) ^ β.count false) ≤
      (∑ w ∈ Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1), Φ w) /
        ((Finset.univ.filter (fun w : ZMod (2 ^ V) => w.val % 8 = 1)).card : ℝ) +
      B * (2 * (1 - ((2 ^ (V - 3) : ℕ) : ℝ) * (3 / 10 : ℝ) ^ (2 ^ (V - 3))) ^ (n / 2 ^ (V - 3))) := by
  set N := 2 ^ (V - 3) with hNdef
  set i9 := ((3 : ZMod (2 ^ V))⁻¹) ^ 2 with hi9
  have hNpos : 0 < N := by positivity
  rw [km_coset_avg hN V hV Φ]
  have hB0 : 0 ≤ B := le_trans (hΦ0 0) (hΦB 0)
  -- split by the residue modulo `N`
  have hfib : ∑ β ∈ blockChoices n, (wtβ β : ℝ) * Φ (i9 ^ β.count false) =
      ∑ y ∈ Finset.range N, (∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y),
        (wtβ β : ℝ)) * Φ (i9 ^ y) := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range N) (g := fun β => β.count false % N)
      (fun β _ => Finset.mem_range.mpr (Nat.mod_lt _ hNpos))]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β hβ => ?_)
    rw [(Finset.mem_filter.mp hβ).2.symm, hi9, ← km_i9_mod V hV]
  rw [hfib]
  have hdoe := hD N n (by omega)
  have hterm : ∀ y ∈ Finset.range N,
      (∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y), (wtβ β : ℝ)) * Φ (i9 ^ y) ≤
        (1 / (N : ℝ)) * Φ (i9 ^ y) +
          |∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y), (wtβ β : ℝ) - 1 / N| * B := by
    intro y _
    set p := ∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y), (wtβ β : ℝ)
    have h1 : (p - 1 / N) * Φ (i9 ^ y) ≤ |p - 1 / N| * B := by
      calc (p - 1 / N) * Φ (i9 ^ y) ≤ |p - 1 / N| * Φ (i9 ^ y) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (hΦ0 _)
        _ ≤ |p - 1 / N| * B := mul_le_mul_of_nonneg_left (hΦB _) (abs_nonneg _)
    linarith
  calc ∑ y ∈ Finset.range N, (∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y),
        (wtβ β : ℝ)) * Φ (i9 ^ y)
      ≤ ∑ y ∈ Finset.range N, ((1 / (N : ℝ)) * Φ (i9 ^ y) +
          |∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y), (wtβ β : ℝ) - 1 / N| * B) :=
        Finset.sum_le_sum hterm
    _ = (1 / (N : ℝ)) * ∑ y ∈ Finset.range N, Φ (i9 ^ y) +
          (∑ y ∈ Finset.range N,
            |∑ β ∈ (blockChoices n).filter (fun β => β.count false % N = y), (wtβ β : ℝ) - 1 / N|) * B := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    _ ≤ (1 / (N : ℝ)) * ∑ y ∈ Finset.range N, Φ (i9 ^ y) +
          (2 * (1 - (N : ℝ) * (3 / 10 : ℝ) ^ N) ^ (n / N)) * B := by
        have := mul_le_mul_of_nonneg_right hdoe hB0
        linarith
    _ = _ := by ring

/-! ### The number of mixed coins -/

/-- `E 2^{-M} = (79/100)^I` in **step (d) of the proof of Theorem B.7** (the coins are independent, and a coin is mixed with probability 21/50). -/
theorem km_coin_avg (R : ℕ) (I : ℕ) :
    ∑ L ∈ blockChoices (2 * I + R), (wtβ L : ℝ) *
      (1 / 2 ^ (Finset.univ.filter (fun j : Fin I => kmOri L j ≠ 0)).card) = (79 / 100) ^ I := by
  have hprod : ∀ (I : ℕ) (L : List Bool),
      (1 : ℝ) / 2 ^ (Finset.univ.filter (fun j : Fin I => kmOri L j ≠ 0)).card =
        ∏ j : Fin I, (if kmOri L j ≠ 0 then (1 / 2 : ℝ) else 1) := by
    intro I L
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, one_div_pow]
  simp_rw [hprod]
  induction I with
  | zero => simp [km_wt_sum]
  | succ I ih =>
    have key : ∀ x y : Bool, ∑ L ∈ blockChoices (2 * I + R), (wtβ (x :: y :: L) : ℝ) *
        ∏ j : Fin (I + 1), (if kmOri (x :: y :: L) j ≠ 0 then (1 / 2 : ℝ) else 1) =
        ((if x then (3 / 10 : ℝ) else 7 / 10) * (if y then (3 / 10 : ℝ) else 7 / 10) *
          (if kmOri [x, y] 0 ≠ 0 then (1 / 2 : ℝ) else 1)) * (79 / 100) ^ I := by
      intro x y
      rw [← ih, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun L _ => ?_)
      rw [Fin.prod_univ_succ, fam_wt_cons, fam_wt_cons]
      simp only [Fin.val_succ, km_ori_cons2, Fin.val_zero]
      have h0 : kmOri (x :: y :: L) 0 = kmOri [x, y] 0 := by simp [kmOri]
      simp only [h0]
      cases x <;> cases y <;> norm_num <;> ring_nf
    rw [show 2 * (I + 1) + R = (2 * I + R) + 1 + 1 by ring, km_sum_cons, km_sum_cons, km_sum_cons,
      key, key, key, key]
    simp [kmOri]
    ring

end Collatz.Arctic
