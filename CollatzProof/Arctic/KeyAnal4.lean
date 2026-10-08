/-
Analytic ingredients of the swap argument (Appendix B.2), part 4: the order of 9 (`SpecNine`; step (c) of the proof of Theorem B.7).

* `ka_nine_pow`: `9^{2^i} = 1 + 2^{i+3} u_i` (`u_i` odd). `u_0 = 1`, `(1 + 2^{i+3}u)² = 1 + 2^{i+4}(u + 2^{i+2}u²)`.
* `ka_nine_order`: the unit 9 of `ZMod (2^k)` has order `2^{k-3}` (`k ≥ 3`).
* `ka_card_mod8`: there are `2^{k-3}` elements `x ≡ 1 (mod 8)` in `[0, 2^k)` (a sum with period 8).
* `specNine`: the image of the map lies in `1 + 8ℤ` (`MapsTo`), the map is injective by the order (`InjOn`), and surjective since the cardinalities agree (`SurjOn`).
-/
import CollatzProof.Arctic.KeyAnal

namespace Collatz.Arctic

open Finset

/-- `9^{2^i} = 1 + 2^{i+3} u` (`u` odd). -/
lemma ka_nine_pow (i : ℕ) : ∃ u, u % 2 = 1 ∧ 9 ^ (2 ^ i) = 1 + 2 ^ (i + 3) * u := by
  induction i with
  | zero => exact ⟨1, rfl, by norm_num⟩
  | succ i ih =>
    obtain ⟨u, hu, h⟩ := ih
    refine ⟨u + 2 ^ (i + 2) * u ^ 2, ?_, ?_⟩
    · have : 2 ^ (i + 2) * u ^ 2 % 2 = 0 := by
        rw [Nat.mul_mod, pow_succ, Nat.mul_mod_left, zero_mul, Nat.zero_mod]
      omega
    · rw [pow_succ, pow_mul, h]
      ring

/-- `9` is a unit of `ZMod (2^k)`. -/
lemma ka_nine_coprime (k : ℕ) : Nat.Coprime 9 (2 ^ k) :=
  Nat.Coprime.pow_right k (by norm_num)

/-- The unit 9 of `ZMod (2^k)` has order `2^{k-3}` (`k ≥ 3`). -/
lemma ka_nine_order (k : ℕ) (hk : 3 ≤ k) :
    orderOf (ZMod.unitOfCoprime 9 (ka_nine_coprime k)) = 2 ^ (k - 3) := by
  set u9 := ZMod.unitOfCoprime 9 (ka_nine_coprime k) with hu9
  have hval : ∀ m : ℕ, ((u9 ^ m : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) = ((9 ^ m : ℕ) : ZMod (2 ^ k)) := by
    intro m
    rw [Units.val_pow_eq_pow_val, hu9, ZMod.coe_unitOfCoprime, Nat.cast_pow]
  -- `9^{2^{k-3}} ≡ 1`.
  have hfin : u9 ^ (2 ^ (k - 3)) = 1 := by
    apply Units.ext
    rw [hval, Units.val_one]
    obtain ⟨u, _, h⟩ := ka_nine_pow (k - 3)
    rw [h, show k - 3 + 3 = k by omega, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
      add_zero, Nat.cast_one]
  rcases Nat.eq_or_lt_of_le hk with h3 | h4
  · subst h3
    rw [show (3 : ℕ) - 3 = 0 by rfl, pow_zero] at hfin ⊢
    exact orderOf_eq_one_iff.mpr (by simpa using hfin)
  · -- `k ≥ 4`: `9^{2^{k-4}} = 1 + 2^{k-1} u` (`u` odd) is not `1`.
    have hnot : ¬ u9 ^ (2 ^ (k - 4)) = 1 := by
      intro heq
      have h1 := congrArg (fun x : (ZMod (2 ^ k))ˣ => (x : ZMod (2 ^ k))) heq
      simp only [hval, Units.val_one] at h1
      obtain ⟨u, hu, h⟩ := ka_nine_pow (k - 4)
      rw [h, show k - 4 + 3 = k - 1 by omega, show (1 : ZMod (2 ^ k)) = ((1 : ℕ) : ZMod (2 ^ k)) by
        norm_num, ZMod.natCast_eq_natCast_iff'] at h1
      -- `(1 + 2^{k-1} u) mod 2^k = 1 + 2^{k-1}`.
      obtain ⟨q, hq⟩ : ∃ q, u = 2 * q + 1 := ⟨u / 2, by omega⟩
      have hk' : 2 ^ k = 2 ^ (k - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have hlt : 1 + 2 ^ (k - 1) < 2 ^ k := by
        have : 2 ≤ 2 ^ (k - 1) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have e1 : 1 + 2 ^ (k - 1) * u = (1 + 2 ^ (k - 1)) + 2 ^ k * q := by rw [hq, hk']; ring
      rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega)] at h1
      have : 0 < 2 ^ (k - 1) := by positivity
      omega
    have := orderOf_eq_prime_pow (p := 2) (n := k - 4) hnot
      (by rw [show k - 4 + 1 = k - 3 by omega]; exact hfin)
    rw [this, show k - 4 + 1 = k - 3 by omega]

/-- There are `2^{k-3}` elements `x ≡ 1 (mod 8)` in `[0, 2^k)`. -/
lemma ka_card_mod8 (k : ℕ) (hk : 3 ≤ k) :
    ((range (2 ^ k)).filter (fun x => x % 8 = 1)).card = 2 ^ (k - 3) := by
  rw [card_filter]
  have h2k : 2 ^ k = 2 ^ (k - 3) * 8 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, Nat.sub_add_cancel hk]
  rw [h2k, ka_sum_periodic 8 (2 ^ (k - 3)) (fun x => if x % 8 = 1 then 1 else 0)
    (fun t => by simp only [Nat.add_mod_right])]
  simp only [smul_eq_mul]
  rw [show (∑ t ∈ range 8, if t % 8 = 1 then 1 else 0) = 1 by decide, mul_one]

theorem specNine : SpecNine := by
  intro k hk
  have hpos : 0 < 2 ^ k := by positivity
  have h8 : 8 ∣ 2 ^ k := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 hk
  set u9 := ZMod.unitOfCoprime 9 (ka_nine_coprime k) with hu9
  have hval : ∀ m : ℕ, ((u9 ^ m : (ZMod (2 ^ k))ˣ) : ZMod (2 ^ k)) = ((9 ^ m : ℕ) : ZMod (2 ^ k)) := by
    intro m
    rw [Units.val_pow_eq_pow_val, hu9, ZMod.coe_unitOfCoprime, Nat.cast_pow]
  have hmaps : Set.MapsTo (fun y : ℕ => 9 ^ y % 2 ^ k) ↑(range (2 ^ (k - 3)))
      {x | x < 2 ^ k ∧ x % 8 = 1} := by
    intro y _
    refine ⟨Nat.mod_lt _ hpos, ?_⟩
    simp only
    rw [Nat.mod_mod_of_dvd _ h8, Nat.pow_mod]
    norm_num
  have hinj : Set.InjOn (fun y : ℕ => 9 ^ y % 2 ^ k) ↑(range (2 ^ (k - 3))) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    have hu : u9 ^ a = u9 ^ b := by
      apply Units.ext
      rw [hval, hval, ZMod.natCast_eq_natCast_iff']
      exact hab
    rw [pow_inj_mod, ka_nine_order k hk, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hu
    exact hu
  refine ⟨hmaps, hinj, ?_⟩
  -- surjectivity: the image has `2^{k-3}` elements, and so does the target.
  set T := (range (2 ^ k)).filter (fun x => x % 8 = 1) with hT
  have hsub : (range (2 ^ (k - 3))).image (fun y : ℕ => 9 ^ y % 2 ^ k) ⊆ T := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hmaps (by simpa using hy)
    rw [hT, mem_filter, mem_range]
    exact this
  have hcard : T.card ≤ ((range (2 ^ (k - 3))).image (fun y : ℕ => 9 ^ y % 2 ^ k)).card := by
    rw [card_image_of_injOn (by simpa using hinj), card_range, hT, ka_card_mod8 k hk]
  have heq := eq_of_subset_of_card_le hsub hcard
  intro x hx
  have hxT : x ∈ T := by
    rw [hT, mem_filter, mem_range]
    exact hx
  rw [← heq, mem_image] at hxT
  obtain ⟨y, hy, hyx⟩ := hxT
  exact ⟨y, by simpa using hy, hyx⟩

end Collatz.Arctic
