/-
The Terras correspondence for $H$ at the level of letter words. The block level and the interface statements
`SpecHModel`, `SpecHClass`, `SpecHBoundary` are in
`Terras2.lean`; the swap `SpecHSwap` is in `Swap.lean`.

**Adapted from**: `TModel.lean` (`terrasState_snoc`, `terras_iter`, `terras_parity`, `terrasR_append`, `terras_prefix`,
`terras_orbit_ge`). For $T$ one step was 1 bit; for $H$ the letter $\mathsf a$ consumes 2 bits (one factor 3) and $\mathsf b$ 3 bits
(two factors 3) (`lbits`, `lthree`). The one-step lemmas (`tA_spec`, `tB_spec`, `Hmap_add_A`, `Hmap_add_B`,
`h_iter`) are adapted accordingly.

**Word level** (letter word `w`, `true` = $\mathsf a$): the state $(m_w, r_w, c_w, a_w)$ is written `wm`, `wr`, `wc`, `wa`.
* `wm_eq`, `wa_eq`: $m_w = \sum$ bits, $a_w = \sum$ exponents of 3 (independent of the state).
* `wr_lt`, `wc_lt`: $r_w < 2^{m_w}$, $c_w < 3^{a_w}$.
* `h_iter`: $H^{\lvert w\rvert}(r_w + 2^{m_w} t) = c_w + 3^{a_w} t$ (the invariant).
* `h_class`: the first $\lvert w\rvert$ steps of the orbit follow $w$ ($\equiv 0 \pmod 4$ for $\mathsf a$, $\equiv 7 \pmod 8$ for $\mathsf b$).
* `wr_append`, `h_prefix`: the residue and the orbit for concatenated words. `h_orbit_ge`: the lower bound $2^{m(w_{\ge i})} t$ for the orbit points.

Correspondence with the paper: the Terras correspondence of the model of $H$ in Proposition 7.2 (in the form of letter words).
-/
import CollatzProof.Arctic.HModel.Defs

namespace Collatz.Arctic.HModel

open Collatz.Arctic

/-! ## One-step lemmas -/

/-- $3^a \bmod 8$ is `pow3mod8 a`. -/
lemma pow3_mod8 (a : ℕ) : 3 ^ a % 8 = pow3mod8 a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    unfold pow3mod8 at *
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs with h1 h2 h2 <;> omega

/-- $c + 3^a t_A \equiv 0 \pmod 4$. -/
lemma tA_spec (c a : ℕ) : (c + 3 ^ a * tA c a) % 4 = 0 := by
  have h8 := pow3_mod8 a
  have h4 : 3 ^ a % 4 = pow3mod8 a % 4 := by
    have : 3 ^ a % 4 = 3 ^ a % 8 % 4 := by omega
    rw [this, h8]
  unfold tA
  rw [Nat.add_mod, Nat.mul_mod, h4]
  unfold pow3mod8
  split_ifs <;> (have := Nat.mod_lt c (show 4 > 0 by norm_num); interval_cases hc : c % 4 <;> simp_all)

/-- $c + 3^a t_B \equiv 7 \pmod 8$. -/
lemma tB_spec (c a : ℕ) : (c + 3 ^ a * tB c a) % 8 = 7 := by
  have h8 := pow3_mod8 a
  unfold tB
  rw [Nat.add_mod, Nat.mul_mod, h8]
  unfold pow3mod8
  split_ifs <;> (have := Nat.mod_lt c (show 8 > 0 by norm_num); interval_cases hc : c % 8 <;> simp_all)

lemma tA_lt (c a : ℕ) : tA c a < 4 := Nat.mod_lt _ (by norm_num)
lemma tB_lt (c a : ℕ) : tB c a < 8 := Nat.mod_lt _ (by norm_num)

lemma Hmap_A (y : ℕ) (hy : y % 4 = 0) : Hmap y = 3 * (y / 4) := by simp [Hmap, hy]

lemma Hmap_B (y : ℕ) (hy : y % 8 = 7) : Hmap y = (9 * y + 1) / 8 := by
  have : y % 4 ≠ 0 := by omega
  simp [Hmap, this, hy]

/-- Adding $4k$ to a point of type $\mathsf a$ shifts its image under $H$ by $3k$. -/
lemma Hmap_add_A (y k : ℕ) (hy : y % 4 = 0) : Hmap (y + 4 * k) = Hmap y + 3 * k := by
  rw [Hmap_A _ (by omega), Hmap_A _ hy]; omega

/-- Adding $8k$ to a point of type $\mathsf b$ shifts its image under $H$ by $9k$. -/
lemma Hmap_add_B (y k : ℕ) (hy : y % 8 = 7) : Hmap (y + 8 * k) = Hmap y + 9 * k := by
  rw [Hmap_B _ (by omega), Hmap_B _ hy]; omega

/-! ## Quantities at the word level -/

/-- The number of bits of a letter (2 for $\mathsf a$, 3 for $\mathsf b$). -/
def lbits (x : Bool) : ℕ := if x then 2 else 3

/-- The exponent of 3 of a letter (1 for $\mathsf a$, 2 for $\mathsf b$). -/
def lthree (x : Bool) : ℕ := if x then 1 else 2

/-- The low digits of $t$ for the next letter `x` (`tA` or `tB`). -/
def tNext (c a : ℕ) (x : Bool) : ℕ := if x then tA c a else tB c a

/-- $m_w$ (the number of bits). -/
def wm (w : List Bool) : ℕ := (hState w).1
/-- $r_w$ (the Terras residue). -/
def wr (w : List Bool) : ℕ := (hState w).2.1
/-- $c_w$ (the end-point constant). -/
def wc (w : List Bool) : ℕ := (hState w).2.2.1
/-- $a_w$ (the exponent of 3). -/
def wa (w : List Bool) : ℕ := (hState w).2.2.2

lemma hState_snoc (w : List Bool) (x : Bool) : hState (w ++ [x]) = hStep (hState w) x := by
  simp [hState, List.foldl_append]

lemma wm_snoc (w : List Bool) (x : Bool) : wm (w ++ [x]) = wm w + lbits x := by
  cases x <;> simp [wm, hState_snoc, hStep, lbits]

lemma wr_snoc (w : List Bool) (x : Bool) :
    wr (w ++ [x]) = wr w + 2 ^ wm w * tNext (wc w) (wa w) x := by
  cases x <;> simp [wr, wm, wc, wa, hState_snoc, hStep, tNext]

lemma wc_snoc (w : List Bool) (x : Bool) :
    wc (w ++ [x]) = Hmap (wc w + 3 ^ wa w * tNext (wc w) (wa w) x) := by
  cases x <;> simp [wc, wa, hState_snoc, hStep, tNext]

lemma wa_snoc (w : List Bool) (x : Bool) : wa (w ++ [x]) = wa w + lthree x := by
  cases x <;> simp [wa, hState_snoc, hStep, lthree]

lemma wm_nil : wm [] = 0 := rfl
lemma wr_nil : wr [] = 0 := rfl
lemma wc_nil : wc [] = 0 := rfl
lemma wa_nil : wa [] = 0 := rfl

lemma tNext_lt (c a : ℕ) (x : Bool) : tNext c a x < 2 ^ lbits x := by
  cases x
  · simpa [tNext, lbits] using tB_lt c a
  · simpa [tNext, lbits] using tA_lt c a

/-- Adding $2^{\mathrm{bits}} k$ to a point of the next letter shifts its image under $H$ by $3^{\mathrm{three}} k$. -/
lemma Hmap_add_next (c a k : ℕ) (x : Bool) :
    Hmap ((c + 3 ^ a * tNext c a x) + 2 ^ lbits x * k)
      = Hmap (c + 3 ^ a * tNext c a x) + 3 ^ lthree x * k := by
  cases x
  · simpa [tNext, lbits, lthree] using Hmap_add_B _ k (tB_spec c a)
  · simpa [tNext, lbits, lthree] using Hmap_add_A _ k (tA_spec c a)

/-- $m_w$ is the sum of the numbers of bits (independent of the state). -/
theorem wm_eq (w : List Bool) : wm w = (w.map lbits).sum := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih => simp [wm_snoc, ih]

/-- $a_w$ is the sum of the exponents of 3. -/
theorem wa_eq (w : List Bool) : wa w = (w.map lthree).sum := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih => simp [wa_snoc, ih]

theorem wm_append (w₁ w₂ : List Bool) : wm (w₁ ++ w₂) = wm w₁ + wm w₂ := by
  simp [wm_eq]

theorem wa_append (w₁ w₂ : List Bool) : wa (w₁ ++ w₂) = wa w₁ + wa w₂ := by
  simp [wa_eq]

/-! ## The Terras correspondence at the word level -/

/-- $r_w < 2^{m_w}$. -/
theorem wr_lt (w : List Bool) : wr w < 2 ^ wm w := by
  induction w using List.reverseRecOn with
  | nil => simp [wr_nil, wm_nil]
  | append_singleton w x ih =>
    rw [wr_snoc, wm_snoc, pow_add]
    have h := tNext_lt (wc w) (wa w) x
    have : 2 ^ wm w * (tNext (wc w) (wa w) x + 1) ≤ 2 ^ wm w * 2 ^ lbits x :=
      Nat.mul_le_mul_left _ h
    rw [mul_add, mul_one] at this
    omega

/-- $c_w < 3^{a_w}$. -/
theorem wc_lt (w : List Bool) : wc w < 3 ^ wa w := by
  induction w using List.reverseRecOn with
  | nil => simp [wc_nil, wa_nil]
  | append_singleton w x ih =>
    rw [wc_snoc, wa_snoc]
    set P := 3 ^ wa w with hP
    cases x
    · have h0 := tB_lt (wc w) (wa w)
      have hs := tB_spec (wc w) (wa w)
      simp only [tNext, Bool.false_eq_true, ↓reduceIte, lthree] at hs ⊢
      set y := wc w + P * tB (wc w) (wa w) with hy
      have hle : P * tB (wc w) (wa w) ≤ P * 7 := Nat.mul_le_mul_left _ (by omega)
      rw [Hmap_B _ hs, pow_add]
      have : y < 8 * P := by omega
      omega
    · have h0 := tA_lt (wc w) (wa w)
      have hs := tA_spec (wc w) (wa w)
      simp only [tNext, ↓reduceIte, lthree] at hs ⊢
      set y := wc w + P * tA (wc w) (wa w) with hy
      have hle : P * tA (wc w) (wa w) ≤ P * 3 := Nat.mul_le_mul_left _ (by omega)
      rw [Hmap_A _ hs, pow_succ, ← hP]
      omega

/-- The junction formula: $r_{wx} + 2^{m_{wx}} t = r_w + 2^{m_w}(t_0 + 2^{\mathrm{bits}} t)$. -/
lemma wr_snoc_add (w : List Bool) (x : Bool) (t : ℕ) :
    wr (w ++ [x]) + 2 ^ wm (w ++ [x]) * t
      = wr w + 2 ^ wm w * (tNext (wc w) (wa w) x + 2 ^ lbits x * t) := by
  rw [wr_snoc, wm_snoc, pow_add]; ring

/-- **The Terras correspondence for $H$**: $H^{\lvert w\rvert}(r_w + 2^{m_w} t) = c_w + 3^{a_w} t$. -/
theorem h_iter (w : List Bool) :
    ∀ t, Hmap^[w.length] (wr w + 2 ^ wm w * t) = wc w + 3 ^ wa w * t := by
  induction w using List.reverseRecOn with
  | nil => intro t; simp [wr_nil, wm_nil, wc_nil, wa_nil]
  | append_singleton w x ih =>
    intro t
    rw [wr_snoc_add, List.length_append, List.length_singleton, Function.iterate_succ_apply', ih,
      wc_snoc, wa_snoc]
    have e : wc w + 3 ^ wa w * (tNext (wc w) (wa w) x + 2 ^ lbits x * t)
        = (wc w + 3 ^ wa w * tNext (wc w) (wa w) x) + 2 ^ lbits x * (3 ^ wa w * t) := by ring
    rw [e, Hmap_add_next, pow_add]
    ring

/-- The first $\lvert w\rvert$ steps of the orbit follow $w$ ($\equiv 0 \pmod 4$ for $\mathsf a$, $\equiv 7 \pmod 8$ for $\mathsf b$). -/
theorem h_class (w : List Bool) :
    ∀ t, ∀ i < w.length,
      if w.getD i false then Hmap^[i] (wr w + 2 ^ wm w * t) % 4 = 0
      else Hmap^[i] (wr w + 2 ^ wm w * t) % 8 = 7 := by
  induction w using List.reverseRecOn with
  | nil => intro t i hi; simp at hi
  | append_singleton w x ih =>
    intro t i hi
    rw [wr_snoc_add]
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [List.getD_append _ _ _ _ h]
      exact ih _ i h
    · subst h
      rw [h_iter w, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp only [List.getD_cons_zero]
      have e : wc w + 3 ^ wa w * (tNext (wc w) (wa w) x + 2 ^ lbits x * t)
          = (wc w + 3 ^ wa w * tNext (wc w) (wa w) x) + 2 ^ lbits x * (3 ^ wa w * t) := by ring
      rw [e]
      cases x
      · have hs := tB_spec (wc w) (wa w)
        simp only [tNext, lbits, Bool.false_eq_true, ↓reduceIte] at hs ⊢
        omega
      · have hs := tA_spec (wc w) (wa w)
        simp only [tNext, lbits, ↓reduceIte] at hs ⊢
        omega

/-- The residue of a concatenated word is the residue of the first word plus $2^{m_{w_1}}$ times a number of $m_{w_2}$ digits. -/
theorem wr_append (w₁ w₂ : List Bool) :
    ∃ r' < 2 ^ wm w₂, wr (w₁ ++ w₂) = wr w₁ + 2 ^ wm w₁ * r' := by
  induction w₂ using List.reverseRecOn with
  | nil => exact ⟨0, by simp [wm_nil], by simp⟩
  | append_singleton w₂ x ih =>
    obtain ⟨r', hr', hR⟩ := ih
    refine ⟨r' + 2 ^ wm w₂ * tNext (wc (w₁ ++ w₂)) (wa (w₁ ++ w₂)) x, ?_, ?_⟩
    · rw [wm_snoc, pow_add]
      have h0 := tNext_lt (wc (w₁ ++ w₂)) (wa (w₁ ++ w₂)) x
      have : 2 ^ wm w₂ * (tNext (wc (w₁ ++ w₂)) (wa (w₁ ++ w₂)) x + 1) ≤ 2 ^ wm w₂ * 2 ^ lbits x :=
        Nat.mul_le_mul_left _ h0
      rw [mul_add, mul_one] at this
      omega
    · rw [← List.append_assoc, wr_snoc, hR, wm_append, pow_add]
      ring

/-- The orbit for concatenated words: the point reached after the first part $w_1$ is the image of $r' + 2^{m_{w_2}} t$ under the Terras correspondence of $w_1$. -/
theorem h_prefix (w₁ w₂ : List Bool) :
    ∃ r' < 2 ^ wm w₂, wr (w₁ ++ w₂) = wr w₁ + 2 ^ wm w₁ * r' ∧
      ∀ t, Hmap^[w₁.length] (wr (w₁ ++ w₂) + 2 ^ wm (w₁ ++ w₂) * t)
        = wc w₁ + 3 ^ wa w₁ * (r' + 2 ^ wm w₂ * t) := by
  obtain ⟨r', hr', hR⟩ := wr_append w₁ w₂
  refine ⟨r', hr', hR, fun t => ?_⟩
  have e : wr (w₁ ++ w₂) + 2 ^ wm (w₁ ++ w₂) * t = wr w₁ + 2 ^ wm w₁ * (r' + 2 ^ wm w₂ * t) := by
    rw [hR, wm_append, pow_add]; ring
  rw [e, h_iter]

/-- Lower bound for the orbit points: for $i \le \lvert w\rvert$, $2^{m(w_{\ge i})} t \le H^i(r_w + 2^{m_w} t)$. -/
theorem h_orbit_ge (w : List Bool) (t i : ℕ) (hi : i ≤ w.length) :
    2 ^ wm (w.drop i) * t ≤ Hmap^[i] (wr w + 2 ^ wm w * t) := by
  obtain ⟨r', _, _, hit⟩ := h_prefix (w.take i) (w.drop i)
  have h := hit t
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hi] at h
  rw [h]
  calc 2 ^ wm (w.drop i) * t ≤ r' + 2 ^ wm (w.drop i) * t := Nat.le_add_left _ _
    _ ≤ 3 ^ wa (w.take i) * (r' + 2 ^ wm (w.drop i) * t) := Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ _ := Nat.le_add_left _ _

end Collatz.Arctic.HModel
