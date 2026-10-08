/-
Examples (dimension 1) of somewhere finite interpretations by arctic linear functions (`Coef.SomeFin`, the class for top termination) that strictly orient rules
not at the left end: the "if" direction of Proposition 4.8 of the paper.

* Family W (`JW E wt`): the letter `E` is the constant `x ↦ 0` (`(M_E)₀₀ = −∞`, `(c_E)₀ = 0`), the other letters are the translations
  `x ↦ x + wt σ`. A string beginning with `E` is the constant 0 (`W_head`); a string without `E` is `x ↦ x + Σ wt` (`W_noE`).
  With `E = /` and `wt f = wt t = 1`, the dynamic rules of `𝒯`, `𝓗` and `R_H` are strictly oriented (the rules beginning with `/` hold with equality).
* Family K (`JK c`): every letter is a constant `x ↦ c σ`. Since `[σ w] = c σ` (`K_head`), rules are compared by their first letters only.
  With `c f = c t = 1` the 6 carry rules are also strictly oriented. For the reversed systems `c` is 1 on the ternary digits.
* Instances (`nonleft_*`): for `𝒯`, `𝓗` and `R_H` (12 rules) each rule not beginning with `/`, and for the reversed systems each rule not beginning with `.`,
  is strictly oriented (one at a time).
-/
import CollatzProof.Arctic.Affine.Fin

namespace Collatz.Arctic.Affine

open Collatz.Arctic

lemma fin_ne_zero (n : ℕ) : Arc.fin n ≠ 0 := by
  intro h
  have := congrArg Arc.val h
  simp at this

lemma apply_fin1 (f : AffFun Arc 1) (y : Fin 1 → Arc) (i : Fin 1) :
    f.apply y i = f.M i 0 * y 0 + f.c i := by
  simp [AffFun.apply, Matrix.mulVec, dotProduct]

lemma mul_ge (a b : ℕ) (hab : b ≤ a) (y : Arc) : Arc.fin b * y ≤ Arc.fin a * y :=
  Arc.mul_le_mul_of_le (Arc.fin_le_fin.mpr hab) le_rfl

lemma mul_gg (a b : ℕ) (hab : b < a) (y : Arc) : GG (Arc.fin a * y) (Arc.fin b * y) := by
  by_cases hy : Arc.val y = ⊥
  · have h0 : y = 0 := Arc.ext (by rw [hy]; rfl)
    subst h0
    exact Or.inr ⟨mul_zero _, mul_zero _⟩
  · obtain ⟨n, rfl⟩ := (Arc.val_ne_bot_iff y).mp hy
    left
    rw [Arc.fin_mul_fin, Arc.fin_mul_fin]
    exact Arc.fin_lt_fin.mpr (by omega)

/-- Assembling "all rules of `R` weakly, `ρ` strictly" in dimension 1. -/
lemma orientable_one (R : List Rule) (ρ : Rule) (J : Letter → AffFun Arc 1) (hs : SomeFin Nat.one_pos J)
    (hw : ∀ ρ' ∈ R, PWeak J ρ') (hρ : PStrict J ρ) : SomeFinOrientable R ρ :=
  ⟨1, Nat.one_pos, J, hs, hw, hρ⟩

/-! ## Family W -/

def JW (E : Letter) (wt : Letter → ℕ) (σ : Letter) : AffFun Arc 1 :=
  ⟨fun _ _ => if σ = E then 0 else Arc.fin (wt σ), fun _ => if σ = E then Arc.fin 0 else 0⟩

lemma JW_E (E : Letter) (wt : Letter → ℕ) (y : Fin 1 → Arc) : (JW E wt E).apply y = fun _ => Arc.fin 0 := by
  funext i
  rw [apply_fin1]
  simp [JW]

lemma JW_ne (E : Letter) (wt : Letter → ℕ) (σ : Letter) (h : σ ≠ E) (y : Fin 1 → Arc) :
    (JW E wt σ).apply y = fun _ => Arc.fin (wt σ) * y 0 := by
  funext i
  rw [apply_fin1]
  simp [JW, h]

lemma W_head (E : Letter) (wt : Letter → ℕ) (w : List Letter) (x : Fin 1 → Arc) :
    (evL (JW E wt) (E :: w)).apply x = fun _ => Arc.fin 0 := by
  rw [evL_apply_cons, JW_E]

lemma W_noE (E : Letter) (wt : Letter → ℕ) (w : List Letter) (hw : E ∉ w) (x : Fin 1 → Arc) :
    (evL (JW E wt) w).apply x = fun _ => Arc.fin (w.map wt).sum * x 0 := by
  induction w with
  | nil =>
    rw [evL_apply_nil]
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    show x 0 = 1 * x 0
    rw [one_mul]
  | cons σ w ih =>
    have hσ : σ ≠ E := fun h => hw (h ▸ List.mem_cons_self)
    have hw' : E ∉ w := fun h => hw (List.mem_cons_of_mem _ h)
    rw [evL_apply_cons, ih hw', JW_ne E wt σ hσ]
    funext i
    rw [← mul_assoc, Arc.fin_mul_fin, List.map_cons, List.sum_cons]

lemma nm_of {l : List Letter} {a : Letter} (h : l.contains a = false) : a ∉ l := by
  simpa using h

/-- Test for weak orientation (family W): both sides begin with `E`, or neither side contains `E` and the weight does not increase. -/
def wOK (E : Letter) (wt : Letter → ℕ) (ρ : Rule) : Bool :=
  (ρ.lhs.head? == some E && ρ.rhs.head? == some E) ||
    (!(ρ.lhs.contains E) && !(ρ.rhs.contains E) && decide ((ρ.rhs.map wt).sum ≤ (ρ.lhs.map wt).sum))

/-- Test for strict orientation (family W): neither side contains `E` and the weight decreases. -/
def wStrict (E : Letter) (wt : Letter → ℕ) (ρ : Rule) : Bool :=
  !(ρ.lhs.contains E) && !(ρ.rhs.contains E) && decide ((ρ.rhs.map wt).sum < (ρ.lhs.map wt).sum)

lemma W_weak (E : Letter) (wt : Letter → ℕ) (ρ : Rule) (h : wOK E wt ρ = true) : PWeak (JW E wt) ρ := by
  intro x i
  simp only [wOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    decide_eq_true_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
  · obtain ⟨l, hl⟩ : ∃ l, ρ.lhs = E :: l := by
      cases hρ : ρ.lhs with
      | nil => simp [hρ] at h1
      | cons a l => rw [hρ] at h1; simp at h1; exact ⟨l, by rw [h1]⟩
    obtain ⟨r, hr⟩ : ∃ r, ρ.rhs = E :: r := by
      cases hρ : ρ.rhs with
      | nil => simp [hρ] at h2
      | cons a r => rw [hρ] at h2; simp at h2; exact ⟨r, by rw [h2]⟩
    rw [hl, hr, W_head, W_head]
  · rw [W_noE E wt _ (nm_of h1), W_noE E wt _ (nm_of h2)]
    exact mul_ge _ _ h3 _

lemma W_strict (E : Letter) (wt : Letter → ℕ) (ρ : Rule) (h : wStrict E wt ρ = true) :
    PStrict (JW E wt) ρ := by
  intro x i
  simp only [wStrict, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  rw [W_noE E wt _ (nm_of h.1.1), W_noE E wt _ (nm_of h.1.2)]
  exact mul_gg _ _ h.2 _

lemma W_someFin (E : Letter) (wt : Letter → ℕ) : SomeFin Nat.one_pos (JW E wt) := by
  intro σ
  by_cases h : σ = E
  · left; simp only [JW, h, ite_true]; exact fin_ne_zero 0
  · right; simp only [JW, h, ite_false]; exact fin_ne_zero _

theorem orientable_W (R : List Rule) (ρ : Rule) (E : Letter) (wt : Letter → ℕ)
    (hR : R.all (wOK E wt) = true) (hρ : wStrict E wt ρ = true) : SomeFinOrientable R ρ :=
  orientable_one R ρ (JW E wt) (W_someFin E wt)
    (fun ρ' h' => W_weak E wt ρ' (List.all_eq_true.mp hR ρ' h')) (W_strict E wt ρ hρ)

/-! ## Family K -/

def JK (c : Letter → ℕ) (σ : Letter) : AffFun Arc 1 := ⟨fun _ _ => 0, fun _ => Arc.fin (c σ)⟩

lemma K_head (c : Letter → ℕ) (σ : Letter) (w : List Letter) (x : Fin 1 → Arc) :
    (evL (JK c) (σ :: w)).apply x = fun _ => Arc.fin (c σ) := by
  rw [evL_apply_cons]
  funext i
  rw [apply_fin1]
  simp [JK]

/-- Test for weak orientation (family K): both sides are nonempty and the constant of the first letter does not increase. -/
def kOK (c : Letter → ℕ) (ρ : Rule) : Bool :=
  match ρ.lhs, ρ.rhs with
  | a :: _, b :: _ => decide (c b ≤ c a)
  | _, _ => false

def kStrict (c : Letter → ℕ) (ρ : Rule) : Bool :=
  match ρ.lhs, ρ.rhs with
  | a :: _, b :: _ => decide (c b < c a)
  | _, _ => false

lemma K_weak (c : Letter → ℕ) (ρ : Rule) (h : kOK c ρ = true) : PWeak (JK c) ρ := by
  intro x i
  obtain ⟨l, r⟩ := ρ
  cases l with
  | nil => simp [kOK] at h
  | cons a l =>
    cases r with
    | nil => simp [kOK] at h
    | cons b r =>
      simp only [kOK, decide_eq_true_eq] at h
      show (evL (JK c) (b :: r)).apply x i ≤ (evL (JK c) (a :: l)).apply x i
      rw [K_head, K_head]
      exact Arc.fin_le_fin.mpr h

lemma K_strict (c : Letter → ℕ) (ρ : Rule) (h : kStrict c ρ = true) : PStrict (JK c) ρ := by
  intro x i
  obtain ⟨l, r⟩ := ρ
  cases l with
  | nil => simp [kStrict] at h
  | cons a l =>
    cases r with
    | nil => simp [kStrict] at h
    | cons b r =>
      simp only [kStrict, decide_eq_true_eq] at h
      show GG ((evL (JK c) (a :: l)).apply x i) ((evL (JK c) (b :: r)).apply x i)
      rw [K_head, K_head]
      exact Or.inl (Arc.fin_lt_fin.mpr h)

lemma K_someFin (c : Letter → ℕ) : SomeFin Nat.one_pos (JK c) := fun _ => Or.inl (fin_ne_zero _)

theorem orientable_K (R : List Rule) (ρ : Rule) (c : Letter → ℕ)
    (hR : R.all (kOK c) = true) (hρ : kStrict c ρ = true) : SomeFinOrientable R ρ :=
  orientable_one R ρ (JK c) (K_someFin c) (fun ρ' h' => K_weak c ρ' (List.all_eq_true.mp hR ρ' h'))
    (K_strict c ρ hρ)

/-! ## Instances -/

open Letter

/-- Weights: 1 for the binary digits, 0 otherwise. -/
def wtBits : Letter → ℕ | f => 1 | t => 1 | _ => 0

/-- Weights: 1 for the ternary digits, 0 otherwise. -/
def wtDigits : Letter → ℕ | d0 => 1 | d1 => 1 | d2 => 1 | _ => 0

/-- `𝒯`: each of the 8 rules not beginning with `/` can be strictly oriented. -/
theorem nonleft_ST : ∀ ρ ∈ rulesST, ρ.lhs.head? ≠ some lft → SomeFinOrientable rulesST ρ := by
  intro ρ hρ hne
  simp only [rulesST, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact orientable_W _ _ lft wtBits (by decide) (by decide)
  · exact orientable_W _ _ lft wtBits (by decide) (by decide)
  all_goals first
    | exact orientable_K _ _ wtBits (by decide) (by decide)
    | exact absurd rfl hne

/-- `𝓗`: the 8 rules not beginning with `/`. -/
theorem nonleft_HT : ∀ ρ ∈ HTPDB.rulesHT, ρ.lhs.head? ≠ some lft → SomeFinOrientable HTPDB.rulesHT ρ := by
  intro ρ hρ hne
  simp only [HTPDB.rulesHT, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact orientable_W _ _ lft wtBits (by decide) (by decide)
  · exact orientable_W _ _ lft wtBits (by decide) (by decide)
  all_goals first
    | exact orientable_K _ _ wtBits (by decide) (by decide)
    | exact absurd rfl hne

/-- `R_H` (12 rules): the 8 rules not beginning with the left end `lft` (the 6 carry rules and the 2 dynamic rules). -/
theorem nonleft_RH : ∀ ρ ∈ RH.rulesRH, ρ.lhs.head? ≠ some lft → SomeFinOrientable RH.rulesRH ρ := by
  intro ρ hρ hne
  simp only [RH.rulesRH, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact orientable_K _ _ wtBits (by decide) (by decide)
    | exact absurd rfl hne

/-- The reversed `𝒯`: the 9 rules not beginning with `.`. -/
theorem nonleft_STrev : ∀ ρ ∈ NonVacuity.rulesSTrev, ρ.lhs.head? ≠ some rgt →
    SomeFinOrientable NonVacuity.rulesSTrev ρ := by
  intro ρ hρ hne
  simp only [NonVacuity.rulesSTrev, rulesST, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | exact orientable_K _ _ wtDigits (by decide) (by decide)

/-- The reversed `𝓗`: the 9 rules not beginning with `.`. -/
theorem nonleft_HTrev : ∀ ρ ∈ HTPDB.NonVacuityH.rulesHTrev, ρ.lhs.head? ≠ some rgt →
    SomeFinOrientable HTPDB.NonVacuityH.rulesHTrev ρ := by
  intro ρ hρ hne
  simp only [HTPDB.NonVacuityH.rulesHTrev, HTPDB.rulesHT, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | exact orientable_K _ _ wtDigits (by decide) (by decide)

/-- The reversed 10 used rules of `R_H`: the 8 rules not beginning with `.`. -/
theorem nonleft_RHrev : ∀ ρ ∈ RH.usedRH.map NonVacuity.revRule, ρ.lhs.head? ≠ some rgt →
    SomeFinOrientable (RH.usedRH.map NonVacuity.revRule) ρ := by
  intro ρ hρ hne
  simp only [RH.usedRH, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | exact orientable_K _ _ wtDigits (by decide) (by decide)

end Collatz.Arctic.Affine
