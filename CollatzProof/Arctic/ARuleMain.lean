/-
The conclusion of `AutoCore` for the carry rules A, without hypotheses
(the quadratic-uses argument of Proposition 3.7).

* **Upper bound on values** (`ARule.autoVal_le`): the automaton value `u ⊗ A_{b_1} ⊗ ⋯ ⊗ A_{b_k} ⊗ c` is at most `fin (Cu + M·lenT n + Cc)`,
  using the maxima of the finite entries of `u`, `c`, `A f`, `A t` (it may be −∞). Linear in the length.
* **Number of uses** (`ARule.aRule_quad`, `ARuleFive.lean`): every carry rule A is used on orbit segments a number of times quadratic in the length of the starting point.
* Main theorem `autoCore_aRule`: the two together give the conclusion of `AutoCore` (when `ρ` is a carry rule A). Neither finiteness of the value
  (the hypothesis `hfin` of `AutoCore`) nor non-increase of the value (the hypothesis with slope `K`) is needed.
-/
import CollatzProof.Arctic.ARuleFive

namespace Collatz.Arctic.ARule

open Arc

/-! ### Upper bound on values -/

/-- A finite value is read as itself, −∞ as 0 (a reading for taking upper bounds). -/
def ub (a : Arc) : ℕ := WithBot.unbotD 0 (val a)

lemma le_fin_ub (a : Arc) : a ≤ fin (ub a) := by
  rw [le_iff_val, val_fin, ub]
  generalize val a = x
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe k => rw [WithBot.unbotD_coe]; exact le_rfl

lemma sum_le_fin {ι : Type*} (s : Finset ι) (f : ι → Arc) (k : ℕ) (h : ∀ i ∈ s, f i ≤ fin k) :
    ∑ i ∈ s, f i ≤ fin k := by
  rw [le_iff_val, val_sum]
  exact Finset.sup_le (fun i hi => h i hi)

lemma zero_le_arc (a : Arc) : (0 : Arc) ≤ a := by
  rw [le_iff_val, val_zero]; exact bot_le

/-- The maximum of the finite entries of a vector. -/
def vecBound {D : ℕ} (v : Fin D → Arc) : ℕ := Finset.univ.sup (fun i => ub (v i))

/-- The maximum of the finite entries of the digit matrices `A f`, `A t`. -/
def digBound {D : ℕ} (A : Interp D) : ℕ :=
  Finset.univ.sup (fun p : Fin D × Fin D => max (ub (A Letter.f p.1 p.2)) (ub (A Letter.t p.1 p.2)))

lemma vec_le {D : ℕ} (v : Fin D → Arc) (i : Fin D) : v i ≤ fin (vecBound v) :=
  (le_fin_ub _).trans (fin_le_fin.mpr
    (Finset.le_sup (f := fun i => ub (v i)) (Finset.mem_univ i)))

lemma entry_le {D : ℕ} (A : Interp D) (x : Letter) (hx : x = Letter.f ∨ x = Letter.t)
    (i j : Fin D) : A x i j ≤ fin (digBound A) := by
  have h1 : max (ub (A Letter.f i j)) (ub (A Letter.t i j)) ≤ digBound A :=
    Finset.le_sup (f := fun p : Fin D × Fin D =>
      max (ub (A Letter.f p.1 p.2)) (ub (A Letter.t p.1 p.2))) (Finset.mem_univ (i, j))
  rcases hx with rfl | rfl
  · exact (le_fin_ub _).trans (fin_le_fin.mpr ((le_max_left _ _).trans h1))
  · exact (le_fin_ub _).trans (fin_le_fin.mpr ((le_max_right _ _).trans h1))

/-- The entries of the matrix of a string of `f` and `t` only are bounded linearly in the length. -/
lemma ev_le {D : ℕ} (A : Interp D) : ∀ (w : Word), (∀ x ∈ w, x = Letter.f ∨ x = Letter.t) →
    ∀ i j, ev A w i j ≤ fin (digBound A * w.length) := by
  intro w
  induction w with
  | nil =>
    intro _ i j
    simp only [ev, List.map_nil, List.prod_nil, Matrix.one_apply, List.length_nil, mul_zero]
    split_ifs
    · exact le_rfl
    · exact zero_le_arc _
  | cons x w ih =>
    intro hw i j
    rw [ev_cons, Matrix.mul_apply]
    apply sum_le_fin
    intro k _
    have := mul_le_mul_of_le (entry_le A x (hw x List.mem_cons_self) i k)
      (ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)) k j)
    rw [fin_mul_fin] at this
    rw [List.length_cons, show digBound A * (w.length + 1) = digBound A + digBound A * w.length by
      ring]
    exact this

lemma binTail_mem (n : ℕ) : ∀ x ∈ binTail n, x = Letter.f ∨ x = Letter.t := by
  intro x hx
  unfold binTail at hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  split_ifs <;> simp

/-- **Upper bound on values**: the automaton value is bounded linearly in `lenT n` (it may be −∞). -/
theorem autoVal_le {D : ℕ} (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (n : ℕ) :
    autoVal u A c n ≤ fin (vecBound u + digBound A * lenT n + vecBound c) := by
  unfold autoVal
  simp only [dotProduct, Matrix.mulVec]
  apply sum_le_fin
  intro i _
  have hin : ∑ j, ev A (binTail n) i j * c j ≤ fin (digBound A * lenT n + vecBound c) := by
    apply sum_le_fin
    intro j _
    have := mul_le_mul_of_le (ev_le A _ (binTail_mem n) i j) (vec_le c j)
    rwa [fin_mul_fin] at this
  have := mul_le_mul_of_le (vec_le u i) hin
  rw [fin_mul_fin] at this
  rw [add_assoc]
  exact this

end Collatz.Arctic.ARule

namespace Collatz.Arctic

/-- **The conclusion of `AutoCore` for the carry rules A** (Proposition 3.7, without hypotheses): for every automaton `(u, A, c)`, slope `K`, carry rule
`aRule b d`, and `N`, there are a starting point `n ≥ N` and an orbit segment `n → T^m n` with all points at least 2 on which
`V(n) < K·len(n) + (number of uses of aRule b d)`. The value is bounded linearly in the length (`ARule.autoVal_le`)
and the number of uses is quadratic (`ARule.aRule_quad`), so the two hypotheses of `AutoCore` (finiteness of the value, non-increase of the value) are not needed. -/
theorem autoCore_aRule (D : ℕ) (u : Fin D → Arc) (A : Interp D) (c : Fin D → Arc) (K : ℕ)
    (b d : ℕ) (hb : b < 2) (hd : d ≤ 2) (N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ m : ℕ, (∀ i < m, 2 ≤ T^[i] n) ∧
      autoVal u A c n < Arc.fin (K * lenT n + usesOrbit (aRule b d) n m) := by
  set B := ARule.vecBound u + ARule.vecBound c + ARule.digBound A with hB
  obtain ⟨n, hN, m, horb, hlt⟩ := ARule.aRule_quad b d hb hd (B + 1) N
  refine ⟨n, hN, m, horb, lt_of_le_of_lt (ARule.autoVal_le u A c n) (Arc.fin_lt_fin.mpr ?_)⟩
  have h1 : ARule.digBound A * lenT n ≤ B * lenT n := Nat.mul_le_mul_right _ (by omega)
  nlinarith

end Collatz.Arctic
