/-
# Natural-number interpretations of 𝒯 (Section 12.4), part (1): averages over uniform binary words

The basis of the laws of large numbers for finite automata (Section 12.4, `DfaLln*.lean`). The expectations over "independent uniform
digits" in Definition 12.12 and Theorem 12.13 are written as finite sums, without probability.

* `avg n G`: the average of `G` over the binary words of length `n` (`List Bool`, `2^n` of them), `(∑_{g : Fin n → Bool} G (ofFn g)) / 2^n`.
* Elementary properties (linearity, monotonicity, constants, absolute values), the split at the first letter `avg_succ`, **the product structure of words** `avg_append`
  (`avg (m + n) G = avg m (u ↦ avg n (v ↦ G (u ++ v)))`), marginalization `avg_take`, `avg_drop`,
  and the probability of a fixed prefix `avg_ind_take` (`= (1/2)^k`).
* Bridges to counting: `avg_ind_eq_card` (the form of `Dfa2.count_words`), `sum_wordsOfLen_eq` (sums over `Window.wordsOfLen`,
  whose words are read by `toB : Letter → Bool`; `ofB : Bool → Letter` is its inverse). Bridges to the words over `Fin 2` of `ValueAuto.lean`: `f2b`, `b2f`,
  `map_fin2_letter` (words turned into letters by `bitLetter`), `run_map_f2b` (DFAs with transitions on `Fin 2`).

Depends on none of Collatz, arctic and `ValueAuto.lean` (it uses only the words `Word` and `wordsOfLen` of `Window`).
-/
import CollatzProof.Arctic.Dfa2
import CollatzProof.Arctic.WindowLLN2

namespace Collatz.Arctic.NatQ5.W3d

open Collatz.Arctic

/-! ## Encoding of letters and digits -/

/-- Reads a digit letter (`f` is 0, `t` is 1) as a `Bool`. -/
def toB (s : Letter) : Bool := decide (s = Letter.t)

/-- A `Bool` digit as a letter (the same map as in the image of `wordsOfLen`). -/
def ofB (b : Bool) : Letter := if b then Letter.t else Letter.f

@[simp] theorem toB_ofB (b : Bool) : toB (ofB b) = b := by cases b <;> rfl

@[simp] theorem map_toB_map_ofB (w : List Bool) : (w.map ofB).map toB = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  exact List.map_congr_left (fun b _ => toB_ofB b)

theorem ofB_bin (b : Bool) : ofB b = Letter.f ∨ ofB b = Letter.t := by cases b <;> simp [ofB]

theorem map_ofB_bin (w : List Bool) : ∀ s ∈ w.map ofB, s = Letter.f ∨ s = Letter.t := by
  intro s hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  exact ofB_bin b

/-- A binary word read by `toB` and mapped back by `ofB` is unchanged. -/
theorem map_ofB_map_toB {w : Word} (hw : ∀ s ∈ w, s = Letter.f ∨ s = Letter.t) :
    (w.map toB).map ofB = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  refine List.map_congr_left (fun s hs => ?_)
  rcases hw s hs with rfl | rfl <;> rfl

/-! ### Bridge to the digits in `Fin 2` (to read the words of `binWord : ℕ → List (Fin 2)` of `ValueAuto.lean`) -/

/-- A `Fin 2` digit as a `Bool` (`1 ↦ true`). -/
def f2b (b : Fin 2) : Bool := decide (b = 1)

/-- A `Bool` as a `Fin 2` digit. -/
def b2f (b : Bool) : Fin 2 := if b then 1 else 0

@[simp] theorem b2f_f2b (b : Fin 2) : b2f (f2b b) = b := by
  fin_cases b <;> rfl

/-- The word turned into letters by `bitLetter` of `ValueAuto.lean` (`0 ↦ f`, `1 ↦ t`) equals the word read by `f2b` and turned into letters by `ofB`. -/
theorem map_fin2_letter (ω : List (Fin 2)) :
    ω.map (fun b => if b = 0 then Letter.f else Letter.t) = (ω.map f2b).map ofB := by
  rw [List.map_map]
  refine List.map_congr_left (fun b _ => ?_)
  fin_cases b <;> rfl

/-- A DFA with transitions on `Fin 2` digits, read with `Bool`: `run (fun s b => δ₂ s (b2f b)) x (ω.map f2b) = ω.foldl δ₂ x`. -/
theorem run_map_f2b {S : Type*} (δ₂ : S → Fin 2 → S) (x : S) (ω : List (Fin 2)) :
    Dfa.run (fun s b => δ₂ s (b2f b)) x (ω.map f2b) = ω.foldl δ₂ x := by
  induction ω generalizing x with
  | nil => rfl
  | cons b ω ih =>
    simp only [List.map_cons, Dfa.run_cons, b2f_f2b, List.foldl_cons]
    exact ih _

/-! ## Averages -/

/-- The average of `G` over the uniform binary words of length `n`. -/
noncomputable def avg (n : ℕ) (G : List Bool → ℝ) : ℝ :=
  (∑ g : Fin n → Bool, G (List.ofFn g)) / 2 ^ n

theorem avg_zero (G : List Bool → ℝ) : avg 0 G = G [] := by
  simp [avg]

/-- Split at the first letter. -/
theorem avg_succ (n : ℕ) (G : List Bool → ℝ) :
    avg (n + 1) G = (avg n (fun v => G (false :: v)) + avg n (fun v => G (true :: v))) / 2 := by
  simp only [avg]
  rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  rw [pow_succ]
  field_simp
  ring

theorem avg_congr {n : ℕ} {G H : List Bool → ℝ} (h : ∀ w : List Bool, w.length = n → G w = H w) :
    avg n G = avg n H := by
  unfold avg
  congr 1
  exact Finset.sum_congr rfl (fun g _ => h _ (List.length_ofFn))

theorem avg_mono {n : ℕ} {G H : List Bool → ℝ} (h : ∀ w : List Bool, w.length = n → G w ≤ H w) :
    avg n G ≤ avg n H := by
  unfold avg
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum (fun g _ => h _ (List.length_ofFn))

theorem avg_const (n : ℕ) (c : ℝ) : avg n (fun _ => c) = c := by
  unfold avg
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp

theorem avg_add (n : ℕ) (G H : List Bool → ℝ) :
    avg n (fun w => G w + H w) = avg n G + avg n H := by
  unfold avg
  rw [Finset.sum_add_distrib, add_div]

theorem avg_mul_left (n : ℕ) (c : ℝ) (G : List Bool → ℝ) :
    avg n (fun w => c * G w) = c * avg n G := by
  unfold avg
  rw [← Finset.mul_sum, mul_div_assoc]

theorem avg_div (n : ℕ) (G : List Bool → ℝ) (c : ℝ) :
    avg n (fun w => G w / c) = avg n G / c := by
  unfold avg
  rw [← Finset.sum_div, div_div, div_div, mul_comm]

theorem avg_neg (n : ℕ) (G : List Bool → ℝ) : avg n (fun w => -G w) = -avg n G := by
  have := avg_mul_left n (-1) G
  simpa using this

theorem avg_sub (n : ℕ) (G H : List Bool → ℝ) :
    avg n (fun w => G w - H w) = avg n G - avg n H := by
  have := avg_add n G (fun w => -H w)
  rw [avg_neg] at this
  simpa [sub_eq_add_neg] using this

theorem avg_sum {ι : Type*} (s : Finset ι) (n : ℕ) (G : ι → List Bool → ℝ) :
    avg n (fun w => ∑ i ∈ s, G i w) = ∑ i ∈ s, avg n (G i) := by
  unfold avg
  rw [Finset.sum_comm, Finset.sum_div]

theorem avg_nonneg {n : ℕ} {G : List Bool → ℝ} (h : ∀ w : List Bool, w.length = n → 0 ≤ G w) :
    0 ≤ avg n G := by
  have := avg_mono (G := fun _ => (0 : ℝ)) h
  rwa [avg_const] at this

theorem abs_avg_le (n : ℕ) (G : List Bool → ℝ) : |avg n G| ≤ avg n (fun w => |G w|) := by
  unfold avg
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.abs_sum_le_sum_abs _ _

/-- The absolute difference between an average and a constant is bounded by any pointwise bound of the absolute differences. -/
theorem abs_avg_sub_le {n : ℕ} {G : List Bool → ℝ} {c K : ℝ}
    (h : ∀ w : List Bool, w.length = n → |G w - c| ≤ K) : |avg n G - c| ≤ K := by
  have e : avg n G - c = avg n (fun w => G w - c) := by rw [avg_sub, avg_const]
  rw [e]
  refine (abs_avg_le n _).trans ?_
  have := avg_mono (G := fun w => |G w - c|) (H := fun _ => K) h
  rwa [avg_const] at this

/-- If `|G| ≤ K` pointwise, then `|avg G| ≤ K`. -/
theorem abs_avg_le_of {n : ℕ} {G : List Bool → ℝ} {K : ℝ}
    (h : ∀ w : List Bool, w.length = n → |G w| ≤ K) : |avg n G| ≤ K := by
  have h' : ∀ w : List Bool, w.length = n → |G w - 0| ≤ K := fun w hw => by
    simpa using h w hw
  simpa using abs_avg_sub_le h'

/-! ## The product structure of words and marginalization -/

/-- **The product structure of words**: a uniform word of length `m + n` is the concatenation of independent uniform words of lengths `m` and `n`. -/
theorem avg_append (m n : ℕ) (G : List Bool → ℝ) :
    avg (m + n) G = avg m (fun u => avg n (fun v => G (u ++ v))) := by
  induction m generalizing G with
  | zero => rw [Nat.zero_add, avg_zero]; rfl
  | succ m ih =>
    rw [Nat.succ_add, avg_succ, ih, ih, avg_succ]
    rfl

/-- The average of a function of the first `k` letters only. -/
theorem avg_take {k n : ℕ} (hk : k ≤ n) (g : List Bool → ℝ) :
    avg n (fun w => g (w.take k)) = avg k g := by
  obtain ⟨r, rfl⟩ : ∃ r, n = k + r := ⟨n - k, by omega⟩
  rw [avg_append]
  refine avg_congr (fun u hu => ?_)
  have : ∀ v : List Bool, g ((u ++ v).take k) = g u := fun v => by
    rw [List.take_left' hu]
  simp only [this, avg_const]

/-- The average of a function of the letters after the first `k` only. -/
theorem avg_drop (k n : ℕ) (g : List Bool → ℝ) :
    avg (k + n) (fun w => g (w.drop k)) = avg n g := by
  rw [avg_append]
  have : ∀ u : List Bool, u.length = k →
      avg n (fun v => g ((u ++ v).drop k)) = avg n g := fun u hu => by
    refine avg_congr (fun v _ => ?_)
    rw [List.drop_left' hu]
  rw [avg_congr this, avg_const]

/-- The probability of being equal to a fixed word. -/
theorem avg_ind_eq (u₀ : List Bool) :
    avg u₀.length (fun u => if u = u₀ then 1 else 0) = (1 / 2) ^ u₀.length := by
  induction u₀ with
  | nil => simp [avg_zero]
  | cons b u₀ ih =>
    rw [List.length_cons, avg_succ, pow_succ]
    cases b
    · have e1 : (fun v : List Bool => if false :: v = false :: u₀ then (1 : ℝ) else 0) =
          fun v => if v = u₀ then 1 else 0 := by funext v; simp
      have e2 : (fun v : List Bool => if true :: v = false :: u₀ then (1 : ℝ) else 0) =
          fun _ => 0 := by funext v; simp
      rw [e1, e2, ih, avg_const]; ring
    · have e1 : (fun v : List Bool => if false :: v = true :: u₀ then (1 : ℝ) else 0) =
          fun _ => 0 := by funext v; simp
      have e2 : (fun v : List Bool => if true :: v = true :: u₀ then (1 : ℝ) else 0) =
          fun v => if v = u₀ then 1 else 0 := by funext v; simp
      rw [e1, e2, ih, avg_const]; ring

/-- **The probability of a fixed prefix**: for a word `u₀` of length `k ≤ n`, the probability that the first `k` letters of a uniform word of
length `n` are `u₀` is `(1/2)^k`. -/
theorem avg_ind_take {n : ℕ} (u₀ : List Bool) (hk : u₀.length ≤ n) :
    avg n (fun w => if w.take u₀.length = u₀ then 1 else 0) = (1 / 2) ^ u₀.length := by
  rw [avg_take hk (fun u => if u = u₀ then (1 : ℝ) else 0), avg_ind_eq]

/-! ## Bridge to counting -/

/-- The probability of an event is the proportion of the count over `Fin n → Bool` (the form of `Dfa2.count_words`). -/
theorem avg_ind_eq_card (n : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    avg n (fun w => if P w then 1 else 0) =
      (((Finset.univ : Finset (Fin n → Bool)).filter (fun g => P (List.ofFn g))).card : ℝ) / 2 ^ n := by
  unfold avg
  rw [Finset.sum_boole]

/-- The sum over `wordsOfLen` (words read by `toB`) is `2^n` times the average. -/
theorem sum_wordsOfLen_eq (n : ℕ) (G : List Bool → ℝ) :
    ∑ v ∈ wordsOfLen n, G (v.map toB) = 2 ^ n * avg n G := by
  unfold wordsOfLen avg
  rw [Finset.sum_image]
  · rw [mul_div_cancel₀ _ (by positivity)]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    congr 1
    rw [List.map_ofFn]
    congr 1
    funext i
    by_cases h : g i <;> simp [h, toB]
  · intro g _ h _ hgh
    have h1 := List.ofFn_injective hgh
    funext i
    have h2 := congrFun h1 i
    cases hg : g i <;> cases hh : h i <;> simp_all

end Collatz.Arctic.NatQ5.W3d
