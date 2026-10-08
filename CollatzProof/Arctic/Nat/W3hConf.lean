/-
# The configuration automaton and realization (Section 12.6 of the paper)

The finite set of configurations and the order of quantifiers of the proof (Definition 12.20 and Lemma 12.21 of the paper).
The configurations and end classes of an earlier, longer argument that is not used here take the following form when all components
are 0/1 (the case of Section 12).

* **Configuration automaton** (§1): the states are pairs `PSt` of the forward state `s_t = μ(ω_{(0,t]})` and the residue `val(1ω_{(0,t]}) mod 3`; a step is
  `(s, r) ↦ (s μ(b), 2r + b)` (`stepF`; `stepP` reads `Bool`). It replaces the enlarged DFA of the earlier argument
  (support DFA, automaton of greedy choices, and so on); when all components are 0/1 only `μ` and the residue are needed.
* **Recurrence** (§2): `e ∈ 𝒦` ($\mathcal K_{\mathrm s}$); for a state `(s, r)` with `s e = s`, reading six times a word that leads back to `s` also brings back the residue
  (the sixth power of an affine permutation modulo 3 is the identity). `P₀ := (e, r₀)` is recurrent (`recurrent_of_mem`; in the setting, `Setup.P0_recurrent`).
* **Realization** (§3, `realize`): for a state `c` with `s e = s` and any word `w` there is a state `b`, reachable from `c`, from which
  reading `w (u♯)^R` leads back to `c` (`e w e` lies in the group $e\mathcal M_{\mathrm s}e$ and has a power equal to `e`; the word `w^♮`
  of the earlier argument and its event (a) are not used; `w` is the word `ρ · r' · y''` determined by `σ`).
* **Counting** (§4, `card_range_bits`): a bridge between counting free bits `u < 2^F` and counting `Fin F → Bool`
  (to apply `Dfa2.count_words`).

The top window is `τ := (u♯)^R` (with `τ'` empty; the window is not moved).
-/
import CollatzProof.Arctic.Nat.W3Decomp
import CollatzProof.Arctic.Nat.W3Bridge
import CollatzProof.Arctic.Dfa2

namespace Collatz.Arctic.NatQ5.W3h

open Collatz.Arctic Collatz.Arctic.NatQ5 Collatz.Arctic.NatQ5.W3c
open Collatz.Arctic.MinIdeal (BRel IsMinIdeal InH)
open Classical

set_option linter.unusedSectionVars false

/-! ## §0 Affine permutations modulo 3 -/

theorem two_pow_zmod3 (n : ℕ) : (2 : ZMod 3) ^ n = 1 ∨ (2 : ZMod 3) ^ n = 2 := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    rw [pow_succ]
    rcases ih with h | h <;> rw [h]
    · right; rfl
    · left; decide

/-- The sixth power of an affine permutation `r ↦ a r + c` (`a ≠ 0`) modulo 3 is the identity. -/
theorem aff_six (a c r : ZMod 3) (ha : a = 1 ∨ a = 2) :
    (fun r => a * r + c)^[6] r = r := by
  simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id]
  rcases ha with rfl | rfl <;> revert c r <;> decide

/-! ## §1 The configuration automaton -/

section Prod

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (B : ValAuto Q)

noncomputable instance instFintypeBRel : Fintype (BRel (ZIdx B)) := Fintype.ofFinite _

noncomputable instance instDecEqBRel : DecidableEq (BRel (ZIdx B)) := Classical.decEq _

/-- A state of the configuration automaton: the forward state, and the residue modulo 3 of the value including the leading 1. -/
abbrev PSt := BRel (ZIdx B) × ZMod 3

/-- One step (a digit of `Fin 2`). -/
def stepF (x : PSt B) (b : Fin 2) : PSt B := (x.1 * muZ B [b], 2 * x.2 + (((b : ℕ) : ZMod 3)))

/-- One step (reading `Bool`; the form of `Dfa`). -/
def stepP (x : PSt B) (b : Bool) : PSt B := stepF B x (W3d.b2f b)

theorem foldl_stepF (ω : List (Fin 2)) (x : PSt B) :
    ω.foldl (stepF B) x = (x.1 * muZ B ω, 2 ^ ω.length * x.2 + (((valW 0 ω : ℕ) : ZMod 3))) := by
  induction ω generalizing x with
  | nil => simp [muZ_nil, valW]
  | cons b ω ih =>
    rw [List.foldl_cons, ih]
    simp only [stepF, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [mul_assoc, ← muZ_append]; rfl
    · simp only [valW, List.length_cons]
      rw [valW_eq (2 * 0 + (b : ℕ)) ω]
      push_cast
      ring

theorem run_stepP (ω : List (Fin 2)) (x : PSt B) :
    Dfa.run (stepP B) x (ω.map W3d.f2b) = ω.foldl (stepF B) x :=
  W3d.run_map_f2b (stepF B) x ω

theorem map_b2f_map_f2b (w : List Bool) : (w.map W3d.b2f).map W3d.f2b = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  refine List.map_congr_left (fun b _ => ?_)
  cases b <;> rfl

theorem run_stepP_bool (w : List Bool) (x : PSt B) :
    Dfa.run (stepP B) x w = (w.map W3d.b2f).foldl (stepF B) x := by
  conv_lhs => rw [← map_b2f_map_f2b w]
  exact run_stepP B _ x

/-- If `s μ(v) = s`, then reading `v` `j` times moves the residue by the `j`-th power of an affine permutation. -/
theorem foldl_rep (v : List (Fin 2)) {s : BRel (ZIdx B)} (hs : s * muZ B v = s) (r : ZMod 3) (j : ℕ) :
    ((List.replicate j v).flatten).foldl (stepF B) (s, r) =
      (s, (fun r => (2 : ZMod 3) ^ v.length * r + (((valW 0 v : ℕ) : ZMod 3)))^[j] r) := by
  induction j generalizing r with
  | zero => simp
  | succ j ih =>
    rw [List.replicate_succ, List.flatten_cons, List.foldl_append, foldl_stepF B v (s, r)]
    simp only [hs]
    rw [ih, Function.iterate_succ_apply]

/-- If `s μ(v) = s`, then reading `v` six times returns to the original state. -/
theorem foldl_rep_six (v : List (Fin 2)) {s : BRel (ZIdx B)} (hs : s * muZ B v = s) (r : ZMod 3) :
    ((List.replicate 6 v).flatten).foldl (stepF B) (s, r) = (s, r) := by
  rw [foldl_rep B v hs r 6, aff_six _ _ _ (two_pow_zmod3 _)]

end Prod

/-! ## §2 Recurrence -/

section Rec

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (B : ValAuto Q)

/-- **Recurrence** (Lemma 12.21 (iii) of the paper): if `s ∈ 𝒦`, then `(s, r)` is a recurrent state of the configuration automaton. -/
theorem recurrent_of_mem {K : Set (BRel (ZIdx B))} (hK : IsMinIdeal (muMon B) K) {s : BRel (ZIdx B)}
    (hs : s ∈ K) (r : ZMod 3) : Dfa.Recurrent (stepP B) (s, r) := by
  rintro q' ⟨w, rfl⟩
  rw [run_stepP_bool]
  set ω := w.map W3d.b2f
  obtain ⟨ω', hω'⟩ := muZ_recurrent B hK hs ω
  set v := ω ++ ω'
  have hv : s * muZ B v = s := by rw [muZ_append, ← mul_assoc, hω']
  refine ⟨(ω' ++ (List.replicate 5 v).flatten).map W3d.f2b, ?_⟩
  rw [run_stepP, ← List.foldl_append]
  have h6 : (List.replicate 6 v).flatten = v ++ (List.replicate 5 v).flatten := rfl
  have e : ω ++ (ω' ++ (List.replicate 5 v).flatten) = (List.replicate 6 v).flatten := by
    rw [h6, List.append_assoc]
  rw [e, foldl_rep_six B v hv]

end Rec

/-! ## §3 Realization -/

section Realize

variable {Q : Type*} [Fintype Q] [DecidableEq Q] (B : ValAuto Q)

/-- `e (y e)^{j+1} = (e y e)^{j+1}` (`e` is idempotent). -/
theorem e_mul_pow {e y : BRel (ZIdx B)} (he : e * e = e) (j : ℕ) :
    e * (y * e) ^ (j + 1) = (e * y * e) ^ (j + 1) := by
  have hx : e * y * e * e = e * y * e := by rw [mul_assoc, he]
  induction j with
  | zero => simp [mul_assoc]
  | succ j ih =>
    have hxe : (e * y * e) ^ (j + 1) * e = (e * y * e) ^ (j + 1) := by
      rw [pow_succ, mul_assoc, hx]
    calc e * (y * e) ^ (j + 1 + 1) = e * (y * e) ^ (j + 1) * (y * e) := by
          rw [pow_succ (y * e) (j + 1), mul_assoc]
      _ = (e * y * e) ^ (j + 1) * (y * e) := by rw [ih]
      _ = (e * y * e) ^ (j + 1) * e * (y * e) := by rw [hxe]
      _ = (e * y * e) ^ (j + 1) * (e * y * e) := by simp only [mul_assoc]
      _ = (e * y * e) ^ (j + 1 + 1) := (pow_succ (e * y * e) (j + 1)).symm

/-- **Realization** (Lemma 12.21 (iv) of the paper): for the `e` of `Sharp`, a state `c = (s, r)` with `s e = s` and any word `w`, there is a state `b`, reachable from `c`,
from which reading `w (u♯)^R` (`R ≥ 1`) leads back to `c`. -/
theorem realize {K : Set (BRel (ZIdx B))} {us : List (Fin 2)} {e : BRel (ZIdx B)} (hS : Sharp B K us e)
    {R : ℕ} (hR : 1 ≤ R) {s : BRel (ZIdx B)} (hs : s * e = s) (r : ZMod 3) (w : List (Fin 2)) :
    ∃ v : List (Fin 2), (w ++ (List.replicate R us).flatten).foldl (stepF B) (v.foldl (stepF B) (s, r)) = (s, r) := by
  set v₀ := w ++ (List.replicate R us).flatten with hv₀
  set y := muZ B w
  have hmu : muZ B v₀ = y * e := by rw [hv₀, muZ_append, hS.mu_pow B hR]
  have hH : InH e (e * y * e) := eMe_inH hS.minIdeal hS.mem hS.idem (muZ_mem B w)
  obtain ⟨m, hm, hpow⟩ := hH.exists_pow_eq hS.idem
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsm : s * muZ B ((List.replicate (m' + 1) v₀).flatten) = s := by
    rw [muZ_flatten_replicate, hmu]
    calc s * (y * e) ^ (m' + 1) = s * e * (y * e) ^ (m' + 1) := by rw [hs]
      _ = s * (e * (y * e) ^ (m' + 1)) := by rw [mul_assoc]
      _ = s * (e * y * e) ^ (m' + 1) := by rw [e_mul_pow B hS.idem]
      _ = s := by rw [hpow, hs]
  set V := (List.replicate (m' + 1) v₀).flatten with hVdef
  have hV : V = (List.replicate m' v₀).flatten ++ v₀ := by
    rw [hVdef, List.replicate_succ', List.flatten_append, List.flatten_singleton]
  have h6 : (List.replicate 6 V).flatten = (List.replicate 5 V).flatten ++ V := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, List.replicate_succ' (n := 5), List.flatten_append,
      List.flatten_singleton]
  refine ⟨(List.replicate 5 V).flatten ++ (List.replicate m' v₀).flatten, ?_⟩
  rw [← List.foldl_append, List.append_assoc, ← hV, ← h6, foldl_rep_six B V hsm]

end Realize

/-! ## §4 A bridge for counting -/

/-- Counting over the free bits `u < 2^F` (the words read by `toB`) is counting over `Fin F → Bool`. -/
theorem card_range_bits (F : ℕ) (P : List Bool → Prop) :
    ((Finset.range (2 ^ F)).filter (fun u => P ((bitsMSB F u).map W3d.toB))).card =
      ((Finset.univ : Finset (Fin F → Bool)).filter (fun g => P (List.ofFn g))).card := by
  rw [card_filter_bitsMSB F (fun w => P (w.map W3d.toB))]
  unfold wordsOfLen
  rw [Finset.filter_image, Finset.card_image_of_injective]
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have : (List.ofFn (fun i => if g i then Letter.t else Letter.f)).map W3d.toB = List.ofFn g := by
      rw [List.map_ofFn]
      congr 1
      funext i
      by_cases h : g i <;> simp [h, W3d.toB]
    rw [this]
  · intro g g' h
    funext i
    have := congrArg (fun l => l[i.val]?) h
    simp only [List.getElem?_ofFn] at this
    by_cases hg : g i <;> by_cases hg' : g' i <;> simp_all

end Collatz.Arctic.NatQ5.W3h
