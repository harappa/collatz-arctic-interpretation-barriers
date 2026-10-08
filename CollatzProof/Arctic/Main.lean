/-
The main theorem `arctic_barrier_ST : ValueCore → ArcticBarrierST` (Theorem 3.1 of the paper for 𝒯, from `ValueCore`).
The correctness of the canonical derivation, `canDeriv_chain`, is proved in `Canon.lean` (lemmas on binary representations).
-/
import CollatzProof.Arctic.Bridge
import CollatzProof.Arctic.Canon

namespace Collatz.Arctic

open Arc

/-- Every carry rule is one of the 11 rules (`b ≤ 1`, `d ≤ 2`). -/
lemma aRule_mem {b d : ℕ} (hb : b < 2) (hd : d ≤ 2) : aRule b d ∈ rulesST := by
  interval_cases b <;> interval_cases d <;> decide

lemma leftRule_mem (d : ℕ) : leftRule d ∈ rulesST := by
  unfold leftRule
  split_ifs <;> decide

lemma sweepRules_mem : ∀ (bs : List ℕ) (d : ℕ), (∀ b ∈ bs, b < 2) → d ≤ 2 →
    ∀ σ ∈ sweepRules bs d, σ ∈ rulesST
  | [], d, _, _ => by
    intro σ hσ
    simp only [sweepRules, List.mem_singleton] at hσ
    subst hσ
    exact leftRule_mem d
  | b :: bs, d, hbs, hd => by
    intro σ hσ
    simp only [sweepRules, List.mem_cons] at hσ
    have hb : b < 2 := hbs b List.mem_cons_self
    rcases hσ with rfl | hσ
    · exact aRule_mem hb hd
    · exact sweepRules_mem bs _ (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
        (by omega) σ hσ

lemma tailBitsLSB_lt (n : ℕ) : ∀ b ∈ tailBitsLSB n, b < 2 := by
  intro b hb
  unfold tailBitsLSB at hb
  have h1 := List.mem_reverse.mp hb
  have h2 := List.mem_of_mem_drop h1
  have h3 := List.mem_reverse.mp h2
  exact Nat.digits_lt_base (by norm_num) h3

/-- Every rule used by a canonical derivation is one of the 11 rules. -/
lemma canDeriv_sub (n : ℕ) : ∀ σ ∈ canDeriv n, σ ∈ rulesST := by
  unfold canDeriv
  split_ifs
  · intro σ hσ
    simp only [List.mem_singleton] at hσ
    subst hσ
    decide
  · intro σ hσ
    simp only [List.mem_cons] at hσ
    rcases hσ with rfl | hσ
    · decide
    · exact sweepRules_mem _ 2 (tailBitsLSB_lt _) (le_refl 2) σ hσ

lemma usesOrbit_zero (ρ : Rule) (n : ℕ) : usesOrbit ρ n 0 = 0 := by
  simp [usesOrbit]

lemma usesOrbit_succ (ρ : Rule) (n m : ℕ) :
    usesOrbit ρ n (m + 1) = uses ρ n + usesOrbit ρ (T n) m := by
  simp only [usesOrbit, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  congr 2

/-- The estimate along an orbit. -/
lemma orbit_bound {d : ℕ} (hd : 0 < d) (I : Interp d) (hfin : Fin00 hd I)
    (hweak : ∀ ρ ∈ rulesST, Weak I ρ) {ρ : Rule} (hρ : Strict I ρ) :
    ∀ (m n : ℕ), (∀ i < m, 2 ≤ T^[i] n) → ∀ a b : ℕ, Phi hd I (can n) = fin a →
      Phi hd I (can (T^[m] n)) = fin b → b + usesOrbit ρ n m ≤ a := by
  intro m
  induction m with
  | zero =>
    intro n _ a b ha hb
    simp only [Function.iterate_zero, id] at hb
    rw [ha] at hb
    have := congrArg val hb
    simp only [val_fin] at this
    have hab : a = b := by exact_mod_cast this
    simp [usesOrbit_zero, hab]
  | succ m ih =>
    intro n horb a b ha hb
    have hn : 2 ≤ n := by simpa using horb 0 (Nat.succ_pos m)
    obtain ⟨c, hc⟩ := phi_fin hd I hfin (can (T n))
    have hstep := phi_chain hd I hfin hρ (canDeriv_chain n hn)
      (fun σ hσ => hweak σ (canDeriv_sub n σ hσ)) a c ha hc
    have horb' : ∀ i < m, 2 ≤ T^[i] (T n) := by
      intro i hi
      have := horb (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    have hb' : Phi hd I (can (T^[m] (T n))) = fin b := by
      rwa [← Function.iterate_succ_apply]
    have hrest := ih (T n) horb' c b hc hb'
    rw [usesOrbit_succ]
    unfold uses
    omega

/-- **Main theorem** (Theorem 3.1 of the paper, 𝒯): under the hypothesis `ValueCore` carrying the probabilistic part, an arctic interpretation (of any dimension)
in which every `(M_s)₀₀` is finite and which weakly orients all rules strictly orients none of them. -/
theorem arctic_barrier_ST (hcore : ValueCore) : ArcticBarrierST := by
  intro d hd I hfin hweak ρ hρmem hρ
  have hmono : ∀ n, 2 ≤ n → Phi hd I (can (T n)) ≤ Phi hd I (can n) := fun n hn =>
    phi_chain_weak hd I (canDeriv_chain n hn) (fun σ hσ => hweak σ (canDeriv_sub n σ hσ))
  obtain ⟨n, -, m, horb, hlt⟩ := hcore d hd I hfin hmono ρ hρmem 0
  obtain ⟨a, ha⟩ := phi_fin hd I hfin (can n)
  obtain ⟨b, hb⟩ := phi_fin hd I hfin (can (T^[m] n))
  have hbound := orbit_bound hd I hfin hweak hρ m n horb a b ha hb
  rw [ha, fin_lt_fin] at hlt
  omega

end Collatz.Arctic
