/-
The bridge from orientations to values (Lemma 5.1 of the paper), and the part of the derivation of the main theorem from the hypothesis `ValueCore` carrying the probabilistic part.
-/
import CollatzProof.Arctic.Statement

namespace Collatz.Arctic

namespace Arc

lemma val_sum {ι : Type*} (s : Finset ι) (f : ι → Arc) :
    val (∑ i ∈ s, f i) = s.sup (fun i => val (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert, val_add, ih]

lemma le_sum_of_mem {ι : Type*} {s : Finset ι} (f : ι → Arc) {i : ι} (hi : i ∈ s) :
    f i ≤ ∑ j ∈ s, f j := by
  rw [le_iff_val, val_sum]
  exact Finset.le_sup (f := fun j => val (f j)) hi

lemma mul_le_mul_of_le {a b c e : Arc} (h1 : a ≤ b) (h2 : c ≤ e) : a * c ≤ b * e := by
  rw [le_iff_val] at *
  simp only [val_mul]
  exact add_le_add h1 h2

lemma sum_le_sum_of_le {ι : Type*} (s : Finset ι) {f g : ι → Arc} (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  rw [le_iff_val, val_sum, val_sum]
  exact Finset.sup_mono_fun (fun i hi => h i hi)

/-- A finite sum is attained at some term. -/
lemma exists_eq_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → Arc) :
    ∃ i ∈ s, f i = ∑ j ∈ s, f j := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup s hs (fun j => val (f j))
  exact ⟨i, hi, ext (by rw [val_sum, h])⟩

lemma val_ne_bot_iff (a : Arc) : val a ≠ ⊥ ↔ ∃ n : ℕ, a = fin n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp h
    exact ⟨n, ext (by rw [val_fin]; exact hn.symm)⟩
  · rintro ⟨n, rfl⟩
    simp

lemma fin_le_fin {m n : ℕ} : fin m ≤ fin n ↔ m ≤ n := by
  rw [le_iff_val]; simp

lemma fin_lt_fin {m n : ℕ} : fin m < fin n ↔ m < n := by
  show val (fin m) < val (fin n) ↔ m < n
  simp

lemma fin_mul_fin (m n : ℕ) : fin m * fin n = fin (m + n) := ext (by simp)

lemma ne_bot_left {a b : Arc} (h : val (a * b) ≠ ⊥) : val a ≠ ⊥ := by
  intro ha; apply h; simp [val_mul, ha]

lemma ne_bot_right {a b : Arc} (h : val (a * b) ≠ ⊥) : val b ≠ ⊥ := by
  intro hb; apply h; simp [val_mul, hb]

lemma mul_ne_zero_of {a b : Arc} (ha : val a ≠ ⊥) (hb : val b ≠ ⊥) : val (a * b) ≠ ⊥ := by
  obtain ⟨m, rfl⟩ := (val_ne_bot_iff a).mp ha
  obtain ⟨n, rfl⟩ := (val_ne_bot_iff b).mp hb
  rw [fin_mul_fin]; simp

end Arc

open Arc

/-- The entrywise order. -/
def MLe {d : ℕ} (A B : AMat d) : Prop := ∀ i j, A i j ≤ B i j

lemma mul_mono {d : ℕ} {A A' B B' : AMat d} (hA : MLe A A') (hB : MLe B B') : MLe (A * B) (A' * B') := by
  intro i j
  simp only [Matrix.mul_apply]
  exact sum_le_sum_of_le _ (fun k _ => mul_le_mul_of_le (hA i k) (hB k j))

lemma MLe.refl {d : ℕ} (A : AMat d) : MLe A A := fun _ _ => le_rfl

lemma ev_append {d : ℕ} (I : Interp d) (u v : Word) : ev I (u ++ v) = ev I u * ev I v := by
  simp [ev, List.map_append, List.prod_append]

lemma ev_cons {d : ℕ} (I : Interp d) (s : Letter) (w : Word) : ev I (s :: w) = I s * ev I w := by
  simp [ev]

/-- Under weak orientation, `Φ` in a context does not increase. -/
lemma phi_step_weak {d : ℕ} (hd : 0 < d) (I : Interp d) {ρ : Rule} (h : Weak I ρ) (p q : Word) :
    Phi hd I (p ++ ρ.rhs ++ q) ≤ Phi hd I (p ++ ρ.lhs ++ q) := by
  unfold Phi
  rw [ev_append, ev_append, ev_append, ev_append]
  exact mul_mono (mul_mono (MLe.refl _) (fun i j => h i j)) (MLe.refl _) _ _

/-- `Φ` is finite (if all `(M_s)₀₀` are finite). -/
lemma phi_finite {d : ℕ} (hd : 0 < d) (I : Interp d) (hfin : Fin00 hd I) (w : Word) :
    val (Phi hd I w) ≠ ⊥ := by
  unfold Phi
  induction w with
  | nil => simp [ev]
  | cons s w ih =>
    rw [ev_cons, Matrix.mul_apply]
    intro hbot
    have hle := le_sum_of_mem (s := Finset.univ)
      (fun k => I s ⟨0, hd⟩ k * ev I w k ⟨0, hd⟩) (Finset.mem_univ ⟨0, hd⟩)
    rw [le_iff_val, hbot] at hle
    have hs : val (I s ⟨0, hd⟩ ⟨0, hd⟩) ≠ ⊥ := fun h0 => hfin s (ext (by simpa using h0))
    exact mul_ne_zero_of hs ih (le_bot_iff.mp hle)

/-- Lemma 5.1: under strict orientation, `Φ` in a context decreases by at least 1. -/
lemma phi_step_strict {d : ℕ} (hd : 0 < d) (I : Interp d) {ρ : Rule} (h : Strict I ρ) (p q : Word)
    {a : ℕ} (ha : Phi hd I (p ++ ρ.rhs ++ q) = fin a) :
    fin (a + 1) ≤ Phi hd I (p ++ ρ.lhs ++ q) := by
  classical
  unfold Phi at ha ⊢
  rw [ev_append, ev_append] at ha ⊢
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  -- choose an index j attaining the value of the right-hand side, then i
  rw [Matrix.mul_apply] at ha
  obtain ⟨j, -, hj⟩ := exists_eq_sum hne
    (fun j => (ev I p * ev I ρ.rhs) ⟨0, hd⟩ j * ev I q j ⟨0, hd⟩)
  rw [← hj] at ha
  have hfa : val ((ev I p * ev I ρ.rhs) ⟨0, hd⟩ j * ev I q j ⟨0, hd⟩) ≠ ⊥ := by rw [ha]; simp
  have hPR := ne_bot_left hfa
  have hQ := ne_bot_right hfa
  rw [Matrix.mul_apply] at hPR ha
  obtain ⟨i, -, hi⟩ := exists_eq_sum hne (fun i => ev I p ⟨0, hd⟩ i * ev I ρ.rhs i j)
  rw [← hi] at hPR ha
  have hP := ne_bot_left hPR
  have hR := ne_bot_right hPR
  obtain ⟨x, hx⟩ := (val_ne_bot_iff _).mp hP
  obtain ⟨y, hy⟩ := (val_ne_bot_iff _).mp hR
  obtain ⟨z, hz⟩ := (val_ne_bot_iff _).mp hQ
  rw [hx, hy, hz, fin_mul_fin, fin_mul_fin] at ha
  have hxyz : x + y + z = a := by
    have := congrArg val ha
    simp only [val_fin] at this
    exact_mod_cast this
  -- strict orientation at that entry
  have hL : fin (y + 1) ≤ ev I ρ.lhs i j := by
    rcases h i j with hlt | ⟨_, hr0⟩
    · rw [hy] at hlt
      have hLne : val (ev I ρ.lhs i j) ≠ ⊥ := by
        intro hb
        have : val (fin y) < val (ev I ρ.lhs i j) := hlt
        rw [hb] at this
        exact absurd this (not_lt_bot)
      obtain ⟨l, hl⟩ := (val_ne_bot_iff _).mp hLne
      rw [hl] at hlt ⊢
      rw [fin_le_fin]
      exact (fin_lt_fin.mp hlt)
    · exfalso
      rw [hy] at hr0
      have := congrArg val hr0
      simp at this
  calc fin (a + 1) = ev I p ⟨0, hd⟩ i * fin (y + 1) * ev I q j ⟨0, hd⟩ := by
        rw [hx, hz, fin_mul_fin, fin_mul_fin]
        congr 1
        omega
    _ ≤ ev I p ⟨0, hd⟩ i * ev I ρ.lhs i j * ev I q j ⟨0, hd⟩ :=
        mul_le_mul_of_le (mul_le_mul_of_le le_rfl hL) le_rfl
    _ ≤ (ev I p * ev I ρ.lhs) ⟨0, hd⟩ j * ev I q j ⟨0, hd⟩ := by
        refine mul_le_mul_of_le ?_ le_rfl
        rw [Matrix.mul_apply]
        exact le_sum_of_mem (fun i => ev I p ⟨0, hd⟩ i * ev I ρ.lhs i j) (Finset.mem_univ i)
    _ ≤ (ev I p * ev I ρ.lhs * ev I q) ⟨0, hd⟩ ⟨0, hd⟩ := by
        rw [Matrix.mul_apply]
        exact le_sum_of_mem (fun j => (ev I p * ev I ρ.lhs) ⟨0, hd⟩ j * ev I q j ⟨0, hd⟩)
          (Finset.mem_univ j)

/-- A derivation by a list of rules. -/
inductive Chain : List Rule → Word → Word → Prop
  | nil (u : Word) : Chain [] u u
  | cons {ρ : Rule} {rs : List Rule} {u w v : Word} : Step ρ u w → Chain rs w v → Chain (ρ :: rs) u v

lemma phi_fin {d : ℕ} (hd : 0 < d) (I : Interp d) (hfin : Fin00 hd I) (w : Word) :
    ∃ a : ℕ, Phi hd I w = fin a :=
  (val_ne_bot_iff _).mp (phi_finite hd I hfin w)

/-- Along a derivation by weakly oriented rules only, `Φ` does not increase. -/
lemma phi_chain_weak {d : ℕ} (hd : 0 < d) (I : Interp d) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, Weak I σ) →
      Phi hd I v ≤ Phi hd I u := by
  intro rs u v hc
  induction hc with
  | nil u => intro _; exact le_rfl
  | @cons σ rs u w v hstep _ ih =>
    intro hw
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    exact (ih (fun τ hτ => hw τ (List.mem_cons_of_mem _ hτ))).trans
      (phi_step_weak hd I (hw σ List.mem_cons_self) p q)

/-- The estimate along a derivation: `Φ` decreases by at least the number of uses of a strictly oriented rule `ρ`. -/
lemma phi_chain {d : ℕ} (hd : 0 < d) (I : Interp d) (hfin : Fin00 hd I) {ρ : Rule} (hρ : Strict I ρ) :
    ∀ {rs : List Rule} {u v : Word}, Chain rs u v → (∀ σ ∈ rs, Weak I σ) →
      ∀ a b : ℕ, Phi hd I u = fin a → Phi hd I v = fin b → b + rs.count ρ ≤ a := by
  intro rs u v hc
  induction hc with
  | nil u =>
    intro _ a b ha hb
    rw [ha] at hb
    have := congrArg val hb
    simp only [val_fin] at this
    have hab : a = b := by exact_mod_cast this
    simp [hab]
  | @cons σ rs u w v hstep _ ih =>
    intro hw a b ha hb
    obtain ⟨c, hc⟩ := phi_fin hd I hfin w
    have hrest := ih (fun τ hτ => hw τ (List.mem_cons_of_mem _ hτ)) c b hc hb
    obtain ⟨p, q, rfl, rfl⟩ := hstep
    by_cases hσ : σ = ρ
    · subst hσ
      have h1 := phi_step_strict hd I hρ p q hc
      rw [ha, fin_le_fin] at h1
      rw [List.count_cons_self]
      omega
    · have h1 := phi_step_weak hd I (hw σ List.mem_cons_self) p q
      rw [hc, ha, fin_le_fin] at h1
      rw [List.count_cons_of_ne hσ]
      omega

end Collatz.Arctic
