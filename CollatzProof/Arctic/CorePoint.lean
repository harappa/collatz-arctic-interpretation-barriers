/-
Assembly of Theorem 6.8 of the paper: upper and lower bounds of the value at one point of the point family.
* `point_upper`: if the configuration of the starting point `x₀` is the minimal configuration, then `V(x₀) ≤ (α_lo + C₁ε) lenT x₀ + Cu` (Lemma 6.5).
* `point_lower`: if the event of the lower bound and an occurrence of the absorbing word happen at the end point `x₁`, then `V(x₁) ≥ (α_lo - ε) lenT x₁ - Cst`
  (Lemma 6.6 and the minimality of `α_lo`).
-/
import CollatzProof.Arctic.CoreUpperApp
import CollatzProof.Arctic.CoreX0
import CollatzProof.Arctic.CoreHelp
import CollatzProof.Arctic.FamilyDigits
import CollatzProof.Arctic.CoreU

namespace Collatz.Arctic

open MinIdeal Matrix Classical

variable {D : ℕ}

/-- Digits of the starting point: `bin'(x₀) = pre₀ ++ S₁ ++ w*L ++ u* ++ z`, `pre₀ = bin'(τ) · u · ρ · r'`. -/
theorem binTail_X0_shape {β₀ β : List Bool} (hpre : β₀ <+: β) {n K τ x : ℕ}
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ) (hx : x < 2 ^ (n - K - (parityOf β₀).length))
    (S₁ ws us z : Word)
    (hS : bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) = S₁ ++ ws ++ us ++ z) :
    binTail (famX0 β₀ β n K τ x) =
      (binTail τ ++ bitsMSB (n - K - (parityOf β₀).length) x ++
        (bitsMSB (parityOf β₀).length (famRho β₀ β) ++
          bitsMSB ((parityOf β).length - (parityOf β₀).length) (famRtop β₀ β))) ++
        (S₁ ++ ws) ++ us ++ z := by
  rw [fam_binTail_X0 hpre hKn hτ hx, hS]
  simp only [List.append_assoc]

/-- Digits of the end point: `bin'(x₁) = pre₁ ++ S₁ ++ w*L ++ u* ++ z`, `pre₁ = bin'(h) · (top digits of ϖ) · (middle digits of ϖ)`. -/
theorem binTail_X1_shape {β₀ β : List Bool} {n K τ x : ℕ} (hK : 1 ≤ K)
    (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ) (hA : 1 ≤ terrasA (parityOf β))
    (S₁ ws us z : Word)
    (hS : bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) = S₁ ++ ws ++ us ++ z) :
    binTail (famX1 β₀ β n K τ x) =
      (binTail (famX1 β₀ β n K τ x / 2 ^ n) ++
        bitsMSB K (famX1 β₀ β n K τ x % 2 ^ n / 2 ^ (n - K)) ++
        bitsMSB (n - K - (parityOf β₀).length)
          (famX1 β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)) ++
        (S₁ ++ ws) ++ us ++ z := by
  rw [fam_binTail_X1 (β₀ := β₀) (β := β) (n := n) (K := K) (τ := τ) x hK (by omega) hτ1 hA,
    fam_bitsMSB_varpi τ x hKn, hS]
  simp only [List.append_assoc]

/-- **Upper bound at the starting point.** -/
theorem point_upper (A : Interp D) (u₀ c : Fin D → Arc) {E : BRel (Fin D)} (hE : E * E = E)
    (us : Word) (ε C₁ Cu : ℝ) (J : ℕ) (δ : ℚ) (z : Word)
    (hupz : ∀ (pre y₁ : Word) (P : List Upper.Seg),
        IsDigits (pre ++ y₁ ++ us ++ z) → Upper.GoodPartition (pre ++ y₁ ++ us ++ z) P ε J δ →
        (pre ++ y₁ ++ us ++ z).length ≤ 2 * (pre ++ y₁ ++ us).length →
        ∀ V : ℕ, vecAfter u₀ A (pre ++ y₁ ++ us ++ z) ⬝ᵥ c = Arc.fin V →
          (V : ℝ) ≤ (alphaZ hE A c z (cfgOf A hE y₁ (suppF (vecAfter u₀ A pre))) + C₁ * ε) *
            (pre ++ y₁ ++ us).length + Cu)
    (x0 : ℕ) (pre₀ y₁ : Word) (hshape : binTail x0 = pre₀ ++ y₁ ++ us ++ z)
    (hdig : IsDigits (binTail x0)) (P : List Upper.Seg) (hP : Upper.GoodPartition (binTail x0) P ε J δ)
    (hlen : (binTail x0).length ≤ 2 * (pre₀ ++ y₁ ++ us).length) (αlo : ℝ)
    (hcfg : alphaZ hE A c z (cfgOf A hE y₁ (suppF (vecAfter u₀ A pre₀))) = αlo)
    (hpos : 0 ≤ αlo + C₁ * ε) :
    ∀ V : ℕ, autoVal u₀ A c x0 = Arc.fin V → (V : ℝ) ≤ (αlo + C₁ * ε) * lenT x0 + Cu := by
  intro V hV
  rw [autoVal_eq, hshape] at hV
  rw [hshape] at hdig hP hlen
  have h := hupz pre₀ y₁ P hdig hP hlen V hV
  rw [hcfg] at h
  have hT : ((pre₀ ++ y₁ ++ us).length : ℝ) ≤ lenT x0 := by
    unfold lenT; rw [hshape]; push_cast; simp
  nlinarith

/-- **Lower bound at the end point.** -/
theorem point_lower (A : Interp D) (u₀ c : Fin D → Arc) {E : BRel (Fin D)} (hE : E * E = E)
    (us z : Word) (hEus : suppRel (ev A us) = E) (ε Cst : ℝ) (hε : 0 < ε) (hCst : 0 ≤ Cst)
    (w₀ : List Bool) (hw₀ : ∀ q, Dfa.Recurrent (supDelta A) (Dfa.run (supDelta A) q w₀))
    (x1 : ℕ) (pa pb pc y₁ : Word) (hshape : binTail x1 = (pa ++ pb ++ pc) ++ y₁ ++ us ++ z)
    (hdpa : IsDigits pa) (hdpb : IsDigits pb) (hdpc : IsDigits pc)
    (hocc : ∃ i, i + (w₀.map ofBool).length ≤ pc.length ∧ window pc i (w₀.map ofBool).length = w₀.map ofBool)
    (hlow : Lower.LowerAt u₀ A hE us z ε Cst (binTail x1)) (αlo : ℝ)
    (hmin : ∀ X, Dfa.Reach (supDelta A) (suppF u₀) X → Dfa.Recurrent (supDelta A) X →
      αlo ≤ alphaZ hE A c z (cfgOf A hE y₁ X)) :
    ∀ V : ℕ, autoVal u₀ A c x1 = Arc.fin V → (αlo - ε) * lenT x1 - Cst ≤ V := by
  intro V hV
  rw [autoVal_eq, hshape] at hV
  rw [hshape, show (pa ++ pb ++ pc) ++ y₁ ++ us ++ z = ((pa ++ pb ++ pc) ++ y₁) ++ us ++ z by
    simp only [List.append_assoc]] at hlow
  rw [show (pa ++ pb ++ pc) ++ y₁ ++ us ++ z = ((pa ++ pb ++ pc) ++ y₁) ++ us ++ z by
    simp only [List.append_assoc]] at hV
  have h := lower_value u₀ c A hE us z ((pa ++ pb ++ pc) ++ y₁) ε Cst hε hCst hEus hlow V hV
  rw [hitSet_vecAfter_eq_cfgOf] at h
  -- the state before the shared part is recurrent
  obtain ⟨i, hi, hwin⟩ := hocc
  have hpc : pc = pc.take i ++ w₀.map ofBool ++ pc.drop (i + (w₀.map ofBool).length) := by
    unfold window at hwin
    conv_lhs => rw [← List.take_append_drop i pc]
    rw [← List.take_append_drop (w₀.map ofBool).length (pc.drop i), hwin, List.drop_drop]
    simp only [List.append_assoc]
  have hdig : IsDigits (pa ++ pb ++ pc) := isDigits_append (isDigits_append hdpa hdpb) hdpc
  have hrun := suppF_vecAfter_run u₀ A (pa ++ pb ++ pc) hdig
  have hrec : Dfa.Recurrent (supDelta A) (suppF (vecAfter u₀ A (pa ++ pb ++ pc))) := by
    rw [hrun, hpc]
    simp only [List.map_append, map_toBool_ofBool, ← List.append_assoc]
    rw [Dfa.run_append]
    apply Dfa.Recurrent.after
    rw [Dfa.run_append]
    exact hw₀ _
  have hreach : Dfa.Reach (supDelta A) (suppF u₀) (suppF (vecAfter u₀ A (pa ++ pb ++ pc))) :=
    ⟨_, hrun.symm⟩
  have hα := hmin _ hreach hrec
  have hN : (0 : ℝ) ≤ lenT x1 := Nat.cast_nonneg _
  have hlenT : ((((pa ++ pb ++ pc) ++ y₁) ++ us ++ z).length : ℝ) = lenT x1 := by
    unfold lenT; rw [hshape]
  rw [hlenT] at h
  nlinarith

end Collatz.Arctic
