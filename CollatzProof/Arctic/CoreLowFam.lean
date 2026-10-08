/-
Lemma 6.6 of the paper applied to the end point `x₁` of the point family (assembly of Theorem 6.8). The lower bound at the end point in the proof
of Theorem 6.8: split the digits of `x₁` into the top part `bin'(⌊h/2^b⌋)` (not controlled), the low `b` bits of `h` (close to uniform by Lemma 6.4 (ii)),
the top `K` bits of `ϖ` (not controlled), the middle bits of `ϖ` (exactly uniform by Lemma 6.4 (i)), and the shared `y z`.
-/
import CollatzProof.Arctic.CoreU
import CollatzProof.Arctic.FamilyDigits

namespace Collatz.Arctic

open MinIdeal Classical

variable {D : ℕ}

/-- If the residues of the values `f x < 2^b` are close to uniform, so are their `b`-digit representations (transfer of the total variation distance). -/
theorem tv_bitsMSB {ι : Type*} (X : Finset ι) (b : ℕ) (f : ι → ℕ) (hf : ∀ x ∈ X, f x < 2 ^ b) (θ : ℝ)
    (htv : ∑ j ∈ Finset.range (2 ^ b), |(((X.filter (fun x => f x = j)).card : ℝ) / X.card) - 1 / 2 ^ b| ≤ θ) :
    Lower.TVClose X (fun x => bitsMSB b (f x)) b (θ / 2) := by
  unfold Lower.TVClose
  rw [← image_bitsMSB, Finset.sum_image (fun j hj j' hj' h => bitsMSB_injOn b hj hj' h)]
  have e : ∀ j ∈ Finset.range (2 ^ b),
      |(((X.filter (fun x => bitsMSB b (f x) = bitsMSB b j)).card : ℝ) / X.card) - 1 / 2 ^ b| =
      |(((X.filter (fun x => f x = j)).card : ℝ) / X.card) - 1 / 2 ^ b| := by
    intro j hj
    have hfil : X.filter (fun x => bitsMSB b (f x) = bitsMSB b j) = X.filter (fun x => f x = j) := by
      apply Finset.filter_congr
      intro x hx
      constructor
      · intro h; exact bitsMSB_injOn b (Finset.mem_coe.mpr (Finset.mem_range.mpr (hf x hx)))
          (Finset.mem_coe.mpr hj) h
      · intro h; rw [h]
    rw [hfil]
  rw [Finset.sum_congr rfl e]
  linarith

/-- A uniform representation (each value taken exactly once) has total variation distance 0. -/
theorem tv_bitsMSB_exact (F : ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ Finset.range (2 ^ F), f x < 2 ^ F)
    (hone : ∀ j < 2 ^ F, ((Finset.range (2 ^ F)).filter (fun x => f x = j)).card = 1) :
    Lower.TVClose (Finset.range (2 ^ F)) (fun x => bitsMSB F (f x)) F 0 := by
  have h := tv_bitsMSB (Finset.range (2 ^ F)) F f hf 0 (by
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j hj
    rw [hone j (Finset.mem_range.mp hj), Finset.card_range]
    push_cast
    simp)
  simpa using h

/-- **Event of the lower bound at the end point** (Lemma 6.6 applied to `x₁`). -/
theorem low_count (hSP : HSP) (A : Interp D) (u₀ : Fin D → Arc) {K₀ : Set (BRel (Fin D))}
    (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K₀) {E : BRel (Fin D)} (hEK : E ∈ K₀) (hE : E * E = E)
    (us : Word) (hus : IsDigits us) (huE : suppRel (ev A us) = E) (y z : Word) (hy : IsDigits y)
    (hyu : us <:+ y) (G : ℕ) :
    ∃ Cst : ℝ, ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (β₀ β : List Bool) (n K τ b Δ : ℕ),
      1 ≤ K → K + (parityOf β₀).length ≤ n → 2 ^ (K - 1) ≤ τ → τ < 2 ^ K →
      2 ^ (b + Δ + K) ≤ 3 ^ terrasA (parityOf β) → 3 ^ terrasA (parityOf β) < 2 ^ (b + (K + Δ + 1)) →
      K + Δ ≤ G → L₀ ≤ b → L₀ ≤ n - K - (parityOf β₀).length →
      bitsMSB (parityOf β₀).length (terrasR (parityOf β₀)) = y ++ z →
      (1 - ((3 : ℝ) / 2 ^ Δ + 2 ^ ((parityOf β₀).length + 2) * 3 ^ terrasA (parityOf β) / 2 ^ n) / 2
          - ε) * 2 ^ (n - K - (parityOf β₀).length) ≤
        (((Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun x =>
          Lower.LowerAt u₀ A hE us z ε Cst (binTail (famX1 β₀ β n K τ x)))).card : ℝ) := by
  obtain ⟨Cst, hlow⟩ := Lower.lemma_56_11_2 hSP A u₀ hK hEK hE us hus huE y z hy hyu G
  refine ⟨Cst, fun ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hlow ε hε
  refine ⟨L₀, fun β₀ β n K τ b Δ hK1 hKn hτ1 hτ2 hb1 hb2 hG hLb hLF hS => ?_⟩
  have hA : 1 ≤ terrasA (parityOf β) := by
    by_contra h0
    push Not at h0
    have h00 : terrasA (parityOf β) = 0 := by omega
    rw [h00, pow_zero] at hb1
    have : 2 ≤ 2 ^ (b + Δ + K) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (b + Δ + K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hKn' : K ≤ n := by omega
  -- decomposition of the digits
  have hdec : ∀ x ∈ Finset.range (2 ^ (n - K - (parityOf β₀).length)),
      binTail (famX1 β₀ β n K τ x) =
      binTail (famX1 β₀ β n K τ x / 2 ^ n / 2 ^ b) ++ bitsMSB b (famX1 β₀ β n K τ x / 2 ^ n % 2 ^ b) ++
        bitsMSB K (famX1 β₀ β n K τ x % 2 ^ n / 2 ^ (n - K)) ++
        bitsMSB (n - K - (parityOf β₀).length)
          (famX1 β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length) ++ y ++ z := by
    intro x _
    have h1 := fam_binTail_X1 (β₀ := β₀) (β := β) (n := n) (K := K) (τ := τ) x hK1 hKn' hτ1 hA
    have hhb := (fam_h_low (β₀ := β₀) (β := β) (n := n) (K := K) (τ := τ) x b Δ hK1 hKn' hτ1 hb1).1
    have h2b : 2 ^ b ≤ famX1 β₀ β n K τ x / 2 ^ n :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hhb
    rw [h1, fam_binTail_divmod _ b h2b, fam_bitsMSB_varpi τ x hKn, hS]
    simp only [List.append_assoc]
  have hlen₀ : ∀ x ∈ Finset.range (2 ^ (n - K - (parityOf β₀).length)),
      (binTail (famX1 β₀ β n K τ x / 2 ^ n / 2 ^ b)).length ≤ G := by
    intro x hx
    have h := fam_h_high (β₀ := β₀) (β := β) (n := n) (K := K) (τ := τ) (u := x) b Δ hKn hτ2
      (Finset.mem_range.mp hx) hb2
    have e : lenT (famX1 β₀ β n K τ x / 2 ^ n / 2 ^ b) =
        (binTail (famX1 β₀ β n K τ x / 2 ^ n / 2 ^ b)).length := rfl
    omega
  have hcard : ((Finset.range (2 ^ (n - K - (parityOf β₀).length))).card : ℝ) =
      2 ^ (n - K - (parityOf β₀).length) := by
    rw [Finset.card_range]; push_cast; ring
  -- total variation distance
  have htv1 := tv_bitsMSB (Finset.range (2 ^ (n - K - (parityOf β₀).length))) b
    (fun x => famX1 β₀ β n K τ x / 2 ^ n % 2 ^ b) (fun x _ => Nat.mod_lt _ (by positivity))
    ((3 : ℝ) / 2 ^ Δ + 2 ^ ((parityOf β₀).length + 2) * 3 ^ terrasA (parityOf β) / 2 ^ n)
    (by
      rw [hcard]
      have hq := fam_end_tv β₀ β τ b Δ hKn hb1
      have hr := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at hr
      exact hr)
  have htv2 := tv_bitsMSB_exact (n - K - (parityOf β₀).length)
    (fun x => famX1 β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)
    (fun x hx => Finset.mem_range.mp (Finset.mem_coe.mp ((fam_mid_bijOn β₀ β τ hKn).mapsTo
      (Finset.mem_coe.mpr hx))))
    (fun j hj => fam_mid_card β₀ β τ hKn j hj)
  have hmain := hL₀ b (n - K - (parityOf β₀).length) hLb hLF
    (Finset.range (2 ^ (n - K - (parityOf β₀).length)))
    (fun x => binTail (famX1 β₀ β n K τ x / 2 ^ n / 2 ^ b))
    (fun x => bitsMSB K (famX1 β₀ β n K τ x % 2 ^ n / 2 ^ (n - K)))
    (fun x => bitsMSB b (famX1 β₀ β n K τ x / 2 ^ n % 2 ^ b))
    (fun x => bitsMSB (n - K - (parityOf β₀).length)
      (famX1 β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)) _ 0 hlen₀
    (fun x _ => ⟨bitsMSB_isDigits _ _, by rw [bitsMSB_length]; omega⟩)
    (fun x _ => bitsMSB_mem_wordsOfLen _ _) (fun x _ => bitsMSB_mem_wordsOfLen _ _) htv1 htv2
  have hfil : (Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun x =>
        Lower.LowerAt u₀ A hE us z ε Cst
          (binTail (famX1 β₀ β n K τ x / 2 ^ n / 2 ^ b) ++ bitsMSB b (famX1 β₀ β n K τ x / 2 ^ n % 2 ^ b) ++
            bitsMSB K (famX1 β₀ β n K τ x % 2 ^ n / 2 ^ (n - K)) ++
            bitsMSB (n - K - (parityOf β₀).length)
              (famX1 β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length) ++ y ++ z)) =
      (Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun x =>
        Lower.LowerAt u₀ A hE us z ε Cst (binTail (famX1 β₀ β n K τ x))) :=
    Finset.filter_congr (fun x hx => by rw [hdec x hx])
  rw [hfil, hcard] at hmain
  linarith

end Collatz.Arctic
