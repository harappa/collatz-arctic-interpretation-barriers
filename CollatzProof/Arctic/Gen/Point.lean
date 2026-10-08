/-
Generic layer: the shape of the digits of the point family, and the counting for the lower bound at the end point.

Adapted from `CoreX0.lean` (`binTail_X0_split`), `CorePoint.lean` (`binTail_X0_shape`, `binTail_X1_shape`),
`CoreLowFam.lean` (`low_count`) and `CoreMain.lean` (the small lemmas `isDigits_binTail`, `lowerAt_mono`, `alphaZ_nonneg`) for $T$.
The point family is `Gen/Family.lean`, `Gen/FamilyDigits.lean` (the form taking a model `BM` as an argument); we only replace the residue `terrasR (parityOf β)` by
`BM.R β`. Material for the splitting in the "upper bound at the starting point" in the proof of Theorem 6.8, and the "lower bound at the end point"
(Lemma 6.6 applied to `x₁`).

Shape-only components are used from the source as they are: the cuts of the starting point `x0Cut`, `x0_goodPartition`, `blockEnd_*` (`CoreX0`),
the upper and lower bounds at one point `point_upper`, `point_lower` (`CorePoint`; claims only about the numbers `x0`, `x1` and the shape of their digits, independent of the model),
the transfer of total variation distance `tv_bitsMSB`, `tv_bitsMSB_exact` (`CoreLowFam`). `CoreMain` imports the components on the number of uses for $T$,
so its three small lemmas are copied here.
-/
import CollatzProof.Arctic.Gen.FamilyDigits
import CollatzProof.Arctic.CorePoint
import CollatzProof.Arctic.CoreLowFam

namespace Collatz.Arctic.Gen

open Collatz.Arctic MinIdeal Classical

variable {D : ℕ} {BM : BlockModel}

/-! ## Small lemmas (copied from `CoreMain`) -/

theorem isDigits_binTail (n : ℕ) : IsDigits (binTail n) := by
  intro s hs
  unfold binTail at hs
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hs
  split_ifs <;> simp

/-- `LowerAt` is monotone in the constant `Cst`. -/
theorem lowerAt_mono {E : BRel (Fin D)} (u : Fin D → Arc) (A : Interp D) (hE : E * E = E)
    (us z : Word) (ε Cst Cst' : ℝ) (h : Cst ≤ Cst') (ω : Word) :
    Lower.LowerAt u A hE us z ε Cst ω → Lower.LowerAt u A hE us z ε Cst' ω := by
  intro hl p hp j hj hjp b hb v hv
  have := hl p hp j hj hjp b hb v hv
  linarith

/-- `α_z(I) ≥ 0`. -/
theorem alphaZ_nonneg {E : BRel (Fin D)} (hE : E * E = E) (A : Interp D) (c : Fin D → Arc) (z : Word)
    (I : Set (Cls E hE)) : 0 ≤ alphaZ hE A c z I :=
  Real.sSup_nonneg (by rintro r ⟨j, -, -, -, -, -, rfl⟩; exact rate_nonneg _ _)

/-! ## Shape of the digits of the starting point and of the end point -/

/-- `bin'(x₀) = bin'(τ) · u · ρ · r_β (m digits)`. -/
theorem binTail_X0_split {β₀ β : List Bool} (hpre : β₀ <+: β) {n K τ u : ℕ}
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ)
    (hu : u < 2 ^ (n - K - (parityOf β₀).length)) :
    binTail (famX0 BM β₀ β n K τ u)
      = binTail τ ++ bitsMSB (n - K - (parityOf β₀).length) u
        ++ bitsMSB (parityOf β₀).length (famRho BM β₀ β)
        ++ bitsMSB (parityOf β).length (BM.R β) := by
  rw [fam_binTail_X0 hpre hKn hτ hu]
  have hsm := fam_s_le hpre
  have hr : bitsMSB (parityOf β).length (BM.R β)
      = bitsMSB ((parityOf β).length - (parityOf β₀).length) (famRtop BM β₀ β) ++
        bitsMSB (parityOf β₀).length (BM.R β₀) := by
    rw [fam_terrasR_split hpre]
    have := bitsMSB_add_mul ((parityOf β).length - (parityOf β₀).length) (parityOf β₀).length
      (famRtop BM β₀ β) (BM.R β₀) (fam_rtop_lt hpre) (BM.R_lt _)
    rwa [Nat.sub_add_cancel hsm] at this
  rw [hr]
  simp only [List.append_assoc]

/-- Shape of the digits of the starting point: `bin'(x₀) = pre₀ ++ S₁ ++ w*L ++ u* ++ z`, `pre₀ = bin'(τ) · u · ρ · r'`. -/
theorem binTail_X0_shape {β₀ β : List Bool} (hpre : β₀ <+: β) {n K τ x : ℕ}
    (hKn : K + (parityOf β₀).length ≤ n) (hτ : 1 ≤ τ) (hx : x < 2 ^ (n - K - (parityOf β₀).length))
    (S₁ ws us z : Word)
    (hS : bitsMSB (parityOf β₀).length (BM.R β₀) = S₁ ++ ws ++ us ++ z) :
    binTail (famX0 BM β₀ β n K τ x) =
      (binTail τ ++ bitsMSB (n - K - (parityOf β₀).length) x ++
        (bitsMSB (parityOf β₀).length (famRho BM β₀ β) ++
          bitsMSB ((parityOf β).length - (parityOf β₀).length) (famRtop BM β₀ β))) ++
        (S₁ ++ ws) ++ us ++ z := by
  rw [fam_binTail_X0 hpre hKn hτ hx, hS]
  simp only [List.append_assoc]

/-- Shape of the digits of the end point: `bin'(x₁) = pre₁ ++ S₁ ++ w*L ++ u* ++ z`, `pre₁ = bin'(h) · upper part of ϖ · middle part of ϖ`. -/
theorem binTail_X1_shape {β₀ β : List Bool} {n K τ x : ℕ} (hK : 1 ≤ K)
    (hKn : K + (parityOf β₀).length ≤ n) (hτ1 : 2 ^ (K - 1) ≤ τ) (hA : 1 ≤ terrasA (parityOf β))
    (S₁ ws us z : Word)
    (hS : bitsMSB (parityOf β₀).length (BM.R β₀) = S₁ ++ ws ++ us ++ z) :
    binTail (famX1 BM β₀ β n K τ x) =
      (binTail (famX1 BM β₀ β n K τ x / 2 ^ n) ++
        bitsMSB K (famX1 BM β₀ β n K τ x % 2 ^ n / 2 ^ (n - K)) ++
        bitsMSB (n - K - (parityOf β₀).length)
          (famX1 BM β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)) ++
        (S₁ ++ ws) ++ us ++ z := by
  rw [fam_binTail_X1 (BM := BM) (β₀ := β₀) (β := β) (n := n) (K := K) (τ := τ) x hK (by omega) hτ1 hA,
    fam_bitsMSB_varpi τ x hKn, hS]
  simp only [List.append_assoc]

/-! ## The event of the lower bound at the end point -/

/-- **The event of the lower bound at the end point** (Lemma 6.6 applied to `x₁`). -/
theorem low_count (hSP : HSP) (A : Interp D) (u₀ : Fin D → Arc) {K₀ : Set (BRel (Fin D))}
    (hK : IsMinIdeal (Mon (B0 A) (B1 A)) K₀) {E : BRel (Fin D)} (hEK : E ∈ K₀) (hE : E * E = E)
    (us : Word) (hus : IsDigits us) (huE : suppRel (ev A us) = E) (y z : Word) (hy : IsDigits y)
    (hyu : us <:+ y) (G : ℕ) :
    ∃ Cst : ℝ, ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (β₀ β : List Bool) (n K τ b Δ : ℕ),
      1 ≤ K → K + (parityOf β₀).length ≤ n → 2 ^ (K - 1) ≤ τ → τ < 2 ^ K →
      2 ^ (b + Δ + K) ≤ 3 ^ terrasA (parityOf β) → 3 ^ terrasA (parityOf β) < 2 ^ (b + (K + Δ + 1)) →
      K + Δ ≤ G → L₀ ≤ b → L₀ ≤ n - K - (parityOf β₀).length →
      bitsMSB (parityOf β₀).length (BM.R β₀) = y ++ z →
      (1 - ((3 : ℝ) / 2 ^ Δ + 2 ^ ((parityOf β₀).length + 2) * 3 ^ terrasA (parityOf β) / 2 ^ n) / 2
          - ε) * 2 ^ (n - K - (parityOf β₀).length) ≤
        (((Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun x =>
          Lower.LowerAt u₀ A hE us z ε Cst (binTail (famX1 BM β₀ β n K τ x)))).card : ℝ) := by
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
      binTail (famX1 BM β₀ β n K τ x) =
      binTail (famX1 BM β₀ β n K τ x / 2 ^ n / 2 ^ b) ++
        bitsMSB b (famX1 BM β₀ β n K τ x / 2 ^ n % 2 ^ b) ++
        bitsMSB K (famX1 BM β₀ β n K τ x % 2 ^ n / 2 ^ (n - K)) ++
        bitsMSB (n - K - (parityOf β₀).length)
          (famX1 BM β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length) ++ y ++ z := by
    intro x _
    have h1 := fam_binTail_X1 (BM := BM) (β₀ := β₀) (β := β) (n := n) (K := K) (τ := τ) x
      hK1 hKn' hτ1 hA
    have hhb := (fam_h_low (BM := BM) (β₀ := β₀) (β := β) (n := n) (K := K) (τ := τ) x b Δ
      hK1 hKn' hτ1 hb1).1
    have h2b : 2 ^ b ≤ famX1 BM β₀ β n K τ x / 2 ^ n :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hhb
    rw [h1, fam_binTail_divmod _ b h2b, fam_bitsMSB_varpi τ x hKn, hS]
    simp only [List.append_assoc]
  have hlen₀ : ∀ x ∈ Finset.range (2 ^ (n - K - (parityOf β₀).length)),
      (binTail (famX1 BM β₀ β n K τ x / 2 ^ n / 2 ^ b)).length ≤ G := by
    intro x hx
    have h := fam_h_high (BM := BM) (β₀ := β₀) (β := β) (n := n) (K := K) (τ := τ) (u := x) b Δ
      hKn hτ2 (Finset.mem_range.mp hx) hb2
    have e : lenT (famX1 BM β₀ β n K τ x / 2 ^ n / 2 ^ b) =
        (binTail (famX1 BM β₀ β n K τ x / 2 ^ n / 2 ^ b)).length := rfl
    omega
  have hcard : ((Finset.range (2 ^ (n - K - (parityOf β₀).length))).card : ℝ) =
      2 ^ (n - K - (parityOf β₀).length) := by
    rw [Finset.card_range]; push_cast; ring
  -- total variation distance
  have htv1 := tv_bitsMSB (Finset.range (2 ^ (n - K - (parityOf β₀).length))) b
    (fun x => famX1 BM β₀ β n K τ x / 2 ^ n % 2 ^ b) (fun x _ => Nat.mod_lt _ (by positivity))
    ((3 : ℝ) / 2 ^ Δ + 2 ^ ((parityOf β₀).length + 2) * 3 ^ terrasA (parityOf β) / 2 ^ n)
    (by
      rw [hcard]
      have hq := fam_end_tv (BM := BM) β₀ β τ b Δ hKn hb1
      have hr := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at hr
      exact hr)
  have htv2 := tv_bitsMSB_exact (n - K - (parityOf β₀).length)
    (fun x => famX1 BM β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)
    (fun x hx => Finset.mem_range.mp (Finset.mem_coe.mp ((fam_mid_bijOn β₀ β τ hKn).mapsTo
      (Finset.mem_coe.mpr hx))))
    (fun j hj => fam_mid_card β₀ β τ hKn j hj)
  have hmain := hL₀ b (n - K - (parityOf β₀).length) hLb hLF
    (Finset.range (2 ^ (n - K - (parityOf β₀).length)))
    (fun x => binTail (famX1 BM β₀ β n K τ x / 2 ^ n / 2 ^ b))
    (fun x => bitsMSB K (famX1 BM β₀ β n K τ x % 2 ^ n / 2 ^ (n - K)))
    (fun x => bitsMSB b (famX1 BM β₀ β n K τ x / 2 ^ n % 2 ^ b))
    (fun x => bitsMSB (n - K - (parityOf β₀).length)
      (famX1 BM β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length)) _ 0 hlen₀
    (fun x _ => ⟨bitsMSB_isDigits _ _, by rw [bitsMSB_length]; omega⟩)
    (fun x _ => bitsMSB_mem_wordsOfLen _ _) (fun x _ => bitsMSB_mem_wordsOfLen _ _) htv1 htv2
  have hfil : (Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun x =>
        Lower.LowerAt u₀ A hE us z ε Cst
          (binTail (famX1 BM β₀ β n K τ x / 2 ^ n / 2 ^ b) ++
            bitsMSB b (famX1 BM β₀ β n K τ x / 2 ^ n % 2 ^ b) ++
            bitsMSB K (famX1 BM β₀ β n K τ x % 2 ^ n / 2 ^ (n - K)) ++
            bitsMSB (n - K - (parityOf β₀).length)
              (famX1 BM β₀ β n K τ x % 2 ^ n % 2 ^ (n - K) / 2 ^ (parityOf β₀).length) ++ y ++ z)) =
      (Finset.range (2 ^ (n - K - (parityOf β₀).length))).filter (fun x =>
        Lower.LowerAt u₀ A hE us z ε Cst (binTail (famX1 BM β₀ β n K τ x))) :=
    Finset.filter_congr (fun x hx => by rw [hdec x hx])
  rw [hfil, hcard] at hmain
  linarith

end Collatz.Arctic.Gen
