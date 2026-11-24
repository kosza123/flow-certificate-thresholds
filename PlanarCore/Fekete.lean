/-
  T3 (Fekete step) of the paper, Appendix A, plus the algebra of the substitution lemma and an
  exponential spanning-tree bound for multigraphs.

  INFORMAL HYPOTHESES (not derived here):
  * `hmul` = planar substitution lemma, `Λ^face_{p+q} ≥ Λ^face_p · Λ^face_q` (p, q ≥ 1).
  * `h1` = `1 ≤ Λ^face_q` for q ≥ 1 (path witness; |I_e| ≤ 1, see `current_abs_le_one`).
  * `hδ` = `Λ^face_q ≤ T_q ≤ δ^q` (Kirchhoff with integer κ ≥ 1, see
    `inv_current_le_trees`, then an exponential bound on T_q).  For the *existence* of the
    limit any exponential bound suffices; `multigraph_tree_bound` gives δ' = exp(2/e) ≈ 2.087
    for all loopless-in-Laplacian multigraphs from AM–GM on Laplacian eigenvalues
    (matrix-tree + trace = 2q is the informal input there).
  * `Λ 0` is unconstrained: Appendix A defines `Λ^face_q` only for q ≥ 1.
-/
import Mathlib

namespace PlanarCore

open Filter Topology

/-- Fekete core: all hypotheses for every `n : ℕ` (forces `Λ 0 = 1`). -/
theorem fekete_core (Λ : ℕ → ℝ) (δ : ℝ) (h1 : ∀ n, 1 ≤ Λ n) (hδ : ∀ n, Λ n ≤ δ ^ n)
    (hmul : ∀ p q, Λ p * Λ q ≤ Λ (p + q)) :
    ∃ L, Tendsto (fun n : ℕ => Λ n ^ (1 / (n:ℝ))) atTop (𝓝 L) ∧
      ∀ n, 1 ≤ n → Λ n ^ (1 / (n:ℝ)) ≤ L := by
  have hpos : ∀ n, 0 < Λ n := fun n => lt_of_lt_of_le one_pos (h1 n)
  set u : ℕ → ℝ := fun n => -Real.log (Λ n) with hu
  have hsub : Subadditive u := by
    intro m n
    simp only [hu]
    have := Real.log_le_log (mul_pos (hpos m) (hpos n)) (hmul m n)
    rw [Real.log_mul (hpos m).ne' (hpos n).ne'] at this
    linarith
  have hδ1 : 1 ≤ δ := by simpa using (h1 1).trans (hδ 1)
  have hbdd : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨-Real.log δ, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.log_nonneg hδ1]
    · have hnr : (0:ℝ) < n := by exact_mod_cast hn
      have hlog : Real.log (Λ n) ≤ n * Real.log δ := by
        rw [← Real.log_pow]
        exact Real.log_le_log (hpos n) (hδ n)
      simp only [hu]
      rw [le_div_iff₀ hnr]; nlinarith
  have ht := hsub.tendsto_lim hbdd
  have hrw : ∀ n : ℕ, Λ n ^ (1 / (n:ℝ)) = Real.exp (-(u n / n)) := by
    intro n
    rw [Real.rpow_def_of_pos (hpos n)]
    simp only [hu]
    congr 1; ring
  refine ⟨Real.exp (-hsub.lim), ?_, ?_⟩
  · have hc := ((Real.continuous_exp.comp continuous_neg).tendsto _).comp ht
    refine hc.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp]
    rw [hrw n]
  · intro n hn
    rw [hrw n]
    apply Real.exp_le_exp.2
    have := hsub.lim_le_div hbdd (by omega : n ≠ 0)
    linarith

/-- **T3 (Fekete step).**  Hypotheses only for `n ≥ 1`.  The `n`-th roots converge, and
the limit is the least upper bound (hence `sSup`) of `{Λ n ^ (1/n) | n ≥ 1}`. -/
theorem T3_fekete (Λ : ℕ → ℝ) (δ : ℝ)
    (h1 : ∀ n, 1 ≤ n → 1 ≤ Λ n) (hδ : ∀ n, 1 ≤ n → Λ n ≤ δ ^ n)
    (hmul : ∀ p q, 1 ≤ p → 1 ≤ q → Λ p * Λ q ≤ Λ (p + q)) :
    ∃ L, Tendsto (fun n : ℕ => Λ n ^ (1 / (n:ℝ))) atTop (𝓝 L) ∧
      IsLUB {x | ∃ n, 1 ≤ n ∧ x = Λ n ^ (1 / (n:ℝ))} L ∧
      L = sSup {x | ∃ n, 1 ≤ n ∧ x = Λ n ^ (1 / (n:ℝ))} := by
  set Λ' : ℕ → ℝ := fun n => if n = 0 then 1 else Λ n with hΛ'
  have hδ1 : 1 ≤ δ := by simpa using (h1 1 le_rfl).trans (hδ 1 le_rfl)
  have h1' : ∀ n, 1 ≤ Λ' n := by
    intro n; by_cases hn : n = 0
    · simp [hΛ', hn]
    · simp only [hΛ', hn, ite_false]; exact h1 n (Nat.one_le_iff_ne_zero.2 hn)
  have hδ' : ∀ n, Λ' n ≤ δ ^ n := by
    intro n; by_cases hn : n = 0
    · simp [hΛ', hn]
    · simp only [hΛ', hn, ite_false]; exact hδ n (Nat.one_le_iff_ne_zero.2 hn)
  have hmul' : ∀ p q, Λ' p * Λ' q ≤ Λ' (p + q) := by
    intro p q
    by_cases hp : p = 0
    · subst hp; simp [hΛ']
    by_cases hq : q = 0
    · subst hq; simp [hΛ']
    have hpq : p + q ≠ 0 := by omega
    simp only [hΛ', hp, hq, hpq, ite_false]
    exact hmul p q (Nat.one_le_iff_ne_zero.2 hp) (Nat.one_le_iff_ne_zero.2 hq)
  obtain ⟨L, hL, hle⟩ := fekete_core Λ' δ h1' hδ' hmul'
  have heq : ∀ n, 1 ≤ n → Λ' n = Λ n := by
    intro n hn; simp [hΛ', Nat.one_le_iff_ne_zero.1 hn]
  have hT : Tendsto (fun n : ℕ => Λ n ^ (1 / (n:ℝ))) atTop (𝓝 L) := by
    refine hL.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [heq n hn]
  have hlub : IsLUB {x | ∃ n, 1 ≤ n ∧ x = Λ n ^ (1 / (n:ℝ))} L := by
    constructor
    · rintro _ ⟨n, hn, rfl⟩
      have := hle n hn; rwa [heq n hn] at this
    · intro M hM
      refine le_of_tendsto hT ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact hM ⟨n, hn, rfl⟩
  exact ⟨L, hT, hlub, (hlub.csSup_eq ⟨_, 1, le_rfl, rfl⟩).symm⟩

/-- **Substitution lemma, circuit algebra.**  `V0` is the open-circuit voltage of `G - uv`
between `u, v`, `R0 ≥ 0` its resistance, `RH = R_H(a,b) ≥ 0` the port resistance of `H`,
`iH` the current on the observed edge of `H` under unit feed at `a, b`.
Original current `I_uv = V0/(R0+1)`; substituted branch current `J = V0/(R0 + (1+RH))`.
The hypotheses `RH` finite (H connected) and `iH ≠ 0` (which needs `a ≠ b`) are exactly
the conditions stated in Appendix A of the paper: with `RH = ∞` the witness would vanish. -/
theorem substitution_bound (V0 R0 RH iH : ℝ) (hR0 : 0 ≤ R0) (hRH : 0 ≤ RH)
    (hV0 : V0 ≠ 0) (hiH : iH ≠ 0) :
    0 < |V0 / (R0 + (1 + RH)) * iH| ∧
      |V0 / (R0 + (1 + RH)) * iH| ≤ |V0 / (R0 + 1)| * |iH| := by
  have hd1 : 0 < R0 + 1 := by linarith
  have hd2 : 0 < R0 + (1 + RH) := by linarith
  refine ⟨abs_pos.2 (mul_ne_zero (div_ne_zero hV0 hd2.ne') hiH), ?_⟩
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [abs_div, abs_div, abs_of_pos hd1, abs_of_pos hd2]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hd1 (by linarith)

/-- Consequence in the `Λ = 1/|current|` scale: the new witness certifies at least
`(1/|I_uv|) · (1/|iH|)`. -/
theorem substitution_supermul (V0 R0 RH iH : ℝ) (hR0 : 0 ≤ R0) (hRH : 0 ≤ RH)
    (hV0 : V0 ≠ 0) (hiH : iH ≠ 0) :
    (1 / |V0 / (R0 + 1)|) * (1 / |iH|) ≤ 1 / |V0 / (R0 + (1 + RH)) * iH| := by
  obtain ⟨hpos, hle⟩ := substitution_bound V0 R0 RH iH hR0 hRH hV0 hiH
  rw [div_mul_div_comm, one_mul]
  exact one_div_le_one_div_of_le hpos hle

/-- AM–GM endgame for multigraphs: `(x/k)^k ≤ exp(x/e)`.  With `x = trace L ≤ 2q` and
`k = n - 1` this turns `T = (1/n) ∏ λ_i ≤ (2q/(n-1))^(n-1)` into `T ≤ exp(2/e)^q`. -/
theorem amgm_exp_bound (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    (x / k) ^ k ≤ Real.exp (x / Real.exp 1) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  rcases hx.eq_or_lt with rfl | hx
  · rw [zero_div, zero_pow (by omega)]; exact (Real.exp_pos _).le
  set t := x / k with ht
  have htpos : 0 < t := div_pos hx hkpos
  have hlog : Real.log t ≤ t / Real.exp 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos htpos (Real.exp_pos 1))
    rw [Real.log_div htpos.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
    linarith
  have hx' : x = k * t := by rw [ht]; field_simp
  calc t ^ k = Real.exp (k * Real.log t) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos htpos k)]
    _ ≤ Real.exp (x / Real.exp 1) := by
          apply Real.exp_le_exp.2
          rw [hx', mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hlog hkpos.le

/-- Multigraph tree bound in exponential form: `(2q/k)^k ≤ (exp (2/e))^q` for `k ≥ 1`. -/
theorem multigraph_tree_bound (q k : ℕ) (hk : 1 ≤ k) :
    ((2 * q : ℝ) / k) ^ k ≤ Real.exp (2 / Real.exp 1) ^ q := by
  rw [← Real.exp_natCast_mul]
  have := amgm_exp_bound (2 * q) (by positivity) k hk
  convert this using 2
  ring

end PlanarCore
