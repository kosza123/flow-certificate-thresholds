/-
  One non-vacuous example, the 11-edge gadget H7.

  Edges 04 05 06 13 15 16 23 24 26 36 45, ports 3 and 4, observed edge (0, 5).
  Its open-circuit data are `S = 83/98`, `P = 111/98`, `Q = -1/98`, certified by two explicit
  potentials of H7 without its observed edge.  The normalized matrix is
  `!![83, 94; 98, 111]` (determinant 1, trace 194), so the `k`-fold nesting has `10 k + 1`
  edges and observed current `± 1 / q_k` with `q_0 = 1`, `q_1 = 209`,
  `q_{k+2} = 194 q_{k+1} - q_k`.  No catalogue records are formalized.
-/
import TwoPort.Main

open Finset Filter Topology

namespace TwoPort.H7

/-- The gadget H7 as a two-port. -/
def port : Port (Fin 7) (Fin 11) where
  src := ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 4]
  tgt := ![4, 5, 6, 3, 5, 6, 3, 4, 6, 6, 5]
  res := fun _ => 1
  s := 3
  t := 4
  e := 1

/-- H7 with its vertex and edge types. -/
def tp : TP where
  V := Fin 7
  E := Fin 11
  port := port

/-- Potential of H7 without its observed edge, unit feed at the ends of that edge. -/
noncomputable def φa : Fin 7 → ℝ := fun v => ![0, -70, -51, -55, -54, -111, -44] v / 98

/-- Potential of H7 without its observed edge, unit feed at the ports. -/
noncomputable def φb : Fin 7 → ℝ := fun v => ![0, 28, 19, 57, -26, 1, 26] v / 98

theorem data : port.Data (83 / 98) (111 / 98) (-1 / 98) := by
  refine ⟨φa, φb, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    simp only [Net.divOn]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    fin_cases v <;>
      simp [Fin.sum_univ_succ, Net.inc, Net.cur, Net.drop, port, φa, feed] <;> norm_num
  · intro v
    simp only [Net.divOn]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
    fin_cases v <;>
      simp [Fin.sum_univ_succ, Net.inc, Net.cur, Net.drop, port, φb, feed] <;> norm_num
  · simp [port, φa]; norm_num
  · simp [port, φb]; norm_num
  · simp [port, φb]; norm_num

/-- The normalized gadget of H7. -/
noncomputable def gadget : Gadget :=
  Gadget.ofData tp data (by norm_num) (by show (3 : Fin 7) ≠ 4; decide) (fun _ _ => rfl)

theorem gadget_M : gadget.M = !![83, 94; 98, 111] := by
  show |(-1 / 98 : ℝ)|⁻¹ • mobM (83 / 98) (111 / 98) (-1 / 98) = _
  have h : |(-1 / 98 : ℝ)| = 1 / 98 := by rw [abs_of_neg (by norm_num)]; norm_num
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mobM] <;> norm_num

theorem gadget_det : gadget.M.det = 1 := Gadget.ofData_det _ _ _ _ _

theorem gadget_abs_κ : |gadget.κ| = 1 := Gadget.ofData_abs_κ _ _ _ _ _

theorem gadget_pos : ∀ i j, 0 < gadget.M i j := by
  rw [gadget_M]
  intro i j
  fin_cases i <;> fin_cases j <;> simp

theorem gadget_card : Fintype.card gadget.tp.E = 10 + 1 := by
  show Fintype.card (Fin 11) = 11
  simp

theorem gadget_trace : gadget.M.trace = 194 := by
  rw [gadget_M, Matrix.trace_fin_two]; norm_num

/-! ### The denominators `q_k` of H7 -/

theorem q_zero : qk gadget.M 0 = 1 := qk_zero

theorem q_one : qk gadget.M 1 = 209 := by
  rw [qk_one, gadget_M]; norm_num

theorem q_rec (k : ℕ) : qk gadget.M (k + 2) = 194 * qk gadget.M (k + 1) - qk gadget.M k := by
  rw [qk_succ_succ gadget_det, gadget_trace]

/-- Cross-check with the exact graph computations in the notes: 40545 and 7865521. -/
theorem q_two : qk gadget.M 2 = 40545 := by
  rw [q_rec, q_one, q_zero]; norm_num

theorem q_three : qk gadget.M 3 = 7865521 := by
  rw [q_rec, q_two, q_one]; norm_num

/-- **H7, all levels.**  The `k`-fold self-substitution of H7 is a unit-resistance network
with `10 k + 1` edges.  Under unit feed at its ports it has a solution, and in every solution
the observed current has absolute value `1 / q_k`. -/
theorem iterate (k : ℕ) :
    Fintype.card (chain (List.replicate k gadget)).E = 10 * k + 1 ∧
    (∀ i, ((chain (List.replicate k gadget)).port.withRes 1).res i = 1) ∧
    0 < qk gadget.M k ∧
    (∃ φ, ((chain (List.replicate k gadget)).port.withRes 1).IsSol
      (feed (chain (List.replicate k gadget)).port.s
        (chain (List.replicate k gadget)).port.t) φ) ∧
    ∀ φ, ((chain (List.replicate k gadget)).port.withRes 1).IsSol
        (feed (chain (List.replicate k gadget)).port.s
          (chain (List.replicate k gadget)).port.t) φ →
      |((chain (List.replicate k gadget)).port.withRes 1).cur φ
          (chain (List.replicate k gadget)).port.e| = 1 / qk gadget.M k := by
  have h := iterate_current gadget gadget_abs_κ k
  rwa [gadget_card, Nat.add_sub_cancel] at h

/-! ### The growth constant of H7 -/

theorem lam_eq : lam gadget.M = 97 + 56 * Real.sqrt 3 := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs : Real.sqrt ((194:ℝ) ^ 2 - 4) = 112 * Real.sqrt 3 := by
    rw [show ((194:ℝ) ^ 2 - 4) = (112 * Real.sqrt 3) ^ 2 by rw [mul_pow, h3]; norm_num]
    exact Real.sqrt_sq (by positivity)
  unfold lam
  rw [gadget_trace, hs]
  ring

theorem lam_eq_pow : lam gadget.M = (2 + Real.sqrt 3) ^ 4 := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  rw [lam_eq]
  linear_combination (-(Real.sqrt 3 ^ 2 + 8 * Real.sqrt 3 + 27)) * h3

/-- **Conditional lower bound from H7.**  Under the hypotheses of the Fekete step and the
planar bridge for the iterated H7 networks, the growth limit is at least
`((2 + √3)^4)^{1/10} = (2 + √3)^{2/5}`. -/
theorem growth_bound (Λ : ℕ → ℝ) (δ : ℝ)
    (h1 : ∀ n, 1 ≤ n → 1 ≤ Λ n) (hδ : ∀ n, 1 ≤ n → Λ n ≤ δ ^ n)
    (hmul : ∀ p q, 1 ≤ p → 1 ≤ q → Λ p * Λ q ≤ Λ (p + q))
    (hbridge : ∀ k, ∀ φ,
      ((chain (List.replicate k gadget)).port.withRes 1).IsSol
        (feed (chain (List.replicate k gadget)).port.s
          (chain (List.replicate k gadget)).port.t) φ →
      |((chain (List.replicate k gadget)).port.withRes 1).cur φ
          (chain (List.replicate k gadget)).port.e|⁻¹
        ≤ Λ (Fintype.card (chain (List.replicate k gadget)).E)) :
    ∃ L, Tendsto (fun n : ℕ => Λ n ^ (1 / (n:ℝ))) atTop (𝓝 L) ∧
      ((2 + Real.sqrt 3) ^ 4) ^ (1 / (10:ℝ)) ≤ L := by
  obtain ⟨L, hT, hL⟩ := growth_fekete gadget gadget_det gadget_pos gadget_abs_κ 10
    (by norm_num) gadget_card Λ δ h1 hδ hmul hbridge
  refine ⟨L, hT, ?_⟩
  rw [← lam_eq_pow]
  exact_mod_cast hL

/-! ### The hypotheses are satisfiable

`Λ n = 2 ^ n` satisfies every hypothesis of `growth_bound`, so the theorem is not vacuous.
(This is only a consistency check: it does not say that `2 ^ n` is `Λ^face`.) -/

theorem q_le (k : ℕ) : qk gadget.M k ≤ 1024 ^ k ∧ qk gadget.M (k + 1) ≤ 1024 ^ (k + 1) := by
  induction k with
  | zero => exact ⟨by rw [q_zero]; norm_num, by rw [q_one]; norm_num⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [q_rec]
    have h0 := (qk_pos gadget_det gadget_pos k).le
    have h1 : (0:ℝ) < 1024 ^ (k + 1) := by positivity
    have h2 : (1024:ℝ) ^ (k + 1 + 1) = 1024 * 1024 ^ (k + 1) := by ring
    rw [h2]
    nlinarith [ih.2]

theorem bridge_consistent (k : ℕ) (φ : (chain (List.replicate k gadget)).V → ℝ)
    (hφ : ((chain (List.replicate k gadget)).port.withRes 1).IsSol
      (feed (chain (List.replicate k gadget)).port.s
        (chain (List.replicate k gadget)).port.t) φ) :
    |((chain (List.replicate k gadget)).port.withRes 1).cur φ
        (chain (List.replicate k gadget)).port.e|⁻¹
      ≤ (2:ℝ) ^ Fintype.card (chain (List.replicate k gadget)).E := by
  obtain ⟨hc, _, hq, _, hcur⟩ := iterate k
  rw [hcur φ hφ, hc, one_div, inv_inv]
  have h1 : (2:ℝ) ^ (10 * k + 1) = 2 * 1024 ^ k := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h1]
  have h2 : (0:ℝ) < 1024 ^ k := by positivity
  linarith [(q_le k).1]

theorem hypotheses_consistent :
    ∃ L, Tendsto (fun n : ℕ => ((2:ℝ) ^ n) ^ (1 / (n:ℝ))) atTop (𝓝 L) ∧
      ((2 + Real.sqrt 3) ^ 4) ^ (1 / (10:ℝ)) ≤ L :=
  growth_bound (fun n => 2 ^ n) 2
    (fun n _ => one_le_pow₀ (by norm_num))
    (fun n _ => le_rfl)
    (fun p q _ _ => by rw [pow_add])
    bridge_consistent

end TwoPort.H7
