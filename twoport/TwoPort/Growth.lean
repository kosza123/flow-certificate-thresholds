/-
  Growth of the denominators.

  For a real 2×2 matrix `N` with determinant 1 and positive entries, `q_k` is the second
  coordinate of `N^k (1, 1)`.  Then `q_{k+2} = tr N · q_{k+1} - q_k`, and
  `q_{k+1} ≥ c · λ^k` with `c > 0` and `λ = (tr N + √(tr N² - 4)) / 2` the larger eigenvalue.
  No Perron–Frobenius theorem is needed.  `growth` turns this into a lower bound for the
  Fekete limit, with the planar bridge `q_k ≤ Λ (m k + 1)` as an explicit hypothesis.
-/
import TwoPort.Compose

open Finset Filter Topology

set_option linter.unusedSectionVars false

namespace TwoPort

/-- `q_k`: the second coordinate of `N^k (1, 1)`. -/
def qk (N : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) : ℝ := den (N ^ k) 1

/-- The larger eigenvalue of a 2×2 matrix of determinant 1 (trace > 2). -/
noncomputable def lam (N : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (N.trace + Real.sqrt (N.trace ^ 2 - 4)) / 2

variable {N : Matrix (Fin 2) (Fin 2) ℝ}

theorem qk_zero : qk N 0 = 1 := by simp [qk, den]

theorem qk_one : qk N 1 = N 1 0 + N 1 1 := by simp [qk, den]

/-- Cayley–Hamilton for a 2×2 matrix of determinant 1. -/
theorem sq_eq (hdet : N.det = 1) : N * N = N.trace • N - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | linear_combination (-1 : ℝ) * hdet | ring

theorem qk_succ_succ (hdet : N.det = 1) (k : ℕ) :
    qk N (k + 2) = N.trace * qk N (k + 1) - qk N k := by
  have h : N ^ (k + 2) = N.trace • N ^ (k + 1) - N ^ k := by
    rw [pow_add, pow_two, sq_eq hdet, mul_sub, mul_one, Matrix.mul_smul, ← pow_succ]
  simp only [qk, h, den, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem trace_gt_two (hdet : N.det = 1) (hpos : ∀ i j, 0 < N i j) : 2 < N.trace := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two]
  nlinarith [sq_nonneg (N 0 0 - N 1 1), mul_pos (hpos 0 1) (hpos 1 0), hpos 0 0, hpos 1 1]

/-- The two eigenvalues `λ` and `μ = tr N - λ`. -/
theorem lam_spec (hT : 2 < N.trace) :
    1 < lam N ∧ lam N * lam N = N.trace * lam N - 1 ∧ 0 < N.trace - lam N ∧
      (N.trace - lam N) * lam N = 1 ∧ N.trace - lam N ≤ lam N := by
  have hnn : 0 ≤ N.trace ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hnn
  have hs0 := Real.sqrt_nonneg (N.trace ^ 2 - 4)
  set s := Real.sqrt (N.trace ^ 2 - 4) with hsdef
  have hsT : s < N.trace := by nlinarith
  simp only [lam, ← hsdef]
  refine ⟨by linarith, by nlinarith, by linarith, by nlinarith, by linarith⟩

/-- The smaller eigenvalue is below the entry `N 1 1`. -/
theorem mu_lt (hdet : N.det = 1) (hpos : ∀ i j, 0 < N i j) : N.trace - lam N < N 1 1 := by
  obtain ⟨_, h2, _, _, h5⟩ := lam_spec (trace_gt_two hdet hpos)
  have hbc := mul_pos (hpos 0 1) (hpos 1 0)
  rw [Matrix.det_fin_two] at hdet
  by_contra hcon
  rw [not_lt] at hcon
  have hprod : 0 ≤ (N.trace - lam N - N 1 1) * (lam N - N 1 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hval : (N.trace - lam N - N 1 1) * (lam N - N 1 1) = -(N 0 1 * N 1 0) := by
    rw [Matrix.trace_fin_two] at h2 ⊢
    linear_combination (-1 : ℝ) * h2 + (-1 : ℝ) * hdet
  linarith

/-- Exact two-term form of the recurrence. -/
theorem qk_growth (hdet : N.det = 1) (hpos : ∀ i j, 0 < N i j) (k : ℕ) :
    0 ≤ qk N k ∧
      qk N (k + 1) - (N.trace - lam N) * qk N k = lam N ^ k * (qk N 1 - (N.trace - lam N)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := lam_spec (trace_gt_two hdet hpos)
  have hc0 : 0 < qk N 1 - (N.trace - lam N) := by
    rw [qk_one]; linarith [mu_lt hdet hpos, hpos 1 0]
  induction k with
  | zero => exact ⟨by rw [qk_zero]; exact zero_le_one, by rw [qk_zero]; ring⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · have hpow : 0 < lam N ^ k := pow_pos (by linarith) k
      nlinarith [mul_nonneg h3.le ih1, mul_pos hpow hc0]
    · rw [qk_succ_succ hdet k]
      linear_combination lam N * ih2 + qk N k * h4

/-- Exponential lower bound for the denominators. -/
theorem qk_lower (hdet : N.det = 1) (hpos : ∀ i j, 0 < N i j) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ k, c0 * lam N ^ k ≤ qk N (k + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := lam_spec (trace_gt_two hdet hpos)
  refine ⟨qk N 1 - (N.trace - lam N), ?_, fun k => ?_⟩
  · rw [qk_one]; linarith [mu_lt hdet hpos, hpos 1 0]
  · obtain ⟨hk1, hk2⟩ := qk_growth hdet hpos k
    nlinarith [mul_nonneg h3.le hk1]

theorem qk_pos (hdet : N.det = 1) (hpos : ∀ i j, 0 < N i j) (k : ℕ) : 0 < qk N k := by
  obtain ⟨h1, _, _, _, _⟩ := lam_spec (trace_gt_two hdet hpos)
  cases k with
  | zero => rw [qk_zero]; exact one_pos
  | succ k =>
    obtain ⟨c0, hc0, hq⟩ := qk_lower hdet hpos
    exact lt_of_lt_of_le (mul_pos hc0 (pow_pos (by linarith) k)) (hq k)

/-- Row sums bound the eigenvalue from below (Collatz–Wielandt for 2×2, determinant 1). -/
theorem min_rowSum_le_lam (hdet : N.det = 1) (hpos : ∀ i j, 0 < N i j) :
    min (N 0 0 + N 0 1) (N 1 0 + N 1 1) ≤ lam N := by
  obtain ⟨_, h2, _, h4, h5⟩ := lam_spec (trace_gt_two hdet hpos)
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at h2 h4 h5
  by_contra hcon
  rw [not_le] at hcon
  rcases le_total (N 0 0 + N 0 1) (N 1 0 + N 1 1) with h | h
  · rw [min_eq_left h] at hcon
    have hp : 0 < (N 0 0 + N 0 1 - lam N) * (N 0 0 + N 0 1 - (N 0 0 + N 1 1 - lam N)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [mul_nonneg (hpos 0 1).le (sub_nonneg.2 h)]
  · rw [min_eq_right h] at hcon
    have hp : 0 < (N 1 0 + N 1 1 - lam N) * (N 1 0 + N 1 1 - (N 0 0 + N 1 1 - lam N)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [mul_nonneg (hpos 1 0).le (sub_nonneg.2 h)]

/-- **Growth.**  If `Λ` has Fekete limit `L` (the least upper bound of its `n`-th roots, as
given by `PlanarCore.T3_fekete`) and `q_k ≤ Λ (m k + 1)` for every `k`, then
`λ^{1/m} ≤ L`. -/
theorem growth (Λ : ℕ → ℝ) (L : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hLUB : IsLUB {x | ∃ n, 1 ≤ n ∧ x = Λ n ^ (1 / (n:ℝ))} L)
    (hdet : N.det = 1) (hpos : ∀ i j, 0 < N i j)
    (hbridge : ∀ k, qk N k ≤ Λ (m * k + 1)) :
    lam N ^ (1 / (m:ℝ)) ≤ L := by
  obtain ⟨c0, hc0, hq⟩ := qk_lower hdet hpos
  obtain ⟨hlam1, _, _, _, _⟩ := lam_spec (trace_gt_two hdet hpos)
  have hlam0 : 0 < lam N := by linarith
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  set n : ℕ → ℕ := fun k => m * (k + 1) + 1 with hn
  have hnpos : ∀ k, (0:ℝ) < (n k : ℝ) := fun k => by
    have : 0 < n k := by simp [hn]
    exact_mod_cast this
  have hbound : ∀ k, (c0 * lam N ^ k) ^ (1 / (n k : ℝ)) ≤ L := by
    intro k
    have h1 : c0 * lam N ^ k ≤ Λ (n k) := (hq k).trans (hbridge (k + 1))
    have h0 : 0 ≤ c0 * lam N ^ k := (mul_pos hc0 (pow_pos hlam0 k)).le
    have h2 : (c0 * lam N ^ k) ^ (1 / (n k : ℝ)) ≤ Λ (n k) ^ (1 / (n k : ℝ)) :=
      Real.rpow_le_rpow h0 h1 (div_nonneg zero_le_one (hnpos k).le)
    exact h2.trans (hLUB.1 ⟨n k, by simp [hn], rfl⟩)
  have hu : Tendsto (fun k => 1 / (n k : ℝ)) atTop (𝓝 0) :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_atTop_mono (fun k => by show k ≤ m * (k + 1) + 1; nlinarith [hm, Nat.zero_le k])
        tendsto_id)
  have hexp : Tendsto (fun k : ℕ => (k:ℝ) * (1 / (n k : ℝ))) atTop (𝓝 (1 / (m:ℝ))) := by
    have h1 : Tendsto (fun k : ℕ => (1 / (m:ℝ)) * (1 - ((m:ℝ) + 1) * (1 / (n k : ℝ)))) atTop
        (𝓝 ((1 / (m:ℝ)) * (1 - ((m:ℝ) + 1) * 0))) :=
      (tendsto_const_nhds.sub (hu.const_mul _)).const_mul _
    have h2 : (1 / (m:ℝ)) * (1 - ((m:ℝ) + 1) * 0) = 1 / (m:ℝ) := by ring
    rw [h2] at h1
    refine h1.congr fun k => ?_
    have hk := (hnpos k).ne'
    have hcast : (n k : ℝ) = (m:ℝ) * ((k:ℝ) + 1) + 1 := by simp [hn]
    field_simp
    rw [hcast]; ring
  have hlim : Tendsto (fun k => (c0 * lam N ^ k) ^ (1 / (n k : ℝ))) atTop
      (𝓝 (lam N ^ (1 / (m:ℝ)))) := by
    have ha : Tendsto (fun k => c0 ^ (1 / (n k : ℝ))) atTop (𝓝 (c0 ^ (0:ℝ))) :=
      (Real.continuousAt_const_rpow hc0.ne').tendsto.comp hu
    have hb : Tendsto (fun k : ℕ => lam N ^ ((k:ℝ) * (1 / (n k : ℝ)))) atTop
        (𝓝 (lam N ^ (1 / (m:ℝ)))) :=
      (Real.continuousAt_const_rpow hlam0.ne').tendsto.comp hexp
    have hab := ha.mul hb
    rw [Real.rpow_zero, one_mul] at hab
    refine hab.congr fun k => ?_
    rw [Real.mul_rpow hc0.le (pow_pos hlam0 k).le, ← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]
  exact le_of_tendsto' hlim hbound

end TwoPort
