/-
  Two-ports and their Möbius form.

  A two-port is a network with two ports `s, t` and an observed edge `e`.  Its open-circuit
  data are three numbers of the network with `e` removed:
    `S`  port resistance,
    `P`  resistance seen from the two ends of `e`,
    `Q`  voltage across the ends of `e` under unit feed at the ports.
  When `e` carries resistance `r`, the port resistance and the current through `e` are
    `R(r) = (S r + (S P - Q²)) / (r + P)`,   `J(r) = Q / (r + P)`      (`resp_of_data`),
  so the two-port is described by the matrix `!![S, S P - Q²; 1, P]`, whose determinant is
  `Q²` (`det_mobM`).  The integer form used in the notes is this matrix scaled by
  `γ = τ(H - e)`; the reading of the scaled entries as spanning-tree counts is the
  matrix-tree theorem and is NOT formalized here.
-/
import TwoPort.Subst

open Finset

set_option linter.unusedSectionVars false

namespace TwoPort

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A two-port: a network, two ports and an observed edge. -/
structure Port (V E : Type) extends Net V E where
  s : V
  t : V
  e : E

namespace Port
variable (X : Port V E)

/-- The network with the observed edge given resistance `r`. -/
def withRes (r : ℝ) : Net V E := { X.toNet with res := Function.update X.res X.e r }

/-- Response of the two-port when the observed edge has resistance `r`: port resistance `R`
and current `J` through the observed edge, under unit feed at the ports. -/
def Resp (r R J : ℝ) : Prop :=
  ∃ φ, (X.withRes r).IsSol (feed X.s X.t) φ ∧ φ X.s - φ X.t = R ∧ (X.withRes r).cur φ X.e = J

/-- Open-circuit data of the two-port (observed edge removed). -/
def Data (S P Q : ℝ) : Prop :=
  ∃ φa φb, X.toNet.IsSolOn (univ.erase X.e) (feed (X.src X.e) (X.tgt X.e)) φa ∧
    X.toNet.IsSolOn (univ.erase X.e) (feed X.s X.t) φb ∧
    φa (X.src X.e) - φa (X.tgt X.e) = P ∧ φb X.s - φb X.t = S ∧
    φb (X.src X.e) - φb (X.tgt X.e) = Q

theorem withRes_cur_ne (r : ℝ) (φ : V → ℝ) {i : E} (h : i ≠ X.e) :
    (X.withRes r).cur φ i = X.toNet.cur φ i := by
  simp [Net.cur, Net.drop, withRes, Function.update_of_ne h]

theorem withRes_cur_e (r : ℝ) (φ : V → ℝ) :
    (X.withRes r).cur φ X.e = X.toNet.drop φ X.e / r := by
  simp [Net.cur, Net.drop, withRes]

/-- Kirchhoff's law of `X.withRes r`, split into the network without `e` and the edge `e`. -/
theorem withRes_divOn (r : ℝ) (φ : V → ℝ) (v : V) :
    (X.withRes r).divOn univ φ v =
      X.toNet.divOn (univ.erase X.e) φ v + X.toNet.inc v X.e * (X.toNet.drop φ X.e / r) := by
  simp only [Net.divOn]
  rw [← Finset.add_sum_erase univ _ (Finset.mem_univ X.e), X.withRes_cur_e, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [X.withRes_cur_ne r φ (Finset.ne_of_mem_erase hi)]
  rfl

theorem inc_eq_feed (v : V) : X.toNet.inc v X.e = feed (X.src X.e) (X.tgt X.e) v := by
  simp only [Net.inc, feed, eq_comm]

/-- **Möbius form.**  From the open-circuit data, the response for every resistance `r` of
the observed edge. -/
theorem resp_of_data {S P Q : ℝ} (h : X.Data S P Q) {r : ℝ} (hr : r ≠ 0) (hrP : r + P ≠ 0) :
    X.Resp r ((S * r + (S * P - Q ^ 2)) / (r + P)) (Q / (r + P)) := by
  obtain ⟨φa, φb, ha, hb, hP, hS, hQ⟩ := h
  have hrec : φa X.s - φa X.t = Q := by
    rw [← hQ]; exact (X.toNet.reciprocity hb ha).symm
  set J : ℝ := Q / (r + P) with hJ
  set φ : V → ℝ := φb + (-J) • φa + fun _ => (0:ℝ) with hφ
  have hsol := hb.comb X.toNet ha (-J) 0
  have hdrop : X.toNet.drop φ X.e = J * r := by
    have : X.toNet.drop φ X.e = Q - J * P := by
      simp only [hφ, Net.drop, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hQ, ← hP]; ring
    rw [this, hJ]; field_simp; ring
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro v
    rw [X.withRes_divOn, hsol v, hdrop, X.inc_eq_feed]
    field_simp
    ring
  · have : φ X.s - φ X.t = S - J * Q := by
      simp only [hφ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hS, ← hrec]; ring
    rw [this, hJ]; field_simp; ring
  · rw [X.withRes_cur_e, hdrop]; field_simp

/-! ### Signs of the data (positive resistances off the observed edge) -/

theorem energy_feed {T : Finset E} {x y : V} {φ : V → ℝ}
    (h : X.toNet.IsSolOn T (feed x y) φ) :
    φ x - φ y = ∑ i ∈ T, (X.toNet.drop φ i) ^ 2 / X.res i := by
  rw [← sum_mul_feed φ x y, X.toNet.energy h]
  exact Finset.sum_congr rfl fun i _ => by simp only [Net.cur]; ring

variable {X}

theorem Data.P_nonneg {S P Q : ℝ} (h : X.Data S P Q)
    (hpos : ∀ i, i ≠ X.e → 0 < X.res i) : 0 ≤ P := by
  obtain ⟨φa, φb, ha, hb, hP, hS, hQ⟩ := h
  rw [← hP, X.energy_feed ha]
  exact Finset.sum_nonneg fun i hi =>
    div_nonneg (sq_nonneg _) (hpos i (Finset.ne_of_mem_erase hi)).le

theorem Data.S_pos {S P Q : ℝ} (h : X.Data S P Q)
    (hpos : ∀ i, i ≠ X.e → 0 < X.res i) (hst : X.s ≠ X.t) : 0 < S := by
  obtain ⟨φa, φb, ha, hb, hP, hS, hQ⟩ := h
  have hnn : ∀ i ∈ univ.erase X.e, 0 ≤ (X.toNet.drop φb i) ^ 2 / X.res i := fun i hi =>
    div_nonneg (sq_nonneg _) (hpos i (Finset.ne_of_mem_erase hi)).le
  have hE := X.energy_feed hb
  rw [hS] at hE
  rcases (Finset.sum_nonneg hnn).lt_or_eq with hlt | heq
  · rw [hE]; exact hlt
  · exfalso
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 heq.symm
    have hcur : ∀ i ∈ univ.erase X.e, X.toNet.cur φb i = 0 := by
      intro i hi
      have h0 := hz i hi
      have hres := (hpos i (Finset.ne_of_mem_erase hi)).ne'
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · simp only [Net.cur, pow_eq_zero_iff (two_ne_zero) |>.1 h0, zero_div]
      · exact absurd h0 hres
    have hdiv : X.toNet.divOn (univ.erase X.e) φb X.s = 0 := by
      simp only [Net.divOn]
      exact Finset.sum_eq_zero fun i hi => by rw [hcur i hi, mul_zero]
    have := hb X.s
    rw [hdiv] at this
    simp [feed, hst] at this

theorem Data.sq_le {S P Q : ℝ} (h : X.Data S P Q)
    (hpos : ∀ i, i ≠ X.e → 0 < X.res i) : Q ^ 2 ≤ S * P := by
  obtain ⟨φa, φb, ha, hb, hP, hS, hQ⟩ := h
  have hrec : φa X.s - φa X.t = Q := by
    rw [← hQ]; exact (X.toNet.reciprocity hb ha).symm
  have hquad : ∀ c : ℝ, 0 ≤ P * (c * c) + 2 * Q * c + S := by
    intro c
    set χ : V → ℝ := φb + c • φa + fun _ => (0:ℝ) with hχ
    have hsol : X.toNet.IsSolOn (univ.erase X.e)
        (fun v => feed X.s X.t v + c * feed (X.src X.e) (X.tgt X.e) v) χ :=
      hb.comb X.toNet ha c 0
    have hE := X.toNet.energy hsol
    have h1 : χ X.s - χ X.t = S + c * Q := by
      simp only [hχ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hS, ← hrec]; ring
    have h2 : χ (X.src X.e) - χ (X.tgt X.e) = Q + c * P := by
      simp only [hχ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← hQ, ← hP]; ring
    have hL : ∑ v, χ v * (feed X.s X.t v + c * feed (X.src X.e) (X.tgt X.e) v)
        = P * (c * c) + 2 * Q * c + S := by
      have e3 : ∑ v, χ v * (feed X.s X.t v + c * feed (X.src X.e) (X.tgt X.e) v)
          = ∑ v, χ v * feed X.s X.t v + c * ∑ v, χ v * feed (X.src X.e) (X.tgt X.e) v := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [e3, sum_mul_feed, sum_mul_feed, h1, h2]; ring
    rw [← hL, hE]
    refine Finset.sum_nonneg fun i hi => ?_
    have : X.toNet.drop χ i * X.toNet.cur χ i = (X.toNet.drop χ i) ^ 2 / X.res i := by
      simp only [Net.cur]; ring
    rw [this]
    exact div_nonneg (sq_nonneg _) (hpos i (Finset.ne_of_mem_erase hi)).le
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  nlinarith [hd]

end Port

/-- The Möbius matrix of a two-port with open-circuit data `S, P, Q`. -/
def mobM (S P Q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![S, S * P - Q ^ 2; 1, P]

/-- `det M = κ²` in normalized form: the determinant is the square of the transfer number. -/
theorem det_mobM (S P Q : ℝ) : (mobM S P Q).det = Q ^ 2 := by
  simp [mobM, Matrix.det_fin_two]

end TwoPort
