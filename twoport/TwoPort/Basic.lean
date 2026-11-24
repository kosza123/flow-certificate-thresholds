/-
  Resistor networks by potentials.

  A network is a finite multigraph with a real resistance on every edge.  Everything is
  phrased through potentials `φ : V → ℝ` and Kirchhoff's current law, so no matrices,
  determinants or connectivity assumptions are needed:
  * `green`        discrete Green identity;
  * `cur_unique`   branch currents are determined by the feed (positive resistances);
  * `reciprocity`  transfer voltages are symmetric.
-/
import PlanarCore.Fekete

open Finset

set_option linter.unusedSectionVars false

namespace TwoPort

/-- A multigraph with vertices `V`, edges `E` and a resistance on every edge. -/
structure Net (V E : Type) where
  src : E → V
  tgt : E → V
  res : E → ℝ

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- Unit current fed in at `s` and drawn at `t`. -/
def feed (s t : V) (v : V) : ℝ := (if v = s then 1 else 0) - (if v = t then 1 else 0)

theorem sum_mul_feed (ψ : V → ℝ) (s t : V) : ∑ v, ψ v * feed s t v = ψ s - ψ t := by
  simp [feed, mul_sub, Finset.sum_sub_distrib]

namespace Net
variable (N : Net V E)

/-- Potential drop along an edge. -/
def drop (φ : V → ℝ) (i : E) : ℝ := φ (N.src i) - φ (N.tgt i)

/-- Ohm's law: the current through an edge, from `src` to `tgt`. -/
noncomputable def cur (φ : V → ℝ) (i : E) : ℝ := N.drop φ i / N.res i

/-- Signed incidence of the vertex `v` with the edge `i`. -/
def inc (v : V) (i : E) : ℝ := (if N.src i = v then 1 else 0) - (if N.tgt i = v then 1 else 0)

/-- Net current leaving `v` through the edges in `T`. -/
noncomputable def divOn (T : Finset E) (φ : V → ℝ) (v : V) : ℝ :=
  ∑ i ∈ T, N.inc v i * N.cur φ i

/-- Kirchhoff's current law on the edge set `T` with feed `b`. -/
def IsSolOn (T : Finset E) (b φ : V → ℝ) : Prop := ∀ v, N.divOn T φ v = b v

/-- Kirchhoff's current law on the whole network. -/
abbrev IsSol (b φ : V → ℝ) : Prop := N.IsSolOn univ b φ

theorem sum_mul_inc (ψ : V → ℝ) (i : E) : ∑ v, ψ v * N.inc v i = N.drop ψ i := by
  simp [inc, drop, mul_sub, Finset.sum_sub_distrib]

/-- Discrete Green identity. -/
theorem green (T : Finset E) (φ ψ : V → ℝ) :
    ∑ v, ψ v * N.divOn T φ v = ∑ i ∈ T, N.drop ψ i * N.cur φ i := by
  simp_rw [divOn, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← N.sum_mul_inc ψ i, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => by ring

/-! ### Linearity in the potential -/

theorem drop_add (φ ψ : V → ℝ) (i : E) : N.drop (φ + ψ) i = N.drop φ i + N.drop ψ i := by
  simp [drop]; ring

theorem drop_smul (c : ℝ) (φ : V → ℝ) (i : E) : N.drop (c • φ) i = c * N.drop φ i := by
  simp [drop]; ring

theorem drop_const (c : ℝ) (i : E) : N.drop (fun _ => c) i = 0 := by
  simp [drop]

theorem cur_add (φ ψ : V → ℝ) (i : E) : N.cur (φ + ψ) i = N.cur φ i + N.cur ψ i := by
  simp [cur, drop_add, add_div]

theorem cur_smul (c : ℝ) (φ : V → ℝ) (i : E) : N.cur (c • φ) i = c * N.cur φ i := by
  simp [cur, drop_smul, mul_div_assoc]

theorem cur_const (c : ℝ) (i : E) : N.cur (fun _ => c) i = 0 := by
  simp [cur, drop_const]

theorem divOn_add (T : Finset E) (φ ψ : V → ℝ) (v : V) :
    N.divOn T (φ + ψ) v = N.divOn T φ v + N.divOn T ψ v := by
  simp [divOn, cur_add, mul_add, Finset.sum_add_distrib]

theorem divOn_smul (T : Finset E) (c : ℝ) (φ : V → ℝ) (v : V) :
    N.divOn T (c • φ) v = c * N.divOn T φ v := by
  simp only [divOn, cur_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem divOn_const (T : Finset E) (c : ℝ) (v : V) : N.divOn T (fun _ => c) v = 0 := by
  simp [divOn, cur_const]

/-- Superposition: `φ + c • ψ + const` solves the combined feed. -/
theorem IsSolOn.comb {T : Finset E} {b b' φ ψ : V → ℝ} (h : N.IsSolOn T b φ)
    (h' : N.IsSolOn T b' ψ) (c d : ℝ) :
    N.IsSolOn T (fun v => b v + c * b' v) (φ + c • ψ + fun _ => d) := by
  intro v
  rw [divOn_add, divOn_add, divOn_smul, divOn_const, h v, h' v]
  ring

/-! ### Energy, uniqueness of currents, reciprocity -/

theorem energy {T : Finset E} {b φ : V → ℝ} (h : N.IsSolOn T b φ) :
    ∑ v, φ v * b v = ∑ i ∈ T, N.drop φ i * N.cur φ i := by
  rw [← N.green T φ φ]
  exact Finset.sum_congr rfl fun v _ => by rw [h v]

/-- With positive resistances the branch currents are determined by the feed. -/
theorem cur_unique {T : Finset E} (hpos : ∀ i ∈ T, 0 < N.res i) {b φ φ' : V → ℝ}
    (h : N.IsSolOn T b φ) (h' : N.IsSolOn T b φ') {i : E} (hi : i ∈ T) :
    N.cur φ i = N.cur φ' i := by
  have hδ : N.IsSolOn T (fun _ => 0) (φ + (-1 : ℝ) • φ' + fun _ => (0:ℝ)) := by
    have := h.comb N h' (-1) 0
    intro v; rw [this v]; ring
  have hE := N.energy hδ
  simp only [mul_zero, Finset.sum_const_zero] at hE
  set δ : V → ℝ := φ + (-1 : ℝ) • φ' + fun _ => (0:ℝ) with hδdef
  have hnn : ∀ j ∈ T, 0 ≤ N.drop δ j * N.cur δ j := by
    intro j hj
    have : N.drop δ j * N.cur δ j = (N.drop δ j) ^ 2 / N.res j := by
      simp only [cur]; ring
    rw [this]
    exact div_nonneg (sq_nonneg _) (hpos j hj).le
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hE.symm i hi
  have hd : N.drop δ i = 0 := by
    have hres := (hpos i hi).ne'
    have : N.drop δ i * N.cur δ i = (N.drop δ i) ^ 2 / N.res i := by
      simp only [cur]; ring
    rw [this, div_eq_zero_iff] at hz
    rcases hz with hz | hz
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 hz
    · exact absurd hz hres
  have hdd : N.drop δ i = N.drop φ i - N.drop φ' i := by
    simp only [hδdef, drop, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [cur]
  rw [show N.drop φ i = N.drop φ' i by linarith]

/-- Reciprocity: the voltage at `(x, y)` under feed `(s, t)` equals the voltage at `(s, t)`
under feed `(x, y)`. -/
theorem reciprocity {T : Finset E} {s t x y : V} {φ ψ : V → ℝ}
    (hφ : N.IsSolOn T (feed s t) φ) (hψ : N.IsSolOn T (feed x y) ψ) :
    φ x - φ y = ψ s - ψ t := by
  have h1 := N.green T φ ψ
  have h2 := N.green T ψ φ
  have e1 : ∑ v, ψ v * N.divOn T φ v = ψ s - ψ t := by
    rw [← sum_mul_feed ψ s t]; exact Finset.sum_congr rfl fun v _ => by rw [hφ v]
  have e2 : ∑ v, φ v * N.divOn T ψ v = φ x - φ y := by
    rw [← sum_mul_feed φ x y]; exact Finset.sum_congr rfl fun v _ => by rw [hψ v]
  have e3 : ∑ i ∈ T, N.drop ψ i * N.cur φ i = ∑ i ∈ T, N.drop φ i * N.cur ψ i :=
    Finset.sum_congr rfl fun i _ => by simp only [cur]; ring
  linarith

end Net

end TwoPort
