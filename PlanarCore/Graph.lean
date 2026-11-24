/-
  H1 and `0 ≤ I ≤ 1` proved from a concrete graph model.

  Model: finite multigraph, vertices `Fin (n+1)` (vertex `0` is the reference vertex),
  edges `Fin q` with endpoints `src i`, `tgt i`.  Loops and parallel edges are allowed
  (a loop has a zero incidence column).  Unit resistances.
  Connectivity is the real graph property `∀ u v, ReflTransGen Adj u v`.
-/
import PlanarCore.Assembly

namespace PlanarCore

open Matrix

/-- A finite multigraph with vertices `Fin (n+1)` and edges `Fin q`. -/
structure MGraph (n q : ℕ) where
  src : Fin q → Fin (n+1)
  tgt : Fin q → Fin (n+1)

namespace MGraph

variable {n q : ℕ} (G : MGraph n q)

/-- Undirected adjacency through some edge. -/
def Adj (u v : Fin (n+1)) : Prop :=
  ∃ i, (G.src i = u ∧ G.tgt i = v) ∨ (G.src i = v ∧ G.tgt i = u)

/-- Connectivity: every two vertices are joined by a walk. -/
def Connected : Prop := ∀ u v, Relation.ReflTransGen G.Adj u v

/-- Full signed incidence: `+1` at the start of the edge, `-1` at its end (`0` for a loop). -/
def inc (v : Fin (n+1)) (i : Fin q) : ℝ :=
  (if G.src i = v then 1 else 0) - (if G.tgt i = v then 1 else 0)

/-- Reduced incidence matrix: the row of the reference vertex `0` is deleted. -/
def redInc : Matrix (Fin n) (Fin q) ℝ := fun j i => G.inc j.succ i

/-- Potential extended by `0` at the reference vertex. -/
def ext (x : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.cons (0:ℝ) x

@[simp] theorem ext_zero (x : Fin n → ℝ) : ext x 0 = 0 := rfl
@[simp] theorem ext_succ (x : Fin n → ℝ) (j : Fin n) : ext x j.succ = x j := rfl

theorem sum_inc_mul (i : Fin q) (e : Fin (n+1) → ℝ) :
    ∑ v, G.inc v i * e v = e (G.src i) - e (G.tgt i) := by
  simp [inc, sub_mul, ite_mul, Finset.sum_sub_distrib]

/-- `Aᵀ x` is the potential drop along each edge. -/
theorem redInc_transpose_mulVec (x : Fin n → ℝ) (i : Fin q) :
    (G.redIncᵀ *ᵥ x) i = ext x (G.src i) - ext x (G.tgt i) := by
  rw [← G.sum_inc_mul i (ext x), Fin.sum_univ_succ]
  simp [Matrix.mulVec, dotProduct, redInc, Matrix.transpose_apply]

/-- Net outflow of an edge flow `z` at vertex `v`. -/
def div (z : Fin q → ℝ) (v : Fin (n+1)) : ℝ := ∑ i, G.inc v i * z i

theorem redInc_mulVec (z : Fin q → ℝ) (j : Fin n) : (G.redInc *ᵥ z) j = G.div z j.succ := by
  simp [Matrix.mulVec, dotProduct, redInc, div]

theorem sum_div (z : Fin q → ℝ) : ∑ v, G.div z v = 0 := by
  unfold div
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := G.sum_inc_mul i (fun _ => z i)
  simp only [sub_self] at this
  exact this

/-- A potential with equal values at both ends of every edge is constant on a
connected graph. -/
theorem const_of_edges (hG : G.Connected) (φ : Fin (n+1) → ℝ)
    (h : ∀ i, φ (G.src i) = φ (G.tgt i)) (v : Fin (n+1)) : φ v = φ 0 := by
  induction hG 0 v with
  | refl => rfl
  | tail _ hadj ih =>
    obtain ⟨i, ⟨hs, ht⟩ | ⟨hs, ht⟩⟩ := hadj
    · rw [← ht, ← h i, hs, ih]
    · rw [← hs, h i, ht, ih]

/-- **H1.**  For a connected multigraph the reduced Laplacian `A Aᵀ` is
invertible. -/
theorem H1_of_connected (hG : G.Connected) : IsUnit (G.redInc * G.redIncᵀ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hx0
  set y := G.redIncᵀ *ᵥ x with hy
  have hyy : y ⬝ᵥ y = 0 := by
    have h0 : x ⬝ᵥ ((G.redInc * G.redIncᵀ) *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
    rwa [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at h0
  have hy0 : y = 0 := dotProduct_self_eq_zero.1 hyy
  have hedge : ∀ i, ext x (G.src i) = ext x (G.tgt i) := by
    intro i
    have := congrFun hy0 i
    rw [hy, G.redInc_transpose_mulVec] at this
    simpa [sub_eq_zero] using this
  funext j
  have := G.const_of_edges hG (ext x) hedge j.succ
  simpa using this

/-- Full source vector `e_s - e_t`. -/
def bvec (s t : Fin (n+1)) (v : Fin (n+1)) : ℝ :=
  (if v = s then 1 else 0) - (if v = t then 1 else 0)

/-- Reduced source vector (reference row deleted). -/
def redB (s t : Fin (n+1)) : Fin n → ℝ := fun j => bvec s t j.succ

/-- Potentials of the unit feed from `s` to `t`, grounded at the reference vertex. -/
noncomputable def pot (s t : Fin (n+1)) : Fin (n+1) → ℝ :=
  ext ((G.redInc * G.redIncᵀ)⁻¹ *ᵥ redB s t)

/-- Ohm's law: the current on an edge is the potential drop. -/
theorem current_eq_drop (s t : Fin (n+1)) (i : Fin q) :
    current G.redInc (redB s t) i = G.pot s t (G.src i) - G.pot s t (G.tgt i) := by
  unfold current pot
  exact G.redInc_transpose_mulVec _ i

/-- Kirchhoff's current law at *every* vertex, including the reference vertex. -/
theorem kcl (hG : G.Connected) (s t : Fin (n+1)) (v : Fin (n+1)) :
    G.div (current G.redInc (redB s t)) v = bvec s t v := by
  have hA : G.redInc *ᵥ current G.redInc (redB s t) = redB s t := by
    unfold current
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (G.H1_of_connected hG),
      Matrix.one_mulVec]
  have hsucc : ∀ j : Fin n, G.div (current G.redInc (redB s t)) j.succ = bvec s t j.succ := by
    intro j
    rw [← G.redInc_mulVec, hA]; rfl
  have hb : ∑ w, bvec s t w = 0 := by simp [bvec, Finset.sum_sub_distrib]
  have hd := G.sum_div (current G.redInc (redB s t))
  rw [Fin.sum_univ_succ] at hb hd
  simp only [hsucc] at hd
  refine Fin.cases ?_ (fun j => hsucc j) v
  linarith

/-- Level-set cut identity: for `χ` the indicator of `{w | c ≤ pot w}`. -/
theorem cut_identity (z : Fin q → ℝ) (χ : Fin (n+1) → ℝ) :
    ∑ v, χ v * G.div z v = ∑ i, z i * (χ (G.src i) - χ (G.tgt i)) := by
  unfold div
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← G.sum_inc_mul i χ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- **Current bound.**  On a connected multigraph, every edge current of the
unit feed from `s` to `t` has modulus at most one.  Bridges, loops and zero-current edges
need no separate treatment. -/
theorem current_abs_le_one (hG : G.Connected) (s t : Fin (n+1)) (i0 : Fin q) :
    |current G.redInc (redB s t) i0| ≤ 1 := by
  set I := current G.redInc (redB s t) with hIdef
  set φ := G.pot s t with hφ
  have hdrop : ∀ i, I i = φ (G.src i) - φ (G.tgt i) := fun i => G.current_eq_drop s t i
  -- for any level `c`, the cut term of each edge is nonnegative and their sum is ≤ 1
  have key : ∀ c : ℝ, I i0 * ((if c ≤ φ (G.src i0) then 1 else 0) -
      (if c ≤ φ (G.tgt i0) then 1 else 0)) ≤ 1 := by
    intro c
    set χ : Fin (n+1) → ℝ := fun w => if c ≤ φ w then 1 else 0 with hχ
    have hterm : ∀ i, 0 ≤ I i * (χ (G.src i) - χ (G.tgt i)) := by
      intro i
      rw [hdrop i]
      simp only [hχ]
      split_ifs with h1 h2 h2 <;> nlinarith
    have hsum : ∑ i, I i * (χ (G.src i) - χ (G.tgt i)) = χ s - χ t := by
      rw [← G.cut_identity I χ]
      have hk : ∀ v, G.div I v = bvec s t v := fun v => G.kcl hG s t v
      simp_rw [hk]
      simp [bvec, mul_sub, Finset.sum_sub_distrib]
    have hle : χ s - χ t ≤ 1 := by simp only [hχ]; split_ifs <;> norm_num
    have := Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ i0)
    linarith
  rcases lt_trichotomy (I i0) 0 with hneg | hzero | hpos
  · have hlt : φ (G.src i0) < φ (G.tgt i0) := by linarith [hdrop i0]
    have := key (φ (G.tgt i0))
    simp only [show ¬ (φ (G.tgt i0) ≤ φ (G.src i0)) from not_le.2 hlt, le_refl,
      ↓reduceIte] at this
    rw [abs_of_neg hneg]; linarith
  · rw [hzero, abs_zero]; exact zero_le_one
  · have hlt : φ (G.tgt i0) < φ (G.src i0) := by linarith [hdrop i0]
    have := key (φ (G.src i0))
    simp only [show ¬ (φ (G.src i0) ≤ φ (G.tgt i0)) from not_le.2 hlt, le_refl,
      ↓reduceIte] at this
    rw [abs_of_pos hpos]; linarith

/-- Reorientation of the edges selected by `flip`. -/
def reorient (flip : Fin q → Prop) [DecidablePred flip] : MGraph n q where
  src i := if flip i then G.tgt i else G.src i
  tgt i := if flip i then G.src i else G.tgt i

/-- Reversing edges multiplies their incidence columns by `-1`. -/
theorem reorient_redInc (flip : Fin q → Prop) [DecidablePred flip] :
    (G.reorient flip).redInc = G.redInc * diagonal (fun i => if flip i then (-1:ℝ) else 1) := by
  ext j i
  simp only [redInc, Matrix.mul_diagonal, inc, reorient]
  split_ifs <;> simp_all

end MGraph

/-! ### Matrix-level reorientation `A ↦ A D`, `B ↦ B D` with `D = diag(±1)` -/

section Reorient

variable {m q k : ℕ}

theorem diag_sq (σ : Fin q → ℝ) (hσ : ∀ i, σ i * σ i = 1) :
    diagonal σ * diagonal σ = 1 := by
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [hσ]
  · simp [h, Matrix.one_apply_ne h]

theorem reorient_gram (A : Matrix (Fin m) (Fin q) ℝ) (σ : Fin q → ℝ) (hσ : ∀ i, σ i * σ i = 1) :
    (A * diagonal σ) * (A * diagonal σ)ᵀ = A * Aᵀ := by
  rw [Matrix.transpose_mul, diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal σ),
    diag_sq σ hσ, Matrix.one_mul]

theorem reorient_current (A : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (σ : Fin q → ℝ)
    (hσ : ∀ i, σ i * σ i = 1) (i : Fin q) :
    current (A * diagonal σ) b i = σ i * current A b i := by
  unfold current
  rw [reorient_gram A σ hσ, Matrix.transpose_mul, diagonal_transpose, ← Matrix.mulVec_mulVec,
    mulVec_diagonal]

theorem reorient_H2 (A : Matrix (Fin m) (Fin q) ℝ) (B : Matrix (Fin k) (Fin q) ℝ)
    (σ : Fin q → ℝ) (hσ : ∀ i, σ i * σ i = 1)
    (H2 : ∀ z, B.mulVec z = 0 ↔ ∃ y, z = Aᵀ.mulVec y) :
    ∀ z, (B * diagonal σ).mulVec z = 0 ↔ ∃ y, z = (A * diagonal σ)ᵀ.mulVec y := by
  intro z
  have hDD : ∀ w, diagonal σ *ᵥ (diagonal σ *ᵥ w) = w := by
    intro w; rw [Matrix.mulVec_mulVec, diag_sq σ hσ, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, H2, Matrix.transpose_mul, diagonal_transpose]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← hy, hDD]
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← Matrix.mulVec_mulVec, hDD]⟩

end Reorient

end PlanarCore
