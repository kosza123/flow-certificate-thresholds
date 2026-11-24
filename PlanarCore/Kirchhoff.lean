/-
  Kirchhoff, part (a) only.  Cramer's rule gives `I_e = N / D` with
  `D = det (A Aᵀ) ∈ ℤ`, `D > 0`, and an integer numerator `N`.
  NOT done: the identification of `D` with the number of spanning trees and of `N` with a
  signed spanning-tree count (matrix-tree theorem).
-/
import PlanarCore.Graph

namespace PlanarCore

open Matrix

namespace MGraph

variable {n q : ℕ} (G : MGraph n q)

/-- Integer signed incidence. -/
def incZ (v : Fin (n+1)) (i : Fin q) : ℤ :=
  (if G.src i = v then 1 else 0) - (if G.tgt i = v then 1 else 0)

/-- Integer reduced incidence matrix. -/
def redIncZ : Matrix (Fin n) (Fin q) ℤ := fun j i => G.incZ j.succ i

/-- Integer reduced source vector. -/
def redBZ (s t : Fin (n+1)) : Fin n → ℤ :=
  fun j => (if j.succ = s then 1 else 0) - (if j.succ = t then 1 else 0)

/-- `D = det (A Aᵀ)` over `ℤ`. -/
def detL : ℤ := (G.redIncZ * G.redIncZᵀ).det

/-- Integer Cramer numerator `N = (Aᵀ adj(A Aᵀ) b)_e`. -/
def numer (s t : Fin (n+1)) (e : Fin q) : ℤ :=
  (G.redIncZᵀ *ᵥ ((G.redIncZ * G.redIncZᵀ).adjugate *ᵥ redBZ s t)) e

theorem redInc_eq_map : G.redInc = G.redIncZ.map (Int.castRingHom ℝ) := by
  ext j i
  simp only [redInc, inc, redIncZ, incZ, Matrix.map_apply, eq_intCast]
  split_ifs <;> norm_num

theorem redB_eq_map (s t : Fin (n+1)) : redB s t = (Int.castRingHom ℝ) ∘ redBZ s t := by
  funext j
  simp only [redB, bvec, redBZ, Function.comp_apply, eq_intCast]
  split_ifs <;> norm_num

theorem gram_eq_map :
    G.redInc * G.redIncᵀ = (G.redIncZ * G.redIncZᵀ).map (Int.castRingHom ℝ) := by
  rw [G.redInc_eq_map, Matrix.map_mul, Matrix.transpose_map]

theorem detL_cast : ((G.detL : ℤ) : ℝ) = (G.redInc * G.redIncᵀ).det := by
  rw [gram_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl

/-- `D > 0` for a connected graph (Gram determinant of full rank). -/
theorem detL_pos (hG : G.Connected) : 0 < G.detL := by
  have hpsd : (G.redInc * G.redIncᵀ).PosSemidef := by
    have := Matrix.posSemidef_self_mul_conjTranspose G.redInc
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdet : (G.redInc * G.redIncᵀ).det ≠ 0 := (G.H1_of_connected hG).ne_zero
  have hpd := hpsd.posDef_iff_det_ne_zero.2 hdet
  have : (0:ℝ) < G.detL := by rw [detL_cast]; exact hpd.det_pos
  exact_mod_cast this

/-- **Cramer form of the current:** `I_e = N / D`. -/
theorem current_eq_numer_div (hG : G.Connected) (s t : Fin (n+1)) (e : Fin q) :
    current G.redInc (redB s t) e = (G.numer s t e : ℝ) / (G.detL : ℝ) := by
  have hD : (G.detL : ℝ) ≠ 0 := by exact_mod_cast (G.detL_pos hG).ne'
  set f := Int.castRingHom ℝ
  have hadj : (G.redInc * G.redIncᵀ).adjugate = (G.redIncZ * G.redIncZᵀ).adjugate.map f := by
    rw [gram_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]; rfl
  have hinv : (G.redInc * G.redIncᵀ)⁻¹ = (G.detL : ℝ)⁻¹ • (G.redInc * G.redIncᵀ).adjugate := by
    rw [Matrix.inv_def, ← detL_cast, Ring.inverse_eq_inv']
  unfold current numer
  rw [hinv, Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hadj,
    redB_eq_map, G.redInc_eq_map, ← Matrix.transpose_map]
  have h1 := RingHom.map_mulVec f (G.redIncZ * G.redIncZᵀ).adjugate (redBZ s t)
  have h2 := RingHom.map_mulVec f G.redIncZᵀ ((G.redIncZ * G.redIncZᵀ).adjugate *ᵥ redBZ s t) e
  have h3 : (fun j => f (((G.redIncZ * G.redIncZᵀ).adjugate *ᵥ redBZ s t) j)) =
      ((G.redIncZ * G.redIncZᵀ).adjugate.map f *ᵥ (f ∘ redBZ s t)) := funext h1
  rw [← h3]
  change _ = f _ / _
  rw [h2, div_eq_inv_mul]
  rfl

/-- The threshold in Cramer form: `|I_e|/(1+|I_e|) = |N|/(D+|N|)`. -/
theorem threshold_cramer (hG : G.Connected) (s t : Fin (n+1)) (e : Fin q) :
    |current G.redInc (redB s t) e| / (1 + |current G.redInc (redB s t) e|) =
      (|G.numer s t e| : ℝ) / ((G.detL : ℝ) + |G.numer s t e|) := by
  have hD : (0:ℝ) < G.detL := by exact_mod_cast G.detL_pos hG
  rw [G.current_eq_numer_div hG, abs_div, abs_of_pos hD]
  have : (G.detL : ℝ) + |(G.numer s t e : ℝ)| ≠ 0 := by positivity
  field_simp
  push_cast
  ring

end MGraph

end PlanarCore
