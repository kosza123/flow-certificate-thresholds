/-
  T1b of the threshold argument, paper Section 3 (abstract linear algebra over ℝ).
  H1 (`A Aᵀ` invertible) encodes connectivity of `G`;
  H2 (`ker B = row A`) encodes planar duality + Euler's formula.  Both are hypotheses.
-/
import Mathlib

namespace PlanarCore

open Matrix

/-- The unit-current flow `I = Aᵀ (A Aᵀ)⁻¹ b`. -/
noncomputable def current {m q : ℕ} (A : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) :
    Fin q → ℝ :=
  Aᵀ.mulVec ((A * Aᵀ)⁻¹.mulVec b)

/-- **T1b.** -/
theorem projection {m q k : ℕ} (A : Matrix (Fin m) (Fin q) ℝ)
    (B : Matrix (Fin k) (Fin q) ℝ) (b : Fin m → ℝ)
    (H1 : IsUnit (A * Aᵀ).det)
    (H2 : ∀ z, B.mulVec z = 0 ↔ ∃ y, z = Aᵀ.mulVec y)
    (z : Fin q → ℝ) (f : ℝ) :
    (A.mulVec z = f • b ∧ B.mulVec z = 0) ↔ z = f • current A b := by
  unfold current
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨y, rfl⟩ := (H2 z).1 hB
    have hy : (A * Aᵀ).mulVec y = f • b := by
      rw [← Matrix.mulVec_mulVec]; exact hA
    have hy' : y = f • (A * Aᵀ)⁻¹.mulVec b := by
      calc y = ((A * Aᵀ)⁻¹ * (A * Aᵀ)).mulVec y := by
              rw [Matrix.nonsing_inv_mul _ H1, Matrix.one_mulVec]
        _ = (A * Aᵀ)⁻¹.mulVec (f • b) := by rw [← Matrix.mulVec_mulVec, hy]
        _ = f • (A * Aᵀ)⁻¹.mulVec b := Matrix.mulVec_smul _ _ _
    rw [hy', Matrix.mulVec_smul]
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ H1, Matrix.one_mulVec]
    · rw [← Matrix.mulVec_smul]
      exact (H2 _).2 ⟨_, rfl⟩

end PlanarCore
