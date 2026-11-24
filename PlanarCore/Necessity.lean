/-
  The condition `0 ≤ I ≤ 1` (`hI01`) is load-bearing in the threshold argument (paper, Section 3).
  Abstract counterexample (`A = [1]` is the reduced incidence of one edge, but `b = [2]` is a
  two-unit feed, not a unit s–t feed; the example isolates the algebra of the assembly step):
  `A = [1]`, `b = [2]`, so `I = Aᵀ (A Aᵀ)⁻¹ b = [2]` violates `I ≤ 1`.  Then network A's
  optimum is `-1/2`, not `-1`, so the gap `1 - f` used there is the wrong gap.
-/
import PlanarCore.Assembly

namespace PlanarCore

open Matrix

/-- `A = [1]`. -/
def exA : Matrix (Fin 1) (Fin 1) ℝ := !![1]
/-- `b = [2]`. -/
def exb : Fin 1 → ℝ := ![2]

theorem ex_current : current exA exb = ![2] := by
  ext i; fin_cases i
  simp [current, exA, exb, Matrix.mulVec, dotProduct, Matrix.vecHead, Matrix.transpose_apply]

theorem ex_not_box : ¬ ∀ i, 0 ≤ current exA exb i ∧ current exA exb i ≤ 1 := by
  intro h; have := (h 0).2; rw [ex_current] at this; norm_num at this

/-- Without `hI01`, the optimum of A is `-1/2`; `optA`'s value `-1` is not attained. -/
theorem ex_optA_fails :
    IsLeast {v | ∃ z f, FeasA exA exb z f ∧ v = -f} (-1/2) ∧
      ¬ IsLeast {v | ∃ z f, FeasA exA exb z f ∧ v = -f} (-1) := by
  have key : ∀ z f, FeasA exA exb z f → f ≤ 1/2 := by
    rintro z f ⟨hA, hz, _⟩
    have h0 := congrFun hA 0
    simp [exA, exb, Matrix.mulVec, dotProduct] at h0
    have := (hz 0).2; linarith
  have feas : FeasA exA exb ![1] (1/2) := by
    refine ⟨?_, ?_, ?_⟩
    · ext i; fin_cases i; simp [exA, exb, Matrix.mulVec, dotProduct]
    · intro i; fin_cases i; simp
    · constructor <;> norm_num
  refine ⟨⟨⟨_, _, feas, by norm_num⟩, ?_⟩, ?_⟩
  · rintro v ⟨z, f, hf, rfl⟩; have := key z f hf; linarith
  · rintro ⟨⟨z, f, hf, hv⟩, _⟩; have := key z f hf; linarith

end PlanarCore
