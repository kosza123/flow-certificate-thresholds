/-
  T1c (assembly) of the threshold argument (paper, Section 3).

  INFORMAL HYPOTHESES (not derived here, taken from the paper, Section 3):
  * Network realisation: network A projects onto `{(z,f) | A z = f b, 0 ≤ z ≤ 1, f ∈ [0,1]}`
    with cost `-f`; network B projects onto `{z | B z = 0, 0 ≤ z ≤ 1}` with cost `z e`.
    (`FeasA`, `FeasB` below are *definitions* of these projections.)
  * H1, H2 of `projection` (connectivity; planar duality + Euler).
  * `hI01 : 0 ≤ I ≤ 1` after reorientation (proved in Graph.lean by a level-set cut argument).
  * `hIe : 0 < I e` (edge `e` carries nonzero current, oriented positively).
  * Kirchhoff: `I e = κ / T` (`hK`).
  * Tolerance contract: additive objective gap, one common `ε` for both networks
    (`AdmissibleNet`).  This is the tolerance contract stated in Section 2 of the paper.
-/
import PlanarCore.Threshold
import PlanarCore.Projection

namespace PlanarCore

open Matrix

variable {m q k : ℕ}

/-- Feasible projections of network A: observed flows `z` and hidden return flow `f`. -/
def FeasA (A : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ) (z : Fin q → ℝ) (f : ℝ) : Prop :=
  A.mulVec z = f • b ∧ (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ f ∈ Set.Icc (0:ℝ) 1

/-- Feasible projections of network B. -/
def FeasB (B : Matrix (Fin k) (Fin q) ℝ) (z : Fin q → ℝ) : Prop :=
  B.mulVec z = 0 ∧ ∀ i, 0 ≤ z i ∧ z i ≤ 1

/-- Shared additive tolerance on the *network* level: one common observation `z`,
returned by A (with some hidden `f`) and by B, each within additive gap `ε` of its own
optimum (`-1` for A, `0` for B; see `optA`, `optB`). -/
def AdmissibleNet (A : Matrix (Fin m) (Fin q) ℝ) (B : Matrix (Fin k) (Fin q) ℝ)
    (b : Fin m → ℝ) (e : Fin q) (ε : ℝ) : Prop :=
  ∃ z f, FeasA A b z f ∧ FeasB B z ∧ (-f) - (-1) ≤ ε ∧ z e - 0 ≤ ε

/-- The optimum of A (minimise `-f`) is `-1`, attained by `(I, 1)`. -/
theorem optA (A : Matrix (Fin m) (Fin q) ℝ) (b : Fin m → ℝ)
    (H1 : IsUnit (A * Aᵀ).det) (hI01 : ∀ i, 0 ≤ current A b i ∧ current A b i ≤ 1) :
    IsLeast {v | ∃ z f, FeasA A b z f ∧ v = -f} (-1) := by
  refine ⟨⟨current A b, 1, ⟨?_, hI01, by norm_num, le_rfl⟩, rfl⟩, ?_⟩
  · unfold current
    rw [one_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ H1, Matrix.one_mulVec]
  · rintro v ⟨z, f, ⟨_, _, _, hf1⟩, rfl⟩; linarith

/-- The optimum of B (minimise `z e`) is `0`, attained by `z = 0`. -/
theorem optB (B : Matrix (Fin k) (Fin q) ℝ) (e : Fin q) :
    IsLeast {v | ∃ z, FeasB B z ∧ v = z e} 0 := by
  refine ⟨⟨0, ⟨Matrix.mulVec_zero B, fun _ => ⟨le_rfl, zero_le_one⟩⟩, rfl⟩, ?_⟩
  rintro v ⟨z, ⟨_, hz⟩, rfl⟩; exact (hz e).1

/-- Under H1, H2 the network-level contract reduces to the scalar one with `c = I e`. -/
theorem admissibleNet_iff (A : Matrix (Fin m) (Fin q) ℝ) (B : Matrix (Fin k) (Fin q) ℝ)
    (b : Fin m → ℝ) (e : Fin q)
    (H1 : IsUnit (A * Aᵀ).det) (H2 : ∀ z, B.mulVec z = 0 ↔ ∃ y, z = Aᵀ.mulVec y)
    (hI01 : ∀ i, 0 ≤ current A b i ∧ current A b i ≤ 1) (ε : ℝ) :
    AdmissibleNet A B b e ε ↔ AdmissibleShared (current A b e) ε := by
  constructor
  · rintro ⟨z, f, ⟨hA, _, hf⟩, ⟨hB, _⟩, h1, h2⟩
    have hz := (projection A B b H1 H2 z f).1 ⟨hA, hB⟩
    refine ⟨f, hf, by linarith, ?_⟩
    rw [hz] at h2; simpa [Pi.smul_apply, smul_eq_mul] using h2
  · rintro ⟨f, hf, h1, h2⟩
    have hproj := (projection A B b H1 H2 (f • current A b) f).2 rfl
    have hbox : ∀ i, 0 ≤ (f • current A b) i ∧ (f • current A b) i ≤ 1 := by
      intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      obtain ⟨h0, h1'⟩ := hI01 i
      exact ⟨mul_nonneg hf.1 h0, by nlinarith [hf.1, hf.2]⟩
    refine ⟨f • current A b, f, ⟨hproj.1, hbox, hf⟩, ⟨hproj.2, hbox⟩, by linarith, ?_⟩
    simpa [Pi.smul_apply, smul_eq_mul] using h2

/-- **T1c (assembly).**  The least shared additive tolerance at which A and B can return
the same observation is `I_e/(1+I_e)`. -/
theorem T1c_threshold (A : Matrix (Fin m) (Fin q) ℝ) (B : Matrix (Fin k) (Fin q) ℝ)
    (b : Fin m → ℝ) (e : Fin q)
    (H1 : IsUnit (A * Aᵀ).det) (H2 : ∀ z, B.mulVec z = 0 ↔ ∃ y, z = Aᵀ.mulVec y)
    (hI01 : ∀ i, 0 ≤ current A b i ∧ current A b i ≤ 1) (hIe : 0 < current A b e) :
    IsLeast {ε | AdmissibleNet A B b e ε} (current A b e / (1 + current A b e)) := by
  have hset : {ε | AdmissibleNet A B b e ε} = {ε | AdmissibleShared (current A b e) ε} := by
    ext ε; exact admissibleNet_iff A B b e H1 H2 hI01 ε
  rw [hset]; exact shared_tolerance_isLeast _ hIe

/-- **T1c (Kirchhoff form).**  With `I_e = κ/T` the threshold is `κ/(T+κ)`. -/
theorem T1c_kirchhoff (A : Matrix (Fin m) (Fin q) ℝ) (B : Matrix (Fin k) (Fin q) ℝ)
    (b : Fin m → ℝ) (e : Fin q)
    (H1 : IsUnit (A * Aᵀ).det) (H2 : ∀ z, B.mulVec z = 0 ↔ ∃ y, z = Aᵀ.mulVec y)
    (hI01 : ∀ i, 0 ≤ current A b i ∧ current A b i ≤ 1)
    (κ T : ℕ) (hκ : 0 < κ) (hT : 0 < T) (hK : current A b e = (κ:ℝ) / T) :
    IsLeast {ε | AdmissibleNet A B b e ε} ((κ:ℝ) / (T + κ)) := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hκpos : (0:ℝ) < κ := by exact_mod_cast hκ
  have hIe : 0 < current A b e := hK ▸ div_pos hκpos hTpos
  rw [← kirchhoff_form _ κ T hT hK]
  exact T1c_threshold A B b e H1 H2 hI01 hIe

/-- "The readouts of the two exact optima are disjoint": at tolerance `0` no common
observation exists when `I e > 0`. -/
theorem exact_optima_disjoint (A : Matrix (Fin m) (Fin q) ℝ) (B : Matrix (Fin k) (Fin q) ℝ)
    (b : Fin m → ℝ) (e : Fin q)
    (H1 : IsUnit (A * Aᵀ).det) (H2 : ∀ z, B.mulVec z = 0 ↔ ∃ y, z = Aᵀ.mulVec y)
    (hI01 : ∀ i, 0 ≤ current A b i ∧ current A b i ≤ 1) (hIe : 0 < current A b e) :
    ¬ AdmissibleNet A B b e 0 := by
  intro h
  have := (T1c_threshold A B b e H1 H2 hI01 hIe).2 h
  have : 0 < current A b e / (1 + current A b e) := by positivity
  linarith

end PlanarCore
