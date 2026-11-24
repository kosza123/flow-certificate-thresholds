/-
  T1a (threshold of two linear gaps) and the arithmetic part of T1c,
  of the threshold argument (paper, Section 3).
-/
import Mathlib

namespace PlanarCore

/-- T1a, lower bound: for `c > 0`, every `f ∈ [0,1]` has `max (1-f) (f*c) ≥ c/(1+c)`.
(The constraint `f ∈ [0,1]` is not even needed.) -/
theorem threshold_lower (c : ℝ) (hc : 0 < c) (f : ℝ) :
    c / (1 + c) ≤ max (1 - f) (f * c) := by
  have hpos : (0:ℝ) < 1 + c := by linarith
  have e1 : c / (1 + c) = 1 - 1 / (1 + c) := by field_simp; ring
  have e2 : c / (1 + c) = 1 / (1 + c) * c := by field_simp
  rcases le_total f (1 / (1 + c)) with h | h
  · exact le_max_of_le_left (by linarith)
  · refine le_max_of_le_right ?_
    rw [e2]; exact mul_le_mul_of_nonneg_right h hc.le

/-- T1a, attainment at `f₀ = 1/(1+c)`. -/
theorem threshold_attained (c : ℝ) (hc : 0 < c) :
    max (1 - 1 / (1 + c)) (1 / (1 + c) * c) = c / (1 + c) := by
  have hpos : (1:ℝ) + c ≠ 0 := by positivity
  have h1 : 1 - 1 / (1 + c) = c / (1 + c) := by field_simp; ring
  have h2 : 1 / (1 + c) * c = c / (1 + c) := by field_simp
  rw [h1, h2, max_self]

/-- `f₀ = 1/(1+c)` lies in `[0,1]`. -/
theorem f0_mem (c : ℝ) (hc : 0 < c) : 1 / (1 + c) ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by linarith)]; linarith

/-- T1a, uniqueness of the minimiser. -/
theorem threshold_unique (c : ℝ) (hc : 0 < c) (f : ℝ)
    (h : max (1 - f) (f * c) = c / (1 + c)) : f = 1 / (1 + c) := by
  have hpos : (0:ℝ) < 1 + c := by linarith
  have e1 : c / (1 + c) = 1 - 1 / (1 + c) := by field_simp; ring
  have e2 : c / (1 + c) = 1 / (1 + c) * c := by field_simp
  have ha : 1 - f ≤ c / (1 + c) := h ▸ le_max_left _ _
  have hb : f * c ≤ c / (1 + c) := h ▸ le_max_right _ _
  have hf1 : 1 / (1 + c) ≤ f := by linarith
  have hf2 : f ≤ 1 / (1 + c) := by
    rw [e2] at hb; exact le_of_mul_le_mul_right hb hc
  exact le_antisymm hf2 hf1

/-- **T1a**: the lower bound on `[0,1]` and equality at `f₀`. -/
theorem T1a (c : ℝ) (hc : 0 < c) :
    (∀ f ∈ Set.Icc (0:ℝ) 1, c / (1 + c) ≤ max (1 - f) (f * c)) ∧
      max (1 - 1 / (1 + c)) (1 / (1 + c) * c) = c / (1 + c) :=
  ⟨fun f _ => threshold_lower c hc f, threshold_attained c hc⟩

/-- The threshold as an `IsLeast` statement over `f ∈ [0,1]`. -/
theorem threshold_isLeast (c : ℝ) (hc : 0 < c) :
    IsLeast ((fun f => max (1 - f) (f * c)) '' Set.Icc (0:ℝ) 1) (c / (1 + c)) := by
  refine ⟨⟨1 / (1 + c), f0_mem c hc, threshold_attained c hc⟩, ?_⟩
  rintro _ ⟨f, _, rfl⟩; exact threshold_lower c hc f

/-- **Shared additive tolerance contract, made explicit.**  A tolerance `ε` is admissible
when one common parameter `f ∈ [0,1]` makes *both* additive gaps `1 - f` (network A) and
`f * c` (network B) at most the *same* `ε`.  The least admissible `ε` is `c/(1+c)`. -/
def AdmissibleShared (c ε : ℝ) : Prop :=
  ∃ f ∈ Set.Icc (0:ℝ) 1, 1 - f ≤ ε ∧ f * c ≤ ε

theorem shared_tolerance_isLeast (c : ℝ) (hc : 0 < c) :
    IsLeast {ε | AdmissibleShared c ε} (c / (1 + c)) := by
  refine ⟨⟨1 / (1 + c), f0_mem c hc, ?_, ?_⟩, ?_⟩
  · have := le_max_left (1 - 1 / (1 + c)) (1 / (1 + c) * c)
    rwa [threshold_attained c hc] at this
  · have := le_max_right (1 - 1 / (1 + c)) (1 / (1 + c) * c)
    rwa [threshold_attained c hc] at this
  · rintro ε ⟨f, _, h1, h2⟩
    exact (threshold_lower c hc f).trans (max_le h1 h2)

/-- With *separate* tolerances `εA, εB` the contract is the region `εA + εB / c ≥ 1`
(for `εA ≤ 1`); the single number `c/(1+c)` exists only because the tolerance is shared. -/
theorem separate_tolerance_iff (c εA εB : ℝ) (hc : 0 < c) (hA : εA ≤ 1) (hA0 : 0 ≤ εA)
    (_hB0 : 0 ≤ εB) :
    (∃ f ∈ Set.Icc (0:ℝ) 1, 1 - f ≤ εA ∧ f * c ≤ εB) ↔ (1 - εA) * c ≤ εB := by
  constructor
  · rintro ⟨f, _, h1, h2⟩
    have : (1 - εA) * c ≤ f * c := mul_le_mul_of_nonneg_right (by linarith) hc.le
    linarith
  · intro h
    exact ⟨1 - εA, ⟨by linarith, by linarith⟩, by linarith, h⟩

/-- T1c, arithmetic: under the Kirchhoff hypothesis `I_e = κ/T` the threshold
`I_e/(1+I_e)` equals `κ/(T+κ)`. -/
theorem kirchhoff_form (Ie : ℝ) (κ T : ℕ) (hT : 0 < T) (hK : Ie = (κ:ℝ) / T) :
    Ie / (1 + Ie) = (κ:ℝ) / (T + κ) := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hκ0 : (0:ℝ) ≤ κ := by exact_mod_cast Nat.zero_le κ
  have : (T:ℝ) + κ ≠ 0 := by positivity
  rw [hK]; field_simp

/-- T1c: least admissible shared tolerance, in Kirchhoff form. -/
theorem threshold_kirchhoff (Ie : ℝ) (κ T : ℕ) (hκ : 0 < κ) (hT : 0 < T)
    (hK : Ie = (κ:ℝ) / T) :
    IsLeast {ε | AdmissibleShared Ie ε} ((κ:ℝ) / (T + κ)) := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hκpos : (0:ℝ) < κ := by exact_mod_cast hκ
  have hIe : 0 < Ie := hK ▸ div_pos hκpos hTpos
  rw [← kirchhoff_form Ie κ T hT hK]; exact shared_tolerance_isLeast Ie hIe

/-- "The least positive threshold over choices of `s,t,e` is `Θ(G) = μ/(1+μ)`":
`x ↦ x/(1+x)` is strictly monotone on `x ≥ 0`, so minimising thresholds is the same
as minimising `|I_e|`. -/
theorem threshold_strictMonoOn : StrictMonoOn (fun x : ℝ => x / (1 + x)) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Lower bound used with Kirchhoff: an integer numerator `κ ≥ 1` gives `1/I_e ≤ T`. -/
theorem inv_current_le_trees (Ie : ℝ) (κ T : ℕ) (hκ : 1 ≤ κ) (hT : 0 < T)
    (hK : Ie = (κ:ℝ) / T) : 1 / Ie ≤ T := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have hκ1 : (1:ℝ) ≤ κ := by exact_mod_cast hκ
  rw [hK, one_div_div, div_le_iff₀ (by linarith)]
  nlinarith

end PlanarCore
