/-
  The substitution lemma.

  `X.subst e Y s t` is the network `X` with its edge `e` replaced by the network `Y`, whose
  ports `s, t` are glued to the two ends of `e`.  If the resistance of `e` in `X` equals the
  port resistance of `Y`, then the outer network cannot tell `Y` from a single resistor:
  outer currents are unchanged, and every current inside `Y` is the branch current through `e`
  times the corresponding current of `Y` under unit feed (`subst_isSol`).
-/
import TwoPort.Basic

open Finset

set_option linter.unusedSectionVars false

namespace TwoPort

variable {V E W F : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Fintype W] [Fintype F] [DecidableEq W]

namespace Net

/-- Attaching map of the inner network: the ports go to the ends of `e`, every other vertex
stays a new vertex. -/
def att (X : Net V E) (e : E) (s t : W) (w : W) : V ⊕ {w : W // w ≠ s ∧ w ≠ t} :=
  if hs : w = s then Sum.inl (X.src e)
  else if ht : w = t then Sum.inl (X.tgt e) else Sum.inr ⟨w, hs, ht⟩

/-- `X` with the edge `e` replaced by `Y`, the ports `s, t` of `Y` glued to the ends of `e`. -/
def subst (X : Net V E) (e : E) (Y : Net W F) (s t : W) :
    Net (V ⊕ {w : W // w ≠ s ∧ w ≠ t}) ({i : E // i ≠ e} ⊕ F) where
  src := Sum.elim (fun i => Sum.inl (X.src i)) (fun j => att X e s t (Y.src j))
  tgt := Sum.elim (fun i => Sum.inl (X.tgt i)) (fun j => att X e s t (Y.tgt j))
  res := Sum.elim (fun i => X.res i) Y.res

/-- The potential on the glued network: `φ` outside, a scaled and shifted copy of `ψ` inside. -/
noncomputable def glue (X : Net V E) (e : E) (s t : W) (φ : V → ℝ) (ψ : W → ℝ) :
    V ⊕ {w : W // w ≠ s ∧ w ≠ t} → ℝ :=
  Sum.elim φ (fun w => φ (X.tgt e) + X.cur φ e * (ψ w - ψ t))

variable (X : Net V E) (e : E) (Y : Net W F) {s t : W}

theorem att_ind_inl (hst : s ≠ t) (w : W) (v : V) :
    (if att X e s t w = Sum.inl v then (1:ℝ) else 0) =
      (if w = s then 1 else 0) * (if X.src e = v then 1 else 0) +
      (if w = t then 1 else 0) * (if X.tgt e = v then 1 else 0) := by
  unfold att
  by_cases hs : w = s
  · subst hs
    simp [hst]
  · by_cases ht : w = t
    · subst ht
      simp [hs]
    · simp [hs, ht]

theorem att_eq_inr_iff (w : W) (w0 : {w : W // w ≠ s ∧ w ≠ t}) :
    att X e s t w = Sum.inr w0 ↔ w = w0.1 := by
  unfold att
  by_cases hs : w = s
  · rw [dite_eq_left_of_eq_true (eq_true hs)]
    constructor
    · intro h; cases h
    · intro h; exact absurd (h.symm.trans hs) w0.2.1
  · rw [dite_eq_right_of_eq_false (eq_false hs)]
    by_cases ht : w = t
    · rw [dite_eq_left_of_eq_true (eq_true ht)]
      constructor
      · intro h; cases h
      · intro h; exact absurd (h.symm.trans ht) w0.2.2
    · rw [dite_eq_right_of_eq_false (eq_false ht)]
      constructor
      · intro h; exact congrArg Subtype.val (Sum.inr.inj h)
      · intro h; exact congrArg Sum.inr (Subtype.ext h)

theorem att_ind_inr (w : W) (w0 : {w : W // w ≠ s ∧ w ≠ t}) :
    (if att X e s t w = Sum.inr w0 then (1:ℝ) else 0) = (if w = w0.1 then 1 else 0) := by
  by_cases h : w = w0.1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h),
      ite_eq_left_of_eq_true _ _ (eq_true ((att_eq_inr_iff X e w w0).2 h))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' => h ((att_eq_inr_iff X e w w0).1 h'))]

/-- The glued potential read through the attaching map. -/
theorem glue_att {φ : V → ℝ} {ψ : W → ℝ} (hR : X.res e = ψ s - ψ t) (hres : X.res e ≠ 0)
    (w : W) :
    glue X e s t φ ψ (att X e s t w) = φ (X.tgt e) + X.cur φ e * (ψ w - ψ t) := by
  unfold att glue
  by_cases hs : w = s
  · subst hs
    simp only [↓reduceDIte, Sum.elim_inl]
    rw [← hR]
    simp only [cur, drop]
    field_simp
    ring
  · by_cases ht : w = t
    · subst ht
      simp [hs]
    · simp [hs, ht]

theorem inc_inl_inl (v : V) (i : {i : E // i ≠ e}) :
    (X.subst e Y s t).inc (Sum.inl v) (Sum.inl i) = X.inc v i := by
  simp [inc, subst]

theorem inc_inr_inl (w0 : {w : W // w ≠ s ∧ w ≠ t}) (i : {i : E // i ≠ e}) :
    (X.subst e Y s t).inc (Sum.inr w0) (Sum.inl i) = 0 := by
  simp [inc, subst]

theorem inc_inl_inr (hst : s ≠ t) (v : V) (j : F) :
    (X.subst e Y s t).inc (Sum.inl v) (Sum.inr j) =
      (if X.src e = v then 1 else 0) * Y.inc s j + (if X.tgt e = v then 1 else 0) * Y.inc t j := by
  show (if att X e s t (Y.src j) = Sum.inl v then (1:ℝ) else 0)
      - (if att X e s t (Y.tgt j) = Sum.inl v then (1:ℝ) else 0) = _
  rw [att_ind_inl X e hst, att_ind_inl X e hst]
  simp only [inc]
  ring

theorem inc_inr_inr (w0 : {w : W // w ≠ s ∧ w ≠ t}) (j : F) :
    (X.subst e Y s t).inc (Sum.inr w0) (Sum.inr j) = Y.inc w0.1 j := by
  show (if att X e s t (Y.src j) = Sum.inr w0 then (1:ℝ) else 0)
      - (if att X e s t (Y.tgt j) = Sum.inr w0 then (1:ℝ) else 0) = _
  rw [att_ind_inr X e, att_ind_inr X e]
  rfl

/-- **Substitution lemma.**  Let `φ` solve `X` with feed `b`, let `ψ` solve `Y` with unit feed
at its ports, and let the resistance of `e` in `X` be the port resistance `ψ s - ψ t` of `Y`.
Then the glued potential solves `X` with `e` replaced by `Y`, under the same outer feed.
Outer currents are unchanged; the current in an edge `j` of `Y` is the branch current through
`e` times the unit-feed current of `j`. -/
theorem subst_isSol (hst : s ≠ t) {b φ : V → ℝ} {ψ : W → ℝ} (hφ : X.IsSol b φ)
    (hψ : Y.IsSol (feed s t) ψ) (hR : X.res e = ψ s - ψ t) (hres : X.res e ≠ 0) :
    (X.subst e Y s t).IsSol (Sum.elim b fun _ => 0) (glue X e s t φ ψ) ∧
    (∀ i : {i : E // i ≠ e},
      (X.subst e Y s t).cur (glue X e s t φ ψ) (Sum.inl i) = X.cur φ i) ∧
    (∀ j : F,
      (X.subst e Y s t).cur (glue X e s t φ ψ) (Sum.inr j) = X.cur φ e * Y.cur ψ j) := by
  have hcurL : ∀ i : {i : E // i ≠ e},
      (X.subst e Y s t).cur (glue X e s t φ ψ) (Sum.inl i) = X.cur φ i := by
    intro i
    simp [cur, drop, subst, glue]
  have hcurR : ∀ j : F,
      (X.subst e Y s t).cur (glue X e s t φ ψ) (Sum.inr j) = X.cur φ e * Y.cur ψ j := by
    intro j
    show (glue X e s t φ ψ (att X e s t (Y.src j)) - glue X e s t φ ψ (att X e s t (Y.tgt j)))
        / Y.res j = X.cur φ e * ((ψ (Y.src j) - ψ (Y.tgt j)) / Y.res j)
    rw [glue_att X e hR hres, glue_att X e hR hres]
    ring
  refine ⟨?_, hcurL, hcurR⟩
  intro v'
  show (X.subst e Y s t).divOn univ (glue X e s t φ ψ) v' = _
  rw [divOn, Fintype.sum_sum_type]
  simp only [hcurL, hcurR]
  have hfs : feed s t s = 1 := by simp [feed, hst]
  have hft : feed s t t = -1 := by simp [feed, hst.symm]
  cases v' with
  | inl v =>
    have h1 : ∑ i : {i : E // i ≠ e}, (X.subst e Y s t).inc (Sum.inl v) (Sum.inl i) * X.cur φ i
        = b v - X.inc v e * X.cur φ e := by
      simp only [inc_inl_inl]
      rw [← hφ v, divOn,
        ← Finset.sum_subtype (univ.erase e) (by simp) (fun i => X.inc v i * X.cur φ i),
        Finset.sum_erase_eq_sub (Finset.mem_univ e)]
    have h2 : ∑ j : F, (X.subst e Y s t).inc (Sum.inl v) (Sum.inr j) * (X.cur φ e * Y.cur ψ j)
        = X.cur φ e * X.inc v e := by
      have hs := hψ s
      have ht := hψ t
      simp only [divOn] at hs ht
      have hterm : ∀ j : F, (X.subst e Y s t).inc (Sum.inl v) (Sum.inr j) *
          (X.cur φ e * Y.cur ψ j) =
          X.cur φ e * (if X.src e = v then 1 else 0) * (Y.inc s j * Y.cur ψ j) +
          X.cur φ e * (if X.tgt e = v then 1 else 0) * (Y.inc t j * Y.cur ψ j) := by
        intro j; rw [inc_inl_inr X e Y hst]; ring
      simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hs, ht, hfs, hft]
      simp only [inc]
      ring
    rw [h1, h2]
    simp only [Sum.elim_inl]
    ring
  | inr w0 =>
    have h1 : ∑ i : {i : E // i ≠ e}, (X.subst e Y s t).inc (Sum.inr w0) (Sum.inl i) * X.cur φ i
        = 0 := by
      simp [inc_inr_inl]
    have h2 : ∑ j : F, (X.subst e Y s t).inc (Sum.inr w0) (Sum.inr j) * (X.cur φ e * Y.cur ψ j)
        = 0 := by
      have hw := hψ w0.1
      simp only [divOn] at hw
      have hterm : ∀ j : F, (X.subst e Y s t).inc (Sum.inr w0) (Sum.inr j) *
          (X.cur φ e * Y.cur ψ j) = X.cur φ e * (Y.inc w0.1 j * Y.cur ψ j) := by
        intro j; rw [inc_inr_inr X e Y]; ring
      simp only [hterm, ← Finset.mul_sum]
      rw [hw]
      simp [feed, w0.2.1, w0.2.2]
    rw [h1, h2]
    simp

end Net

end TwoPort
