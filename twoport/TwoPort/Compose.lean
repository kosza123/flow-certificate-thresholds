/-
  Composition of two-ports is a matrix product.

  `X.comp Y` replaces the observed edge of `X` by the two-port `Y`; the observed edge of the
  result is the observed edge of `Y`.  If `X` and `Y` have Möbius data `(M, κ)` and `(M', κ')`
  then `X.comp Y` has data `(M * M', κ * κ')` (`hasMob_comp`).  Iterating over a list of
  gadgets (`chain`) gives a unit-resistance network whose observed current under unit feed is
  `∏ κ / q`, where `q` is the second coordinate of `(∏ M) (1, 1)` (`chain_current`).
-/
import TwoPort.Mobius

open Finset

set_option linter.unusedSectionVars false

namespace TwoPort

variable {V E W F : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]

theorem Net.ext' {N N' : Net V E} (h1 : N.src = N'.src) (h2 : N.tgt = N'.tgt)
    (h3 : N.res = N'.res) : N = N' := by
  cases N; cases N'; simp_all

/-! ### Möbius data -/

/-- Numerator of the Möbius map of `M`. -/
def num (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) : ℝ := M 0 0 * r + M 0 1

/-- Denominator of the Möbius map of `M`. -/
def den (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) : ℝ := M 1 0 * r + M 1 1

theorem num_mul (M M' : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) :
    num (M * M') r = M 0 0 * num M' r + M 0 1 * den M' r := by
  simp only [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem den_mul (M M' : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) :
    den (M * M') r = M 1 0 * num M' r + M 1 1 * den M' r := by
  simp only [num, den, Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- `den M 1` is the second coordinate of `M (1, 1)`. -/
theorem den_one_eq (M : Matrix (Fin 2) (Fin 2) ℝ) : den M 1 = (M.mulVec ![1, 1]) 1 := by
  simp [den, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

namespace Port

/-- The two-port has Möbius data `(M, κ)`: for every positive resistance `r` of the observed
edge, the port resistance is `num M r / den M r` and the observed current is `κ / den M r`. -/
def HasMob (X : Port V E) (M : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) : Prop :=
  ∀ r, 0 < r → 0 < den M r ∧ 0 < num M r ∧ X.Resp r (num M r / den M r) (κ / den M r)

/-- `X` with its observed edge replaced by the two-port `Y`. -/
def comp (X : Port V E) (Y : Port W F) :
    Port (V ⊕ {w : W // w ≠ Y.s ∧ w ≠ Y.t}) ({i : E // i ≠ X.e} ⊕ F) where
  toNet := X.toNet.subst X.e Y.toNet Y.s Y.t
  s := Sum.inl X.s
  t := Sum.inl X.t
  e := Sum.inr Y.e

theorem comp_withRes (X : Port V E) (Y : Port W F) (r R : ℝ) :
    (X.comp Y).withRes r = (X.withRes R).subst X.e (Y.withRes r) Y.s Y.t := by
  apply Net.ext'
  · rfl
  · rfl
  · funext i
    cases i with
    | inl i =>
      show Function.update (Sum.elim (fun i : {i : E // i ≠ X.e} => X.res i) Y.res)
          (Sum.inr Y.e) r (Sum.inl i) = Function.update X.res X.e R i.1
      rw [Function.update_of_ne (by simp), Function.update_of_ne i.2]
      rfl
    | inr j =>
      show Function.update (Sum.elim (fun i : {i : E // i ≠ X.e} => X.res i) Y.res)
          (Sum.inr Y.e) r (Sum.inr j) = Function.update Y.res Y.e r j
      by_cases h : j = Y.e
      · rw [h, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (fun h' => h (Sum.inr.inj h')), Function.update_of_ne h]
        rfl

theorem feed_inl (s t : V) :
    (Sum.elim (feed s t) fun _ => 0 : V ⊕ {w : W // w ≠ (Y : Port W F).s ∧ w ≠ Y.t} → ℝ) =
      feed (Sum.inl s) (Sum.inl t) := by
  funext v
  cases v <;> simp [feed]

/-- Response of a composite two-port. -/
theorem resp_comp (X : Port V E) (Y : Port W F) (hst : Y.s ≠ Y.t) {r RY JY RX JX : ℝ}
    (hY : Y.Resp r RY JY) (hX : X.Resp RY RX JX) (hRY : RY ≠ 0) :
    (X.comp Y).Resp r RX (JX * JY) := by
  obtain ⟨ψ, hψ, hψR, hψJ⟩ := hY
  obtain ⟨φ, hφ, hφR, hφJ⟩ := hX
  have hR : (X.withRes RY).res X.e = ψ Y.s - ψ Y.t := by
    rw [hψR]; simp [withRes]
  have hres : (X.withRes RY).res X.e ≠ 0 := by
    simpa [withRes] using hRY
  obtain ⟨h1, _, h3⟩ := Net.subst_isSol (X.withRes RY) X.e (Y.withRes r) hst hφ hψ hR hres
  refine ⟨Net.glue (X.withRes RY) X.e Y.s Y.t φ ψ, ?_, ?_, ?_⟩
  · rw [X.comp_withRes Y r RY]
    have := feed_inl (Y := Y) X.s X.t
    show ((X.withRes RY).subst X.e (Y.withRes r) Y.s Y.t).IsSol
      (feed (Sum.inl X.s) (Sum.inl X.t)) _
    rw [← this]
    exact h1
  · exact hφR
  · rw [X.comp_withRes Y r RY]
    show ((X.withRes RY).subst X.e (Y.withRes r) Y.s Y.t).cur _ (Sum.inr Y.e) = _
    rw [h3 Y.e, hφJ, hψJ]

/-- **Composition is a matrix product.** -/
theorem hasMob_comp {X : Port V E} {Y : Port W F} {M M' : Matrix (Fin 2) (Fin 2) ℝ}
    {κ κ' : ℝ} (hX : X.HasMob M κ) (hY : Y.HasMob M' κ') (hst : Y.s ≠ Y.t) :
    (X.comp Y).HasMob (M * M') (κ * κ') := by
  intro r hr
  obtain ⟨hd', hn', hrY⟩ := hY r hr
  have hRpos : 0 < num M' r / den M' r := div_pos hn' hd'
  obtain ⟨hd, hn, hrX⟩ := hX _ hRpos
  have hd0 : den M' r ≠ 0 := hd'.ne'
  have hden : den (M * M') r = den M (num M' r / den M' r) * den M' r := by
    rw [den_mul]
    show _ = (M 1 0 * (num M' r / den M' r) + M 1 1) * den M' r
    field_simp
  have hnum : num (M * M') r = num M (num M' r / den M' r) * den M' r := by
    rw [num_mul]
    show _ = (M 0 0 * (num M' r / den M' r) + M 0 1) * den M' r
    field_simp
  refine ⟨by rw [hden]; exact mul_pos hd hd', by rw [hnum]; exact mul_pos hn hd', ?_⟩
  have := X.resp_comp Y hst hrY hrX hRpos.ne'
  have e1 : num (M * M') r / den (M * M') r =
      num M (num M' r / den M' r) / den M (num M' r / den M' r) := by
    rw [hnum, hden]; field_simp
  have e2 : κ * κ' / den (M * M') r =
      κ / den M (num M' r / den M' r) * (κ' / den M' r) := by
    rw [hden]; field_simp
  rw [e1, e2]
  exact this

/-- Scaling `(M, κ)` by a positive number does not change the data. -/
theorem HasMob.smul {X : Port V E} {M : Matrix (Fin 2) (Fin 2) ℝ} {κ : ℝ} (h : X.HasMob M κ)
    {c : ℝ} (hc : 0 < c) : X.HasMob (c • M) (c * κ) := by
  intro r hr
  obtain ⟨hd, hn, hresp⟩ := h r hr
  have hden : den (c • M) r = c * den M r := by
    simp only [den, Matrix.smul_apply, smul_eq_mul]; ring
  have hnum : num (c • M) r = c * num M r := by
    simp only [num, Matrix.smul_apply, smul_eq_mul]; ring
  refine ⟨by rw [hden]; exact mul_pos hc hd, by rw [hnum]; exact mul_pos hc hn, ?_⟩
  have e1 : num (c • M) r / den (c • M) r = num M r / den M r := by
    rw [hnum, hden]; field_simp
  have e2 : c * κ / den (c • M) r = κ / den M r := by
    rw [hden]; field_simp
  rw [e1, e2]
  exact hresp

/-- A two-port with open-circuit data `S, P, Q` and positive resistances off the observed
edge has Möbius data `(mobM S P Q, Q)`. -/
theorem hasMob_of_data {X : Port V E} {S P Q : ℝ} (h : X.Data S P Q)
    (hpos : ∀ i, i ≠ X.e → 0 < X.res i) (hst : X.s ≠ X.t) : X.HasMob (mobM S P Q) Q := by
  intro r hr
  have hP := h.P_nonneg hpos
  have hS := h.S_pos hpos hst
  have hQ := h.sq_le hpos
  have hden : den (mobM S P Q) r = r + P := by simp [den, mobM]
  have hnum : num (mobM S P Q) r = S * r + (S * P - Q ^ 2) := by simp [num, mobM]
  have hd : 0 < r + P := by linarith
  refine ⟨by rw [hden]; exact hd, by rw [hnum]; nlinarith [mul_pos hS hr], ?_⟩
  rw [hden, hnum]
  exact X.resp_of_data h hr.ne' hd.ne'

end Port

/-! ### Iteration over a list of gadgets -/

/-- A two-port together with its (finite) vertex and edge types. -/
structure TP where
  V : Type
  E : Type
  [fV : Fintype V]
  [fE : Fintype E]
  [dV : DecidableEq V]
  [dE : DecidableEq E]
  port : Port V E

attribute [instance] TP.fV TP.fE TP.dV TP.dE

/-- Composition of packaged two-ports. -/
def TP.comp (A B : TP) : TP where
  V := A.V ⊕ {w : B.V // w ≠ B.port.s ∧ w ≠ B.port.t}
  E := {i : A.E // i ≠ A.port.e} ⊕ B.E
  port := A.port.comp B.port

/-- A single edge between its two ports, as a two-port observing itself. -/
def edgePort : Port (Fin 2) Unit where
  src := fun _ => 0
  tgt := fun _ => 1
  res := fun _ => 1
  s := 0
  t := 1
  e := ()

/-- A single edge between its two ports. -/
def TP.edge : TP where
  V := Fin 2
  E := Unit
  port := edgePort

/-- A gadget: a two-port with unit resistances off its observed edge, distinct ports, and
Möbius data `(M, κ)`. -/
structure Gadget where
  tp : TP
  M : Matrix (Fin 2) (Fin 2) ℝ
  κ : ℝ
  hst : tp.port.s ≠ tp.port.t
  hunit : ∀ i, i ≠ tp.port.e → tp.port.res i = 1
  hmob : tp.port.HasMob M κ

/-- Nest the gadgets of the list: the first is outermost, a single edge is innermost. -/
def chain : List Gadget → TP
  | [] => TP.edge
  | g :: l => g.tp.comp (chain l)

theorem edgePort_hasMob : edgePort.HasMob 1 1 := by
  intro r hr
  have hden : den (1 : Matrix (Fin 2) (Fin 2) ℝ) r = 1 := by simp [den]
  have hnum : num (1 : Matrix (Fin 2) (Fin 2) ℝ) r = r := by simp [num]
  refine ⟨by rw [hden]; exact one_pos, by rw [hnum]; exact hr, ?_⟩
  rw [hden, hnum]
  have hcur : ∀ i : Unit, (edgePort.withRes r).cur (fun v : Fin 2 => if v = 0 then r else 0) i
      = 1 := by
    intro i
    simp [Net.cur, Net.drop, Port.withRes, edgePort, hr.ne']
  refine ⟨fun v : Fin 2 => if v = 0 then r else 0, ?_, ?_, ?_⟩
  · intro v
    show ∑ i : Unit, (edgePort.withRes r).inc v i *
      (edgePort.withRes r).cur (fun v : Fin 2 => if v = 0 then r else 0) i = feed 0 1 v
    rw [Fintype.sum_unique, hcur, mul_one]
    fin_cases v <;> simp [Net.inc, Port.withRes, edgePort, feed]
  · simp [edgePort]
  · rw [hcur]; norm_num

theorem edge_hasMob : TP.edge.port.HasMob 1 1 := edgePort_hasMob

theorem card_comp_edges (A B : TP) :
    Fintype.card (A.comp B).E = (Fintype.card A.E - 1) + Fintype.card B.E := by
  show Fintype.card ({i : A.E // i ≠ A.port.e} ⊕ B.E) = _
  rw [Fintype.card_sum, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Everything about a chain of gadgets. -/
theorem chain_spec (l : List Gadget) :
    (chain l).port.s ≠ (chain l).port.t ∧
    (∀ i, i ≠ (chain l).port.e → (chain l).port.res i = 1) ∧
    (chain l).port.HasMob (l.map (·.M)).prod (l.map (·.κ)).prod ∧
    Fintype.card (chain l).E = (l.map fun g => Fintype.card g.tp.E - 1).sum + 1 := by
  induction l with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (0 : Fin 2) ≠ 1
      decide
    · intro i hi; exact absurd rfl hi
    · simp only [List.map_nil, List.prod_nil]
      exact edge_hasMob
    · simp only [List.map_nil, List.sum_nil, zero_add]
      exact Fintype.card_unit
  | cons g l ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (Sum.inl g.tp.port.s : g.tp.V ⊕ _) ≠ Sum.inl g.tp.port.t
      exact fun h => g.hst (Sum.inl.inj h)
    · intro i hi
      cases i with
      | inl i => exact g.hunit i.1 i.2
      | inr j => exact ih2 j fun h => hi (congrArg Sum.inr h)
    · simp only [List.map_cons, List.prod_cons]
      exact Port.hasMob_comp g.hmob ih3 ih1
    · show Fintype.card (g.tp.comp (chain l)).E = _
      rw [card_comp_edges, ih4]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- At resistance 1 on the observed edge the chain is a unit-resistance network. -/
theorem chain_unit (l : List Gadget) (i : (chain l).E) :
    ((chain l).port.withRes 1).res i = 1 := by
  by_cases h : i = (chain l).port.e
  · subst h; simp [Port.withRes]
  · simp [Port.withRes, Function.update_of_ne h, (chain_spec l).2.1 i h]

/-- **Telescoping.**  In the unit-resistance network `chain l`, under unit feed at the ports,
the current through the innermost edge is `∏ κ / q`, where `q = den (∏ M) 1 > 0` is the
second coordinate of `(∏ M) (1, 1)`.  The current is the same for every solution. -/
theorem chain_current (l : List Gadget) :
    0 < den (l.map (·.M)).prod 1 ∧
    (∃ φ, ((chain l).port.withRes 1).IsSol (feed (chain l).port.s (chain l).port.t) φ) ∧
    ∀ φ, ((chain l).port.withRes 1).IsSol (feed (chain l).port.s (chain l).port.t) φ →
      ((chain l).port.withRes 1).cur φ (chain l).port.e =
        (l.map (·.κ)).prod / den (l.map (·.M)).prod 1 := by
  obtain ⟨hd, _, φ, hφ, _, hJ⟩ := (chain_spec l).2.2.1 1 one_pos
  refine ⟨hd, ⟨φ, hφ⟩, fun φ' hφ' => ?_⟩
  rw [← hJ]
  exact Net.cur_unique _ (fun i _ => by rw [chain_unit l i]; exact one_pos) hφ' hφ
    (Finset.mem_univ _)

end TwoPort
