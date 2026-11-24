import AdapterBounds

/-!
# The pattern of the uncertain entries: conditions (C2) and (C3)

For an incidence `p = (j, side)` let `firstV p`, `secondV p` be the two fresh vertices of its
feature (internal vertices `2i + 1`, `2i + 2` of the chain of its arc, `i` its position).
The uncertain entry of `p` is `(uRow p, uCol p)`:

* for the A-feature of `j` (`side = true`): the feature arc `(firstV p, secondV p)`;
* for the B-feature of `j` (`side = false`): the diagonal entry `(firstV p, firstV p)`.

Results:

* `adapterCost_affine` **(C2)** : for all vertices `x, y` and every real scenario `θ`,
    `C θ x y = C 0 x y + ∑ p, θ p.1 · [x = uRow p ∧ y = uCol p]`,
  so each `θ j` occurs in exactly the two entries of its two incidences, with coefficient `1`;
* `uRow_eq_uCol_iff` : the entry of `p` is diagonal exactly for the B-feature;
* `uRow_injective`, `uCol_injective` **(C3)** : the `2 |J|` uncertain entries have pairwise
  different rows and pairwise different columns.
-/

namespace DagCycleAssignment
namespace Adapter

open Finset Subdivision

variable {V A J : Type*}

theorem internal_eq {length : A → ℕ} {a a' : A} (h : a' = a) {i : Fin (length a + 1)}
    {i' : Fin (length a' + 1)} (hv : i'.val = i.val) :
    (internal length a' i' : Vertex V A length) = internal length a i := by
  subst h
  rw [Fin.ext hv]

theorem internal_arc_eq {length : A → ℕ} {a b : A} {i : Fin (length a + 1)}
    {k : Fin (length b + 1)}
    (h : (internal length a i : Vertex V A length) = internal length b k) :
    a = b ∧ i.val = k.val :=
  ⟨congrArg (fun z : Σ a : A, Fin (length a + 1) => z.1) (Sum.inr.inj h),
    congrArg (fun z : Σ a : A, Fin (length a + 1) => (z.2 : ℕ)) (Sum.inr.inj h)⟩

variable [DecidableEq A] [Fintype J]

section Positions

variable (arcA arcB : J → A)

/-- The incidence at position `n` of the arc `a`, if any. -/
noncomputable def incAt (a : A) (n : ℕ) : Option (Incidence J) :=
  if h : n < mult arcA arcB a then some (slot arcA arcB a ⟨n, h⟩).1 else none

/-- The position of an incidence in the chain of its arc. -/
noncomputable def idx (p : Incidence J) : Fin (mult arcA arcB (arcOf arcA arcB p)) :=
  (slot arcA arcB (arcOf arcA arcB p)).symm ⟨p, rfl⟩

theorem atSlot_of_some {f : Incidence J → ℝ} {a : A} {n : ℕ} {q : Incidence J}
    (h : incAt arcA arcB a n = some q) : atSlot arcA arcB f a n = f q := by
  unfold incAt at h
  unfold atSlot
  by_cases hn : n < mult arcA arcB a
  · rw [dif_pos hn] at h ⊢
    rw [Option.some.inj h]
  · rw [dif_neg hn] at h
    cases h

theorem atSlot_of_none {f : Incidence J → ℝ} {a : A} {n : ℕ}
    (h : incAt arcA arcB a n = none) : atSlot arcA arcB f a n = 0 := by
  unfold incAt at h
  unfold atSlot
  by_cases hn : n < mult arcA arcB a
  · rw [dif_pos hn] at h
    cases h
  · rw [dif_neg hn]

theorem incAt_idx (p : Incidence J) :
    incAt arcA arcB (arcOf arcA arcB p) (idx arcA arcB p).val = some p := by
  unfold incAt
  rw [dif_pos (idx arcA arcB p).isLt]
  unfold idx
  simp

theorem incAt_some {a : A} {n : ℕ} {p : Incidence J} (h : incAt arcA arcB a n = some p) :
    arcOf arcA arcB p = a ∧ (idx arcA arcB p).val = n := by
  unfold incAt at h
  by_cases hn : n < mult arcA arcB a
  · rw [dif_pos hn] at h
    have hp : (slot arcA arcB a ⟨n, hn⟩).1 = p := Option.some.inj h
    generalize hq : slot arcA arcB a ⟨n, hn⟩ = q at hp
    obtain ⟨p', hp'⟩ := q
    simp only at hp
    subst hp
    subst hp'
    refine ⟨rfl, ?_⟩
    unfold idx
    rw [← hq, Equiv.symm_apply_apply]
  · rw [dif_neg hn] at h
    cases h

variable (V)

/-- The first fresh vertex of the feature of an incidence. -/
noncomputable def firstV (p : Incidence J) : Vertex V A (chainLength arcA arcB) :=
  internal (chainLength arcA arcB) (arcOf arcA arcB p)
    ⟨2 * (idx arcA arcB p).val + 1, by
      have := (idx arcA arcB p).isLt
      unfold chainLength
      omega⟩

/-- The second fresh vertex of the feature of an incidence. -/
noncomputable def secondV (p : Incidence J) : Vertex V A (chainLength arcA arcB) :=
  internal (chainLength arcA arcB) (arcOf arcA arcB p)
    ⟨2 * (idx arcA arcB p).val + 2, by
      have := (idx arcA arcB p).isLt
      unfold chainLength
      omega⟩

/-- The row of the uncertain entry of an incidence. -/
noncomputable def uRow (p : Incidence J) : Vertex V A (chainLength arcA arcB) :=
  firstV V arcA arcB p

/-- The column of the uncertain entry of an incidence. -/
noncomputable def uCol (p : Incidence J) : Vertex V A (chainLength arcA arcB) :=
  if p.2 = true then secondV V arcA arcB p else firstV V arcA arcB p

theorem internal_eq_firstV_iff (a : A) (i : Fin (chainLength arcA arcB a + 1))
    (p : Incidence J) :
    (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
        = firstV V arcA arcB p ↔
      i.val % 2 = 1 ∧ incAt arcA arcB a (i.val / 2) = some p := by
  constructor
  · intro h
    unfold firstV at h
    obtain ⟨h1, h2⟩ := internal_arc_eq h
    have h2' : i.val = 2 * (idx arcA arcB p).val + 1 := h2
    have h3 : i.val / 2 = (idx arcA arcB p).val := by omega
    refine ⟨by omega, ?_⟩
    rw [h3, h1]
    exact incAt_idx arcA arcB p
  · rintro ⟨hodd, hinc⟩
    obtain ⟨ha, hidx⟩ := incAt_some arcA arcB hinc
    unfold firstV
    exact internal_eq ha.symm (by
      show i.val = 2 * (idx arcA arcB p).val + 1
      omega)

theorem firstV_injective : Function.Injective (firstV V arcA arcB) := by
  intro p p' h
  have h2 : incAt arcA arcB (arcOf arcA arcB p) ((2 * (idx arcA arcB p).val + 1) / 2) = some p' :=
    ((internal_eq_firstV_iff V arcA arcB (arcOf arcA arcB p) _ p').1 h).2
  have h3 : (2 * (idx arcA arcB p).val + 1) / 2 = (idx arcA arcB p).val := by omega
  rw [h3, incAt_idx] at h2
  exact Option.some.inj h2

theorem secondV_injective : Function.Injective (secondV V arcA arcB) := by
  intro p p' h
  unfold secondV at h
  obtain ⟨h1, h2⟩ := internal_arc_eq h
  have h2' : 2 * (idx arcA arcB p).val + 2 = 2 * (idx arcA arcB p').val + 2 := h2
  have e1 := incAt_idx arcA arcB p
  have e2 := incAt_idx arcA arcB p'
  rw [show (idx arcA arcB p).val = (idx arcA arcB p').val by omega, h1] at e1
  exact Option.some.inj (e1.symm.trans e2)

theorem firstV_ne_secondV (p p' : Incidence J) :
    firstV V arcA arcB p ≠ secondV V arcA arcB p' := by
  intro h
  unfold firstV secondV at h
  have h2 : 2 * (idx arcA arcB p).val + 1 = 2 * (idx arcA arcB p').val + 2 :=
    (internal_arc_eq h).2
  omega

/-- **(C3), rows.**  The uncertain entries lie in pairwise different rows. -/
theorem uRow_injective : Function.Injective (uRow V arcA arcB) :=
  firstV_injective V arcA arcB

/-- **(C3), columns.**  The uncertain entries lie in pairwise different columns. -/
theorem uCol_injective : Function.Injective (uCol V arcA arcB) := by
  intro p p' h
  unfold uCol at h
  by_cases hp : p.2 = true <;> by_cases hp' : p'.2 = true
  · rw [if_pos hp, if_pos hp'] at h
    exact secondV_injective V arcA arcB h
  · rw [if_pos hp, if_neg hp'] at h
    exact absurd h.symm (firstV_ne_secondV V arcA arcB p' p)
  · rw [if_neg hp, if_pos hp'] at h
    exact absurd h (firstV_ne_secondV V arcA arcB p p')
  · rw [if_neg hp, if_neg hp'] at h
    exact firstV_injective V arcA arcB h

/-- The uncertain entry of an incidence is diagonal exactly for the B-feature. -/
theorem uRow_eq_uCol_iff (p : Incidence J) :
    uRow V arcA arcB p = uCol V arcA arcB p ↔ p.2 = false := by
  unfold uRow uCol
  by_cases hp : p.2 = true
  · rw [if_pos hp]
    constructor
    · intro h
      exact absurd h (firstV_ne_secondV V arcA arcB p p)
    · intro h
      rw [hp] at h
      cases h
  · rw [if_neg hp]
    exact ⟨fun _ => by simpa using hp, fun _ => rfl⟩

/-- Which pairs of internal vertices are the uncertain entry of `p`. -/
theorem uEntry_iff (a b : A) (i : Fin (chainLength arcA arcB a + 1))
    (k : Fin (chainLength arcA arcB b + 1)) (p : Incidence J) :
    ((internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
          = uRow V arcA arcB p ∧
        (internal (chainLength arcA arcB) b k : Vertex V A (chainLength arcA arcB))
          = uCol V arcA arcB p) ↔
      (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
          = firstV V arcA arcB p ∧ a = b ∧
        ((p.2 = true ∧ k.val = i.val + 1) ∨ (p.2 = false ∧ k.val = i.val)) := by
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
        = firstV V arcA arcB p := hx
    have hxf := hx'
    unfold firstV at hxf
    obtain ⟨ha, hi⟩ := internal_arc_eq hxf
    have hi' : i.val = 2 * (idx arcA arcB p).val + 1 := hi
    unfold uCol at hy
    by_cases hp : p.2 = true
    · rw [if_pos hp] at hy
      unfold secondV at hy
      obtain ⟨hb, hk⟩ := internal_arc_eq hy
      have hk' : k.val = 2 * (idx arcA arcB p).val + 2 := hk
      exact ⟨hx', ha.trans hb.symm, Or.inl ⟨hp, by omega⟩⟩
    · rw [if_neg hp] at hy
      unfold firstV at hy
      obtain ⟨hb, hk⟩ := internal_arc_eq hy
      have hk' : k.val = 2 * (idx arcA arcB p).val + 1 := hk
      exact ⟨hx', ha.trans hb.symm, Or.inr ⟨by simpa using hp, by omega⟩⟩
  · rintro ⟨hx, hab, hcase⟩
    refine ⟨hx, ?_⟩
    subst hab
    have hxf := hx
    unfold firstV at hxf
    obtain ⟨ha, hi⟩ := internal_arc_eq hxf
    have hi' : i.val = 2 * (idx arcA arcB p).val + 1 := hi
    unfold uCol
    rcases hcase with ⟨hp, hk⟩ | ⟨hp, hk⟩
    · rw [if_pos hp]
      unfold secondV
      exact internal_eq ha (by
        show k.val = 2 * (idx arcA arcB p).val + 2
        omega)
    · rw [if_neg (by rw [hp]; simp), Fin.ext hk]
      exact hx

variable [DecidableEq V]

/-- The incidences whose first vertex is a given internal vertex. -/
theorem sum_firstV (g : Incidence J → ℝ) (a : A) (i : Fin (chainLength arcA arcB a + 1)) :
    ∑ p : Incidence J, g p *
        (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
            = firstV V arcA arcB p then 1 else 0)
      = if i.val % 2 = 1 then atSlot arcA arcB g a (i.val / 2) else 0 := by
  by_cases hodd : i.val % 2 = 1
  · rw [if_pos hodd]
    cases hinc : incAt arcA arcB a (i.val / 2) with
    | none =>
        rw [atSlot_of_none arcA arcB hinc]
        refine Finset.sum_eq_zero fun p _ => ?_
        rw [if_neg, mul_zero]
        intro h
        have h' := ((internal_eq_firstV_iff V arcA arcB a i p).1 h).2
        rw [hinc] at h'
        cases h'
    | some q =>
        rw [atSlot_of_some arcA arcB hinc, Finset.sum_eq_single q]
        · rw [if_pos ((internal_eq_firstV_iff V arcA arcB a i q).2 ⟨hodd, hinc⟩), mul_one]
        · intro p _ hpq
          rw [if_neg, mul_zero]
          intro h
          have h' := ((internal_eq_firstV_iff V arcA arcB a i p).1 h).2
          rw [hinc] at h'
          exact hpq (Option.some.inj h').symm
        · intro h
          exact absurd (Finset.mem_univ q) h
  · rw [if_neg hodd]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg, mul_zero]
    intro h
    exact hodd ((internal_eq_firstV_iff V arcA arcB a i p).1 h).1

/-! ### (C2): the cost matrix is affine in the scenario, with the stated pattern -/

omit [DecidableEq A] [Fintype J] [DecidableEq V] in
theorem featureArc_split (β θ : J → ℝ) (p : Incidence J) :
    featureArc β θ p = featureArc β (fun _ => 0) p + (if p.2 = true then θ p.1 else 0) := by
  unfold featureArc
  by_cases hp : p.2 = true
  · rw [if_pos hp, if_pos hp, if_pos hp, zero_add]
  · rw [if_neg hp, if_neg hp, if_neg hp, add_zero]

omit [DecidableEq V] in
theorem atSlot_add (f g : Incidence J → ℝ) (a : A) (n : ℕ) :
    atSlot arcA arcB (fun p => f p + g p) a n
      = atSlot arcA arcB f a n + atSlot arcA arcB g a n := by
  unfold atSlot
  by_cases hn : n < mult arcA arcB a
  · rw [dif_pos hn, dif_pos hn, dif_pos hn]
  · rw [dif_neg hn, dif_neg hn, dif_neg hn, add_zero]

omit [DecidableEq V] in
theorem stepCost_split (β θ : J → ℝ) (a : A) (n : ℕ) :
    stepCost arcA arcB β θ a n = stepCost arcA arcB β (fun _ => 0) a n
      + (if n % 2 = 1
          then atSlot arcA arcB (fun p => if p.2 = true then θ p.1 else 0) a (n / 2) else 0) := by
  unfold stepCost
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn, if_pos hn, ← atSlot_add]
    have h : featureArc β θ
        = fun p => featureArc β (fun _ => 0) p + (if p.2 = true then θ p.1 else 0) :=
      funext (featureArc_split β θ)
    rw [h]
  · rw [if_neg hn, if_neg hn, if_neg hn, add_zero]

omit [DecidableEq V] in
theorem diagCost_zero (a : A) (n : ℕ) : diagCost arcA arcB (fun _ => (0 : ℝ)) a n = 0 := by
  unfold diagCost
  by_cases hn : n % 2 = 1
  · rw [if_pos hn]
    unfold atSlot
    by_cases hm : n / 2 < mult arcA arcB a
    · rw [dif_pos hm]
      unfold featureDiag
      split_ifs <;> rfl
    · rw [dif_neg hm]
  · rw [if_neg hn]

theorem adapterCost_internal (tail head : A → V) (s t : V) (α : A → ℝ) (β θ : J → ℝ) (δ H : ℝ)
    (a b : A) (i : Fin (chainLength arcA arcB a + 1)) (k : Fin (chainLength arcA arcB b + 1)) :
    adapterCost tail head arcA arcB s t α β θ δ H
        (internal (chainLength arcA arcB) a i) (internal (chainLength arcA arcB) b k)
      = if a = b then
          (if k.val = i.val then diagCost arcA arcB θ a i.val
           else if k.val = i.val + 1 then stepCost arcA arcB β θ a i.val else H)
        else H := rfl

/-- **(C2).**  The cost matrix is the matrix of the zero scenario plus `θ j` in the uncertain
entries of the two incidences of `j`; nothing else depends on `θ`. -/
theorem adapterCost_affine (tail head : A → V) (s t : V) (α : A → ℝ) (β θ : J → ℝ) (δ H : ℝ)
    (x y : Vertex V A (chainLength arcA arcB)) :
    adapterCost tail head arcA arcB s t α β θ δ H x y
      = adapterCost tail head arcA arcB s t α β (fun _ => 0) δ H x y
        + ∑ p : Incidence J,
            θ p.1 * (if x = uRow V arcA arcB p ∧ y = uCol V arcA arcB p then 1 else 0) := by
  rcases x with u | ⟨a, i⟩
  · have hz : ∑ p : Incidence J, θ p.1 *
        (if (Sum.inl u : Vertex V A (chainLength arcA arcB)) = uRow V arcA arcB p
            ∧ y = uCol V arcA arcB p then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun p _ => by
        rw [if_neg, mul_zero]
        rintro ⟨h, _⟩
        cases h
    rw [hz, add_zero]
    rcases y with v | ⟨b, k⟩ <;> rfl
  · rcases y with v | ⟨b, k⟩
    · have hz : ∑ p : Incidence J, θ p.1 *
          (if (Sum.inr ⟨a, i⟩ : Vertex V A (chainLength arcA arcB)) = uRow V arcA arcB p
              ∧ (Sum.inl v : Vertex V A (chainLength arcA arcB)) = uCol V arcA arcB p
            then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun p _ => by
          rw [if_neg, mul_zero]
          rintro ⟨_, h⟩
          unfold uCol at h
          split_ifs at h <;> cases h
      rw [hz, add_zero]
      rfl
    · show adapterCost tail head arcA arcB s t α β θ δ H
          (internal (chainLength arcA arcB) a i) (internal (chainLength arcA arcB) b k)
        = adapterCost tail head arcA arcB s t α β (fun _ => 0) δ H
            (internal (chainLength arcA arcB) a i) (internal (chainLength arcA arcB) b k)
          + ∑ p : Incidence J, θ p.1 *
              (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
                    = uRow V arcA arcB p
                  ∧ (internal (chainLength arcA arcB) b k : Vertex V A (chainLength arcA arcB))
                    = uCol V arcA arcB p then 1 else 0)
      rw [adapterCost_internal, adapterCost_internal]
      simp only [uEntry_iff V arcA arcB a b i k]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_pos rfl]
        by_cases hki : k.val = i.val
        · rw [if_pos hki, if_pos hki, diagCost_zero, zero_add]
          have hterm : ∀ p : Incidence J, θ p.1 *
              (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
                    = firstV V arcA arcB p ∧ a = a ∧
                  ((p.2 = true ∧ k.val = i.val + 1) ∨ (p.2 = false ∧ k.val = i.val))
                then (1 : ℝ) else 0)
              = featureDiag θ p *
                (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
                    = firstV V arcA arcB p then 1 else 0) := by
            intro p
            by_cases hF : (internal (chainLength arcA arcB) a i :
                Vertex V A (chainLength arcA arcB)) = firstV V arcA arcB p <;>
              by_cases hp : p.2 = true <;> simp [featureDiag, hF, hp, hki]
          rw [Finset.sum_congr rfl (fun p _ => hterm p),
            sum_firstV V arcA arcB (featureDiag θ) a i]
          rfl
        · rw [if_neg hki, if_neg hki]
          by_cases hk1 : k.val = i.val + 1
          · rw [if_pos hk1, if_pos hk1, stepCost_split arcA arcB β θ a i.val]
            congr 1
            have hterm : ∀ p : Incidence J, θ p.1 *
                (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
                      = firstV V arcA arcB p ∧ a = a ∧
                    ((p.2 = true ∧ k.val = i.val + 1) ∨ (p.2 = false ∧ k.val = i.val))
                  then (1 : ℝ) else 0)
                = (if p.2 = true then θ p.1 else 0) *
                  (if (internal (chainLength arcA arcB) a i :
                      Vertex V A (chainLength arcA arcB)) = firstV V arcA arcB p
                    then 1 else 0) := by
              intro p
              by_cases hF : (internal (chainLength arcA arcB) a i :
                  Vertex V A (chainLength arcA arcB)) = firstV V arcA arcB p <;>
                by_cases hp : p.2 = true <;> simp [hF, hp, hki, hk1]
            rw [Finset.sum_congr rfl (fun p _ => hterm p),
              sum_firstV V arcA arcB (fun p => if p.2 = true then θ p.1 else 0) a i]
          · rw [if_neg hk1, if_neg hk1]
            have hz : ∑ p : Incidence J, θ p.1 *
                (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
                      = firstV V arcA arcB p ∧ a = a ∧
                    ((p.2 = true ∧ k.val = i.val + 1) ∨ (p.2 = false ∧ k.val = i.val))
                  then (1 : ℝ) else 0) = 0 :=
              Finset.sum_eq_zero fun p _ => by
                rw [if_neg, mul_zero]
                rintro ⟨_, _, h | h⟩
                · exact hk1 h.2
                · exact hki h.2
            rw [hz, add_zero]
      · rw [if_neg hab, if_neg hab]
        have hz : ∑ p : Incidence J, θ p.1 *
            (if (internal (chainLength arcA arcB) a i : Vertex V A (chainLength arcA arcB))
                  = firstV V arcA arcB p ∧ a = b ∧
                ((p.2 = true ∧ k.val = i.val + 1) ∨ (p.2 = false ∧ k.val = i.val))
              then (1 : ℝ) else 0) = 0 :=
          Finset.sum_eq_zero fun p _ => by
            rw [if_neg, mul_zero]
            rintro ⟨_, h, _⟩
            exact hab h
        rw [hz, add_zero]

end Positions

end Adapter
end DagCycleAssignment
