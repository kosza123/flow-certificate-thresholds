import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic.Linarith

/-!
# The designated-permutation kernel of the exact DAG assignment adapter

The hypotheses specify only a bounded strict topological rank and the
entry pattern (diagonal, DAG edge, or the sole return t→s). The route and
the complete support of the permutation are derived below.
-/

namespace DagCycleAssignment

variable {V : Type*} {N : ℕ}

def Designated (E : V → V → Prop) (s t : V) (σ : Equiv.Perm V) : Prop :=
  ∀ v, σ v = v ∨ E v (σ v) ∨ (v = t ∧ σ v = s)

def orbit (σ : Equiv.Perm V) (v : V) (k : ℕ) : V :=
  (σ : V → V)^[k] v

@[simp] theorem orbit_zero (σ : Equiv.Perm V) (v : V) : orbit σ v 0 = v := rfl

theorem orbit_succ (σ : Equiv.Perm V) (v : V) (k : ℕ) :
    orbit σ v (k + 1) = σ (orbit σ v k) :=
  Function.iterate_succ_apply' _ _ _

theorem orbit_succ_start (σ : Equiv.Perm V) (v : V) (k : ℕ) :
    orbit σ v (k + 1) = orbit σ (σ v) k :=
  Function.iterate_succ_apply _ _ _

theorem orbit_moved (σ : Equiv.Perm V) {v : V} (hv : σ v ≠ v) (k : ℕ) :
    σ (orbit σ v k) ≠ orbit σ v k := by
  induction k with
  | zero => exact hv
  | succ k ih =>
      rw [orbit_succ]
      intro h
      exact ih (σ.injective h)

theorem rank_growth (rank : V → Fin N) (σ : Equiv.Perm V) (v : V)
    (hstep : ∀ k, rank (orbit σ v k) < rank (orbit σ v (k + 1))) :
    ∀ k, (rank v).val + k ≤ (rank (orbit σ v k)).val := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := hstep k
      change (rank (orbit σ v k)).val < (rank (orbit σ v (k + 1))).val at hs
      omega

theorem no_infinite_increase (rank : V → Fin N) (σ : Equiv.Perm V) (v : V) :
    ¬ (∀ k, rank (orbit σ v k) < rank (orbit σ v (k + 1))) := by
  intro h
  have hg := rank_growth rank σ v h N
  have hb := (rank (orbit σ v N)).isLt
  omega

theorem moved_reaches_return
    {E : V → V → Prop} {s t : V} (rank : V → Fin N)
    (hE : ∀ {u v}, E u v → rank u < rank v)
    {σ : Equiv.Perm V} (hσ : Designated E s t σ)
    {v : V} (hv : σ v ≠ v) : ∃ k, orbit σ v k = t := by
  classical
  by_contra hn
  push_neg at hn
  apply no_infinite_increase rank σ v
  intro k
  rcases hσ (orbit σ v k) with hfix | hedge | hreturn
  · exact False.elim (orbit_moved σ hv k hfix)
  · simpa only [orbit_succ] using hE hedge
  · exact False.elim (hn k hreturn.1)

theorem return_used
    {E : V → V → Prop} {s t : V} (rank : V → Fin N)
    (hE : ∀ {u v}, E u v → rank u < rank v)
    {σ : Equiv.Perm V} (hσ : Designated E s t σ)
    (hne : σ ≠ Equiv.refl V) : σ t = s := by
  classical
  have hmoved : ∃ v, σ v ≠ v := by
    by_contra h
    push_neg at h
    apply hne
    exact Equiv.ext h
  obtain ⟨v, hv⟩ := hmoved
  by_contra hts
  apply no_infinite_increase rank σ v
  intro k
  rcases hσ (orbit σ v k) with hfix | hedge | hreturn
  · exact False.elim (orbit_moved σ hv k hfix)
  · simpa only [orbit_succ] using hE hedge
  · exact False.elim (hts (hreturn.1 ▸ hreturn.2))

/-- A simple path together with the exact action and support of its cycle.
The length is the number of DAG edges; the return is a separate edge. -/
structure RouteWitness (E : V → V → Prop) (s t : V) (σ : Equiv.Perm V) where
  length : ℕ
  positive : 0 < length
  vertices : Fin (length + 1) → V
  start : vertices 0 = s
  finish : vertices (Fin.last length) = t
  injective : Function.Injective vertices
  edges : ∀ i : Fin length, E (vertices i.castSucc) (vertices i.succ)
  follows : ∀ i : Fin length, σ (vertices i.castSucc) = vertices i.succ
  return_step : σ t = s
  support_exact : ∀ v, σ v ≠ v ↔ ∃ i, vertices i = v

theorem orbit_path_injective
    (rank : V → Fin N) (σ : Equiv.Perm V) (s : V) (m : ℕ)
    (hstep : ∀ i < m, rank (orbit σ s i) < rank (orbit σ s (i + 1))) :
    Function.Injective (fun i : Fin (m + 1) => orbit σ s i.val) := by
  have hmono : StrictMono (fun i : Fin (m + 1) => rank (orbit σ s i.val)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    exact hstep i.val i.isLt
  intro i j hij
  apply hmono.injective
  exact congrArg rank hij

theorem predecessor_on_route
    (σ : Equiv.Perm V) (s t : V) (m : ℕ)
    (hend : orbit σ s m = t) (hreturn : σ t = s)
    {v : V} (hmem : ∃ i ≤ m, orbit σ s i = σ v) :
    ∃ i ≤ m, orbit σ s i = v := by
  obtain ⟨i, hi, heq⟩ := hmem
  cases i with
  | zero =>
      refine ⟨m, le_refl m, ?_⟩
      rw [hend]
      apply σ.injective
      rw [hreturn]
      exact heq
  | succ i =>
      refine ⟨i, by omega, ?_⟩
      apply σ.injective
      simpa only [orbit_succ] using heq

theorem reaches_return_on_route
    (σ : Equiv.Perm V) (s t : V) (m : ℕ)
    (hend : orbit σ s m = t) (hreturn : σ t = s)
    (k : ℕ) : ∀ v, orbit σ v k = t → ∃ i ≤ m, orbit σ s i = v := by
  induction k with
  | zero =>
      intro v hv
      exact ⟨m, le_refl m, hend.trans hv.symm⟩
  | succ k ih =>
      intro v hv
      apply predecessor_on_route σ s t m hend hreturn
      apply ih (σ v)
      simpa only [orbit_succ_start] using hv

theorem designated_nonidentity_is_one_route
    {E : V → V → Prop} {s t : V} (hst : s ≠ t)
    (rank : V → Fin N) (hE : ∀ {u v}, E u v → rank u < rank v)
    {σ : Equiv.Perm V} (hσ : Designated E s t σ)
    (hne : σ ≠ Equiv.refl V) : Nonempty (RouteWitness E s t σ) := by
  classical
  have hreturn : σ t = s := return_used rank hE hσ hne
  have hs : σ s ≠ s := by
    intro h
    apply hst
    exact σ.injective (h.trans hreturn.symm)
  have hex : ∃ k, orbit σ s k = t := moved_reaches_return rank hE hσ hs
  let m := Nat.find hex
  have hend : orbit σ s m = t := Nat.find_spec hex
  have hbefore : ∀ i < m, orbit σ s i ≠ t := by
    intro i hi
    exact Nat.find_min hex hi
  have hmpos : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    apply hst
    simpa only [hmzero, orbit_zero] using hend
  have hedges : ∀ i < m, E (orbit σ s i) (orbit σ s (i + 1)) := by
    intro i hi
    rcases hσ (orbit σ s i) with hfix | hedge | hret
    · exact False.elim (orbit_moved σ hs i hfix)
    · simpa only [orbit_succ] using hedge
    · exact False.elim (hbefore i hi hret.1)
  refine ⟨{
    length := m
    positive := hmpos
    vertices := fun i => orbit σ s i.val
    start := rfl
    finish := hend
    injective := orbit_path_injective rank σ s m (fun i hi => hE (hedges i hi))
    edges := fun i => hedges i.val i.isLt
    follows := fun i => (orbit_succ σ s i.val).symm
    return_step := hreturn
    support_exact := ?_
  }⟩
  intro v
  constructor
  · intro hv
    obtain ⟨k, hk⟩ := moved_reaches_return rank hE hσ hv
    obtain ⟨i, hi, heq⟩ := reaches_return_on_route σ s t m hend hreturn k v hk
    exact ⟨⟨i, by omega⟩, heq⟩
  · rintro ⟨i, rfl⟩
    exact orbit_moved σ hs i.val

theorem designated_identity_or_one_route
    {E : V → V → Prop} {s t : V} (hst : s ≠ t)
    (rank : V → Fin N) (hE : ∀ {u v}, E u v → rank u < rank v)
    {σ : Equiv.Perm V} (hσ : Designated E s t σ) :
    σ = Equiv.refl V ∨ Nonempty (RouteWitness E s t σ) := by
  classical
  by_cases h : σ = Equiv.refl V
  · exact Or.inl h
  · exact Or.inr (designated_nonidentity_is_one_route hst rank hE hσ h)

/-- An explicit cyclic successor on the positions of a nonempty path. -/
def positionNext (m : ℕ) (i : Fin (m + 1)) : Fin (m + 1) :=
  if h : i.val < m then ⟨i.val + 1, by omega⟩ else 0

def positionPrev (m : ℕ) (i : Fin (m + 1)) : Fin (m + 1) :=
  if i.val = 0 then Fin.last m else ⟨i.val - 1, by omega⟩

def positionCycle (m : ℕ) : Equiv.Perm (Fin (m + 1)) where
  toFun := positionNext m
  invFun := positionPrev m
  left_inv := by
    intro i
    by_cases hi : i.val < m
    · rw [positionNext, dif_pos hi]
      apply Fin.ext
      simp [positionPrev]
    · have hilast : i = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
      subst i
      simp [positionNext, positionPrev]
  right_inv := by
    intro i
    by_cases hi : i.val = 0
    · have hizero : i = 0 := Fin.ext hi
      subst i
      simp [positionPrev, positionNext]
    · rw [positionPrev, if_neg hi]
      have hprev : i.val - 1 < m := by have := i.isLt; omega
      rw [positionNext, dif_pos hprev]
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

@[simp] theorem positionCycle_castSucc (m : ℕ) (i : Fin m) :
    positionCycle m i.castSucc = i.succ := by
  apply Fin.ext
  simp [positionCycle, positionNext, i.isLt]

@[simp] theorem positionCycle_last (m : ℕ) :
    positionCycle m (Fin.last m) = 0 := by
  simp [positionCycle, positionNext]

theorem positionCycle_no_fixed {m : ℕ} (hm : 0 < m) (i : Fin (m + 1)) :
    positionCycle m i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  change (positionNext m i).val = i.val at hv
  by_cases hi : i.val < m
  · simp only [positionNext, dif_pos hi, Fin.val_mk] at hv
    omega
  · simp only [positionNext, dif_neg hi, Fin.val_zero] at hv
    omega

/-- Extend the explicit position cycle along an injective vertex array,
fixing every vertex outside that array. -/
noncomputable def cyclePermutation {m : ℕ} (p : Fin (m + 1) → V)
    (hp : Function.Injective p) : Equiv.Perm V := by
  classical
  exact (positionCycle m).extendDomain (Equiv.ofInjective p hp)

theorem cyclePermutation_apply {m : ℕ} (p : Fin (m + 1) → V)
    (hp : Function.Injective p) (i : Fin (m + 1)) :
    cyclePermutation p hp (p i) = p (positionCycle m i) := by
  classical
  simpa [cyclePermutation] using
    (Equiv.Perm.extendDomain_apply_image (positionCycle m) (Equiv.ofInjective p hp) i)

theorem cyclePermutation_outside {m : ℕ} (p : Fin (m + 1) → V)
    (hp : Function.Injective p) {v : V} (hv : ¬ ∃ i, p i = v) :
    cyclePermutation p hp v = v := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype
    (positionCycle m) (Equiv.ofInjective p hp) hv

theorem cyclePermutation_support {m : ℕ} (hm : 0 < m)
    (p : Fin (m + 1) → V) (hp : Function.Injective p) (v : V) :
    cyclePermutation p hp v ≠ v ↔ ∃ i, p i = v := by
  classical
  constructor
  · intro h
    by_contra hn
    exact h (cyclePermutation_outside p hp hn)
  · rintro ⟨i, rfl⟩ h
    rw [cyclePermutation_apply] at h
    exact positionCycle_no_fixed hm i (hp h)

structure SimplePath (E : V → V → Prop) (s t : V) where
  length : ℕ
  positive : 0 < length
  vertices : Fin (length + 1) → V
  start : vertices 0 = s
  finish : vertices (Fin.last length) = t
  injective : Function.Injective vertices
  edges : ∀ i : Fin length, E (vertices i.castSucc) (vertices i.succ)

noncomputable def SimplePath.toPerm {E : V → V → Prop} {s t : V}
    (P : SimplePath E s t) : Equiv.Perm V :=
  cyclePermutation P.vertices P.injective

theorem SimplePath.toPerm_return {E : V → V → Prop} {s t : V}
    (P : SimplePath E s t) : P.toPerm t = s := by
  change cyclePermutation P.vertices P.injective t = s
  calc
    cyclePermutation P.vertices P.injective t =
        cyclePermutation P.vertices P.injective (P.vertices (Fin.last P.length)) :=
      congrArg (cyclePermutation P.vertices P.injective) P.finish.symm
    _ = P.vertices (positionCycle P.length (Fin.last P.length)) :=
      cyclePermutation_apply _ _ _
    _ = s := by rw [positionCycle_last, P.start]

theorem SimplePath.toPerm_designated {E : V → V → Prop} {s t : V}
    (P : SimplePath E s t) : Designated E s t P.toPerm := by
  classical
  intro v
  by_cases hv : ∃ i, P.vertices i = v
  · obtain ⟨i, rfl⟩ := hv
    by_cases hi : i.val < P.length
    · let j : Fin P.length := ⟨i.val, hi⟩
      have hij : j.castSucc = i := Fin.ext rfl
      right; left
      rw [← hij, SimplePath.toPerm, cyclePermutation_apply, positionCycle_castSucc]
      exact P.edges j
    · have hilast : i = Fin.last P.length := Fin.ext (by simp only [Fin.val_last]; omega)
      right; right
      rw [hilast, P.finish]
      exact ⟨rfl, P.toPerm_return⟩
  · left
    exact cyclePermutation_outside P.vertices P.injective hv

def RouteWitness.path {E : V → V → Prop} {s t : V} {σ : Equiv.Perm V}
    (W : RouteWitness E s t σ) : SimplePath E s t where
  length := W.length
  positive := W.positive
  vertices := W.vertices
  start := W.start
  finish := W.finish
  injective := W.injective
  edges := W.edges

theorem RouteWitness.reconstructs {E : V → V → Prop} {s t : V} {σ : Equiv.Perm V}
    (W : RouteWitness E s t σ) : W.path.toPerm = σ := by
  classical
  apply Equiv.ext
  intro v
  by_cases hv : ∃ i, W.vertices i = v
  · obtain ⟨i, rfl⟩ := hv
    by_cases hi : i.val < W.length
    · let j : Fin W.length := ⟨i.val, hi⟩
      have hij : j.castSucc = i := Fin.ext rfl
      change cyclePermutation W.vertices W.injective (W.vertices i) = σ (W.vertices i)
      rw [← hij, cyclePermutation_apply, positionCycle_castSucc]
      exact (W.follows j).symm
    · have hilast : i = Fin.last W.length := Fin.ext (by simp only [Fin.val_last]; omega)
      change cyclePermutation W.vertices W.injective (W.vertices i) = σ (W.vertices i)
      rw [hilast, cyclePermutation_apply, positionCycle_last, W.start, W.finish, W.return_step]
  · change cyclePermutation W.vertices W.injective v = σ v
    rw [cyclePermutation_outside W.vertices W.injective hv]
    exact (not_not.mp (fun h => hv ((W.support_exact v).mp h))).symm

/-- Exact characterization. Both extraction and construction are proved;
the right hand correspondence is not a premise of this theorem. -/
theorem designated_iff_identity_or_path
    {E : V → V → Prop} {s t : V} (hst : s ≠ t)
    (rank : V → Fin N) (hE : ∀ {u v}, E u v → rank u < rank v)
    (σ : Equiv.Perm V) :
    Designated E s t σ ↔
      σ = Equiv.refl V ∨ ∃ P : SimplePath E s t, P.toPerm = σ := by
  constructor
  · intro hσ
    rcases designated_identity_or_one_route hst rank hE hσ with hid | hW
    · exact Or.inl hid
    · obtain ⟨W⟩ := hW
      exact Or.inr ⟨W.path, W.reconstructs⟩
  · rintro (rfl | ⟨P, rfl⟩)
    · intro v
      exact Or.inl rfl
    · exact P.toPerm_designated

end DagCycleAssignment

#print axioms DagCycleAssignment.moved_reaches_return
#print axioms DagCycleAssignment.return_used
#print axioms DagCycleAssignment.designated_nonidentity_is_one_route
#print axioms DagCycleAssignment.designated_identity_or_one_route
#print axioms DagCycleAssignment.cyclePermutation_support
#print axioms DagCycleAssignment.SimplePath.toPerm_designated
#print axioms DagCycleAssignment.RouteWitness.reconstructs
#print axioms DagCycleAssignment.designated_iff_identity_or_path
