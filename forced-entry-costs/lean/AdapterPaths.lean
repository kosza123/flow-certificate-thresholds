import AdapterCost
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Cases

/-!
# Paths of the original graph and routes of the subdivided graph

A path of the original graph is a list of arcs (`IsWalk tail head u v l`: the arcs of `l` lead
from `u` to `v`; in an acyclic graph every such walk is a path).  Parallel arcs are different
arcs, so a path is not determined by its vertices.

* `walk_of_designated` : for a designated permutation `σ` that selects the return entry
  (`σ t = s`) there is a path `l` from `s` to `t` in the original graph with
  `a ∈ l ↔ the arc a is used by σ`.
* `walkPerm`, `walkPerm_designated`, `walkPerm_return`, `walkPerm_used` : conversely, for every
  path `l` from `s` to `t` there is a designated permutation that selects the return entry and
  uses exactly the arcs of `l`.

Acyclicity is given by a rank that increases along every arc.
-/

namespace DagCycleAssignment
namespace Subdivision

variable {V A : Type*}

/-- The arcs of `l` lead from `u` to `v` in the original graph. -/
def IsWalk (tail head : A → V) : V → V → List A → Prop
  | u, v, [] => u = v
  | u, v, a :: l => tail a = u ∧ IsWalk tail head (head a) v l

section Walks

variable (tail head : A → V)

theorem walk_next {v : V} : ∀ (l : List A) (u : V), IsWalk tail head u v l →
    ∀ a ∈ l, head a = v ∨ ∃ c ∈ l, tail c = head a := by
  intro l
  induction l with
  | nil =>
      intro u _ a ha
      cases ha
  | cons a0 l' ih =>
      intro u hw a ha
      obtain ⟨_, hw'⟩ := hw
      rcases List.mem_cons.1 ha with heq | ha'
      · rw [heq]
        cases l' with
        | nil => exact Or.inl hw'
        | cons c l'' =>
            exact Or.inr ⟨c, List.mem_cons_of_mem _ List.mem_cons_self, hw'.1⟩
      · rcases ih (head a0) hw' a ha' with h | ⟨c, hc, hct⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, hct⟩

theorem walk_prev {v : V} : ∀ (l : List A) (u : V), IsWalk tail head u v l →
    ∀ a ∈ l, tail a = u ∨ ∃ c ∈ l, head c = tail a := by
  intro l
  induction l with
  | nil =>
      intro u _ a ha
      cases ha
  | cons a0 l' ih =>
      intro u hw a ha
      obtain ⟨h0, hw'⟩ := hw
      rcases List.mem_cons.1 ha with heq | ha'
      · left
        rw [heq]
        exact h0
      · rcases ih (head a0) hw' a ha' with h | ⟨c, hc, hct⟩
        · exact Or.inr ⟨a0, List.mem_cons_self, h.symm⟩
        · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, hct⟩

theorem walk_first {u v : V} (l : List A) (hw : IsWalk tail head u v l) (huv : u ≠ v) :
    ∃ a ∈ l, tail a = u := by
  cases l with
  | nil => exact absurd hw huv
  | cons a l' => exact ⟨a, List.mem_cons_self, hw.1⟩

theorem walk_last {v : V} : ∀ (l : List A) (u : V), IsWalk tail head u v l → u ≠ v →
    ∃ a ∈ l, head a = v := by
  intro l
  induction l with
  | nil =>
      intro u hw huv
      exact absurd hw huv
  | cons a0 l' ih =>
      intro u hw _
      obtain ⟨_, hw'⟩ := hw
      by_cases h : head a0 = v
      · exact ⟨a0, List.mem_cons_self, h⟩
      · obtain ⟨a, ha, hav⟩ := ih (head a0) hw' h
        exact ⟨a, List.mem_cons_of_mem _ ha, hav⟩

variable {N : ℕ} (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a))
include hA

theorem walk_rank {v : V} : ∀ (l : List A) (u : V), IsWalk tail head u v l →
    rank u ≤ rank v ∧ ∀ a ∈ l, rank u ≤ rank (tail a) ∧ rank (head a) ≤ rank v := by
  intro l
  induction l with
  | nil =>
      intro u hw
      exact ⟨le_of_eq (congrArg rank hw), fun a ha => by cases ha⟩
  | cons a0 l' ih =>
      intro u hw
      obtain ⟨h0, hw'⟩ := hw
      obtain ⟨h1, h2⟩ := ih (head a0) hw'
      have hlt := hA a0
      rw [h0] at hlt
      refine ⟨(le_of_lt hlt).trans h1, ?_⟩
      intro a ha
      rcases List.mem_cons.1 ha with heq | ha'
      · rw [heq, h0]
        exact ⟨le_refl _, h1⟩
      · exact ⟨(le_of_lt hlt).trans (h2 a ha').1, (h2 a ha').2⟩

theorem walk_tail_inj {v : V} : ∀ (l : List A) (u : V), IsWalk tail head u v l →
    ∀ a ∈ l, ∀ b ∈ l, tail a = tail b → a = b := by
  intro l
  induction l with
  | nil =>
      intro u _ a ha
      cases ha
  | cons a0 l' ih =>
      intro u hw a ha b hb hab
      obtain ⟨_, hw'⟩ := hw
      have hr := (walk_rank tail head rank hA l' (head a0) hw').2
      have key : ∀ c ∈ l', tail a0 ≠ tail c := by
        intro c hc h
        have h1 := (hr c hc).1
        have h2 := hA a0
        rw [h] at h2
        exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)
      rcases List.mem_cons.1 ha with ha0 | ha' <;> rcases List.mem_cons.1 hb with hb0 | hb'
      · rw [ha0, hb0]
      · rw [ha0] at hab
        exact absurd hab (key b hb')
      · rw [hb0] at hab
        exact absurd hab.symm (key a ha')
      · exact ih (head a0) hw' a ha' b hb' hab

theorem walk_head_inj {v : V} : ∀ (l : List A) (u : V), IsWalk tail head u v l →
    ∀ a ∈ l, ∀ b ∈ l, head a = head b → a = b := by
  intro l
  induction l with
  | nil =>
      intro u _ a ha
      cases ha
  | cons a0 l' ih =>
      intro u hw a ha b hb hab
      obtain ⟨_, hw'⟩ := hw
      have hr := (walk_rank tail head rank hA l' (head a0) hw').2
      have key : ∀ c ∈ l', head a0 ≠ head c := by
        intro c hc h
        have h1 := (hr c hc).1
        have h2 := hA c
        rw [← h] at h2
        exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
      rcases List.mem_cons.1 ha with ha0 | ha' <;> rcases List.mem_cons.1 hb with hb0 | hb'
      · rw [ha0, hb0]
      · rw [ha0] at hab
        exact absurd hab (key b hb')
      · rw [hb0] at hab
        exact absurd hab.symm (key a ha')
      · exact ih (head a0) hw' a ha' b hb' hab

theorem walk_tail_ne_end {u v : V} (l : List A) (hw : IsWalk tail head u v l) :
    ∀ a ∈ l, tail a ≠ v := by
  intro a ha h
  have h1 := ((walk_rank tail head rank hA l u hw).2 a ha).2
  have h2 := hA a
  rw [h] at h2
  exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)

theorem walk_head_ne_start {u v : V} (l : List A) (hw : IsWalk tail head u v l) :
    ∀ a ∈ l, head a ≠ u := by
  intro a ha h
  have h1 := ((walk_rank tail head rank hA l u hw).2 a ha).1
  have h2 := hA a
  rw [h] at h2
  exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

end Walks

/-! ### From a route to a path -/

/-- An edge that enters an original vertex is the exit edge of a chain. -/
theorem edge_into_original (tail head : A → V) (length : A → ℕ)
    {x y : Vertex V A length} (h : Edge tail head length x y) :
    ∀ w, y = Sum.inl w → ∃ a, x = internal length a (Fin.last (length a)) ∧ head a = w := by
  cases h with
  | entry a =>
      intro w hw
      cases hw
  | step a i =>
      intro w hw
      cases hw
  | exit a =>
      intro w hw
      exact ⟨a, rfl, Sum.inl.inj hw⟩

section Routes

variable (tail head : A → V) (length : A → ℕ) {s t : V} {σ : Equiv.Perm (Vertex V A length)}

theorem used_tail_inj {a b : A} (ha : Used tail length σ a) (hb : Used tail length σ b)
    (h : tail a = tail b) : a = b := by
  unfold Used at ha hb
  rw [h, hb] at ha
  exact (Sigma.mk.inj (Sum.inr.inj ha)).1.symm

theorem used_exit (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ) {a : A}
    (ha : Used tail length σ a) :
    σ (internal length a (Fin.last (length a))) = Sum.inl (head a) := by
  obtain ⟨i, hi⟩ := (chain_entry_iff_any_internal_moved tail head length hσ a).mp ha
  exact (whole_chain_forced tail head length hσ a i hi).2.2.1

theorem head_moved (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ) {a : A}
    (ha : Used tail length σ a) : σ (Sum.inl (head a)) ≠ Sum.inl (head a) := by
  intro hfix
  have h := used_exit tail head length hσ ha
  have hbad := σ.injective (h.trans hfix.symm)
  cases hbad

theorem out_arc_of_moved (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    {u : V} (hu : σ (Sum.inl u) ≠ Sum.inl u) (hut : u ≠ t) :
    ∃ a, tail a = u ∧ Used tail length σ a := by
  rcases hσ (Sum.inl u) with hfix | hedge | hret
  · exact absurd hfix hu
  · obtain ⟨a, hua, hy⟩ := edge_from_original tail head length hedge u rfl
    refine ⟨a, hua.symm, ?_⟩
    unfold Used
    rw [← hua]
    exact hy
  · exact absurd (Sum.inl.inj hret.1) hut

theorem in_arc_of_used (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    {b : A} (hb : Used tail length σ b) (hbs : tail b ≠ s) :
    ∃ a, Used tail length σ a ∧ head a = tail b := by
  have hx : σ (σ.symm (Sum.inl (tail b))) = Sum.inl (tail b) := σ.apply_symm_apply _
  rcases hσ (σ.symm (Sum.inl (tail b))) with hfix | hedge | hret
  · have hxe : σ.symm (Sum.inl (tail b)) = Sum.inl (tail b) := hfix.symm.trans hx
    rw [hxe] at hx
    unfold Used at hb
    rw [hb] at hx
    cases hx
  · rw [hx] at hedge
    obtain ⟨a, hxa, hab⟩ := edge_into_original tail head length hedge (tail b) rfl
    refine ⟨a, ?_, hab⟩
    apply (chain_entry_iff_any_internal_moved tail head length hσ a).mpr
    refine ⟨Fin.last (length a), ?_⟩
    rw [← hxa, hx]
    intro h
    rw [hxa] at h
    cases h
  · have h : (Sum.inl s : Vertex V A length) = Sum.inl (tail b) := hret.2.symm.trans hx
    exact absurd (Sum.inl.inj h).symm hbs

variable {N : ℕ} (rank : V → Fin N) (hA : ∀ a, rank (tail a) < rank (head a))
include hA

theorem exists_walk_of_designated
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ) :
    ∀ (k : ℕ) (u : V), N - (rank u).val = k →
      (u = t ∨ ∃ a, tail a = u ∧ Used tail length σ a) →
      ∃ l, IsWalk tail head u t l ∧ ∀ a ∈ l, Used tail length σ a := by
  intro k
  induction' k using Nat.strong_induction_on with k ih
  intro u hk hu
  by_cases hut : u = t
  · exact ⟨[], hut, fun a ha => by cases ha⟩
  · obtain ⟨a, hau, haU⟩ := hu.resolve_left hut
    have hlt := hA a
    rw [hau] at hlt
    have hnext : head a = t ∨ ∃ b, tail b = head a ∧ Used tail length σ b := by
      by_cases h : head a = t
      · exact Or.inl h
      · exact Or.inr (out_arc_of_moved tail head length hσ (head_moved tail head length hσ haU) h)
    have hmeas : N - (rank (head a)).val < k := by
      have h1 := (rank (head a)).isLt
      have h2 := Fin.lt_def.1 hlt
      omega
    obtain ⟨l, hl, hlU⟩ := ih _ hmeas (head a) rfl hnext
    refine ⟨a :: l, ⟨hau, hl⟩, ?_⟩
    intro b hb
    rcases List.mem_cons.1 hb with h | h
    · rw [h]
      exact haU
    · exact hlU b h

/-- **From a route to a path.**  A designated permutation that selects the return entry
determines a path from `s` to `t` in the original graph whose arcs are exactly the used arcs. -/
theorem walk_of_designated (hst : s ≠ t)
    (hσ : Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ)
    (hret : σ (Sum.inl t) = Sum.inl s) :
    ∃ l, IsWalk tail head s t l ∧ ∀ a, a ∈ l ↔ Used tail length σ a := by
  have hs : σ (Sum.inl s) ≠ Sum.inl s := by
    intro h
    exact hst (Sum.inl.inj (σ.injective (h.trans hret.symm)))
  obtain ⟨l, hl, hlU⟩ := exists_walk_of_designated tail head length rank hA hσ _ s rfl
    (Or.inr (out_arc_of_moved tail head length hσ hs hst))
  refine ⟨l, hl, fun a => ⟨hlU a, ?_⟩⟩
  have key : ∀ (k : ℕ) (b : A), (rank (tail b)).val = k → Used tail length σ b → b ∈ l := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    intro b hk hb
    by_cases hbs : tail b = s
    · obtain ⟨a, hal, has⟩ := walk_first tail head l hl hst
      have hab : a = b := used_tail_inj tail length (hlU a hal) hb (has.trans hbs.symm)
      rw [← hab]
      exact hal
    · obtain ⟨a, haU, hab⟩ := in_arc_of_used tail head length hσ hb hbs
      have hlt := hA a
      rw [hab] at hlt
      have hal : a ∈ l := ih _ (by rw [← hk]; exact Fin.lt_def.1 hlt) a rfl haU
      rcases walk_next tail head l s hl a hal with hend | ⟨c, hcl, hc⟩
      · exfalso
        unfold Used at hb
        rw [← hab, hend, hret] at hb
        cases hb
      · have hcb : c = b := used_tail_inj tail length (hlU c hcl) hb (hc.trans hab)
        rw [← hcb]
        exact hcl
  exact key _ a rfl

end Routes

/-! ### From a path to a route -/

theorem chainNext_castSucc (head : A → V) (length : A → ℕ) (a : A) (j : Fin (length a)) :
    chainNext head length a j.castSucc = internal length a j.succ := by
  simp [chainNext, j.isLt, internal, Fin.ext_iff]

theorem chainNext_last (head : A → V) (length : A → ℕ) (a : A) :
    chainNext head length a (Fin.last (length a)) = Sum.inl (head a) := by
  simp [chainNext]

theorem chainPrev_zero (tail : A → V) (length : A → ℕ) (a : A) :
    chainPrev tail length a 0 = Sum.inl (tail a) := by
  simp [chainPrev]

theorem chainPrev_succ (tail : A → V) (length : A → ℕ) (a : A) (j : Fin (length a)) :
    chainPrev tail length a j.succ = internal length a j.castSucc := by
  simp [chainPrev, internal, Fin.ext_iff]

section FromWalk

variable [DecidableEq V] [DecidableEq A]

/-- The first arc `a` of `l` with `f a = v`, if any. -/
def findArc (f : A → V) (l : List A) (v : V) : Option A :=
  l.find? (fun a => decide (f a = v))

omit [DecidableEq A] in
theorem findArc_some {f : A → V} {l : List A} {v : V} {a : A} (h : findArc f l v = some a) :
    a ∈ l ∧ f a = v := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have h' := List.find?_some h
  simpa using h'

omit [DecidableEq A] in
theorem findArc_none {f : A → V} {l : List A} {v : V} (h : findArc f l v = none) :
    ∀ a ∈ l, f a ≠ v := by
  intro a ha
  have h' := List.find?_eq_none.1 h a ha
  simpa using h'

omit [DecidableEq A] in
theorem findArc_of_mem {f : A → V} {l : List A}
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) {a : A} (ha : a ∈ l) :
    findArc f l (f a) = some a := by
  cases h : findArc f l (f a) with
  | none => exact absurd rfl (findArc_none h a ha)
  | some b =>
      obtain ⟨hb, hbt⟩ := findArc_some h
      rw [hinj b hb a ha hbt]

/-- The facts about a path that the construction uses. -/
structure WalkFacts (tail head : A → V) (s t : V) (l : List A) : Prop where
  tail_inj : ∀ a ∈ l, ∀ b ∈ l, tail a = tail b → a = b
  head_inj : ∀ a ∈ l, ∀ b ∈ l, head a = head b → a = b
  tail_ne_t : ∀ a ∈ l, tail a ≠ t
  head_ne_s : ∀ a ∈ l, head a ≠ s
  next : ∀ a ∈ l, head a = t ∨ ∃ c ∈ l, tail c = head a
  prev : ∀ a ∈ l, tail a = s ∨ ∃ c ∈ l, head c = tail a
  first : ∃ a ∈ l, tail a = s
  last : ∃ a ∈ l, head a = t

omit [DecidableEq V] [DecidableEq A] in
theorem walkFacts {tail head : A → V} {s t : V} {l : List A} {N : ℕ} (rank : V → Fin N)
    (hA : ∀ a, rank (tail a) < rank (head a)) (hst : s ≠ t) (W : IsWalk tail head s t l) :
    WalkFacts tail head s t l where
  tail_inj := walk_tail_inj tail head rank hA l s W
  head_inj := walk_head_inj tail head rank hA l s W
  tail_ne_t := walk_tail_ne_end tail head rank hA l W
  head_ne_s := walk_head_ne_start tail head rank hA l W
  next := walk_next tail head l s W
  prev := walk_prev tail head l s W
  first := walk_first tail head l W hst
  last := walk_last tail head l s W hst

variable (tail head : A → V) (length : A → ℕ) (s t : V) (l : List A)

/-- The permutation of a path: follow the chains of the arcs of `l`, return from `t` to `s`,
fix everything else. -/
def walkFun : Vertex V A length → Vertex V A length
  | Sum.inl v =>
      match findArc tail l v with
      | some a => internal length a 0
      | none => if v = t then Sum.inl s else Sum.inl v
  | Sum.inr ⟨a, i⟩ => if a ∈ l then chainNext head length a i else Sum.inr ⟨a, i⟩

/-- The inverse map. -/
def walkInv : Vertex V A length → Vertex V A length
  | Sum.inl v =>
      match findArc head l v with
      | some a => internal length a (Fin.last (length a))
      | none => if v = s then Sum.inl t else Sum.inl v
  | Sum.inr ⟨a, i⟩ => if a ∈ l then chainPrev tail length a i else Sum.inr ⟨a, i⟩

section Eval

variable {tail head length s t l}

theorem walkFun_inl_some {v : V} {a : A} (h : findArc tail l v = some a) :
    walkFun tail head length s t l (Sum.inl v) = internal length a 0 := by
  simp only [walkFun, h]

theorem walkFun_inl_none {v : V} (h : findArc tail l v = none) :
    walkFun tail head length s t l (Sum.inl v) = if v = t then Sum.inl s else Sum.inl v := by
  simp only [walkFun, h]

theorem walkFun_internal_mem {a : A} (i : Fin (length a + 1)) (h : a ∈ l) :
    walkFun tail head length s t l (internal length a i) = chainNext head length a i := by
  show (if a ∈ l then chainNext head length a i else Sum.inr ⟨a, i⟩) = _
  rw [if_pos h]

theorem walkFun_internal_not_mem {a : A} (i : Fin (length a + 1)) (h : a ∉ l) :
    walkFun tail head length s t l (internal length a i) = internal length a i := by
  show (if a ∈ l then chainNext head length a i else Sum.inr ⟨a, i⟩) = _
  rw [if_neg h]
  rfl

theorem walkInv_inl_some {v : V} {a : A} (h : findArc head l v = some a) :
    walkInv tail head length s t l (Sum.inl v) = internal length a (Fin.last (length a)) := by
  simp only [walkInv, h]

theorem walkInv_inl_none {v : V} (h : findArc head l v = none) :
    walkInv tail head length s t l (Sum.inl v) = if v = s then Sum.inl t else Sum.inl v := by
  simp only [walkInv, h]

theorem walkInv_internal_mem {a : A} (i : Fin (length a + 1)) (h : a ∈ l) :
    walkInv tail head length s t l (internal length a i) = chainPrev tail length a i := by
  show (if a ∈ l then chainPrev tail length a i else Sum.inr ⟨a, i⟩) = _
  rw [if_pos h]

theorem walkInv_internal_not_mem {a : A} (i : Fin (length a + 1)) (h : a ∉ l) :
    walkInv tail head length s t l (internal length a i) = internal length a i := by
  show (if a ∈ l then chainPrev tail length a i else Sum.inr ⟨a, i⟩) = _
  rw [if_neg h]
  rfl

omit [DecidableEq A] in
theorem findArc_tail_t (F : WalkFacts tail head s t l) : findArc tail l t = none := by
  cases h : findArc tail l t with
  | none => rfl
  | some b => exact absurd (findArc_some h).2 (F.tail_ne_t b (findArc_some h).1)

omit [DecidableEq A] in
theorem findArc_head_s (F : WalkFacts tail head s t l) : findArc head l s = none := by
  cases h : findArc head l s with
  | none => rfl
  | some b => exact absurd (findArc_some h).2 (F.head_ne_s b (findArc_some h).1)

theorem walkInv_walkFun (F : WalkFacts tail head s t l) (x : Vertex V A length) :
    walkInv tail head length s t l (walkFun tail head length s t l x) = x := by
  rcases x with v | ⟨a, i⟩
  · cases h : findArc tail l v with
    | some a =>
        obtain ⟨hal, hav⟩ := findArc_some h
        rw [walkFun_inl_some h, walkInv_internal_mem _ hal, chainPrev_zero, hav]
    | none =>
        rw [walkFun_inl_none h]
        by_cases hvt : v = t
        · rw [if_pos hvt, walkInv_inl_none (findArc_head_s F), if_pos rfl, hvt]
        · have hn : findArc head l v = none := by
            cases h' : findArc head l v with
            | none => rfl
            | some b =>
                obtain ⟨hbl, hbv⟩ := findArc_some h'
                rcases F.next b hbl with hend | ⟨c, hcl, hc⟩
                · exact absurd (hbv.symm.trans hend) hvt
                · exact absurd (hc.trans hbv) (findArc_none h c hcl)
          have hvs : v ≠ s := by
            intro hvs
            obtain ⟨a, hal, has⟩ := F.first
            exact findArc_none h a hal (has.trans hvs.symm)
          rw [if_neg hvt, walkInv_inl_none hn, if_neg hvs]
  · show walkInv tail head length s t l (walkFun tail head length s t l (internal length a i))
      = internal length a i
    by_cases hal : a ∈ l
    · by_cases hi : i.val < length a
      · obtain ⟨j, rfl⟩ : ∃ j : Fin (length a), i = j.castSucc := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
        rw [walkFun_internal_mem _ hal, chainNext_castSucc, walkInv_internal_mem _ hal,
          chainPrev_succ]
      · have hil : i = Fin.last (length a) :=
          Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
        rw [hil, walkFun_internal_mem _ hal, chainNext_last,
          walkInv_inl_some (findArc_of_mem F.head_inj hal)]
    · rw [walkFun_internal_not_mem _ hal, walkInv_internal_not_mem _ hal]

theorem walkFun_walkInv (F : WalkFacts tail head s t l) (x : Vertex V A length) :
    walkFun tail head length s t l (walkInv tail head length s t l x) = x := by
  rcases x with v | ⟨a, i⟩
  · cases h : findArc head l v with
    | some a =>
        obtain ⟨hal, hav⟩ := findArc_some h
        rw [walkInv_inl_some h, walkFun_internal_mem _ hal, chainNext_last, hav]
    | none =>
        rw [walkInv_inl_none h]
        by_cases hvs : v = s
        · rw [if_pos hvs, walkFun_inl_none (findArc_tail_t F), if_pos rfl, hvs]
        · have hn : findArc tail l v = none := by
            cases h' : findArc tail l v with
            | none => rfl
            | some b =>
                obtain ⟨hbl, hbv⟩ := findArc_some h'
                rcases F.prev b hbl with hstart | ⟨c, hcl, hc⟩
                · exact absurd (hbv.symm.trans hstart) hvs
                · exact absurd (hc.trans hbv) (findArc_none h c hcl)
          have hvt : v ≠ t := by
            intro hvt
            obtain ⟨a, hal, hat⟩ := F.last
            exact findArc_none h a hal (hat.trans hvt.symm)
          rw [if_neg hvs, walkFun_inl_none hn, if_neg hvt]
  · show walkFun tail head length s t l (walkInv tail head length s t l (internal length a i))
      = internal length a i
    by_cases hal : a ∈ l
    · by_cases hi : i.val = 0
      · have hi0 : i = 0 := Fin.ext hi
        rw [hi0, walkInv_internal_mem _ hal, chainPrev_zero,
          walkFun_inl_some (findArc_of_mem F.tail_inj hal)]
      · obtain ⟨j, rfl⟩ : ∃ j : Fin (length a), i = j.succ :=
          ⟨⟨i.val - 1, by have := i.isLt; omega⟩, Fin.ext (by
            show i.val = i.val - 1 + 1
            omega)⟩
        rw [walkInv_internal_mem _ hal, chainPrev_succ, walkFun_internal_mem _ hal,
          chainNext_castSucc]
    · rw [walkInv_internal_not_mem _ hal, walkFun_internal_not_mem _ hal]

end Eval

/-- **The permutation of a path of the original graph.** -/
def walkPerm (F : WalkFacts tail head s t l) : Equiv.Perm (Vertex V A length) where
  toFun := walkFun tail head length s t l
  invFun := walkInv tail head length s t l
  left_inv := walkInv_walkFun F
  right_inv := walkFun_walkInv F

/-- It selects the return entry. -/
theorem walkPerm_return (F : WalkFacts tail head s t l) :
    walkPerm tail head length s t l F (Sum.inl t) = Sum.inl s := by
  show walkFun tail head length s t l (Sum.inl t) = Sum.inl s
  rw [walkFun_inl_none (findArc_tail_t F), if_pos rfl]

/-- It is designated: it uses only chain edges and the return entry. -/
theorem walkPerm_designated (F : WalkFacts tail head s t l) :
    Designated (Edge tail head length) (Sum.inl s) (Sum.inl t)
      (walkPerm tail head length s t l F) := by
  intro x
  show walkFun tail head length s t l x = x
    ∨ Edge tail head length x (walkFun tail head length s t l x)
    ∨ (x = Sum.inl t ∧ walkFun tail head length s t l x = Sum.inl s)
  rcases x with v | ⟨a, i⟩
  · cases h : findArc tail l v with
    | some a =>
        obtain ⟨_, hav⟩ := findArc_some h
        right; left
        rw [walkFun_inl_some h, ← hav]
        exact Edge.entry a
    | none =>
        rw [walkFun_inl_none h]
        by_cases hvt : v = t
        · right; right
          rw [if_pos hvt, hvt]
          exact ⟨rfl, rfl⟩
        · left
          rw [if_neg hvt]
  · show walkFun tail head length s t l (internal length a i) = internal length a i
      ∨ Edge tail head length (internal length a i)
          (walkFun tail head length s t l (internal length a i))
      ∨ (internal length a i = Sum.inl t
          ∧ walkFun tail head length s t l (internal length a i) = Sum.inl s)
    by_cases hal : a ∈ l
    · right; left
      by_cases hi : i.val < length a
      · obtain ⟨j, rfl⟩ : ∃ j : Fin (length a), i = j.castSucc := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
        rw [walkFun_internal_mem _ hal, chainNext_castSucc]
        exact Edge.step a j
      · have hil : i = Fin.last (length a) :=
          Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
        rw [hil, walkFun_internal_mem _ hal, chainNext_last]
        exact Edge.exit a
    · left
      exact walkFun_internal_not_mem _ hal

/-- It uses exactly the arcs of the path. -/
theorem walkPerm_used (F : WalkFacts tail head s t l) (a : A) :
    Used tail length (walkPerm tail head length s t l F) a ↔ a ∈ l := by
  unfold Used
  show walkFun tail head length s t l (Sum.inl (tail a)) = internal length a 0 ↔ a ∈ l
  constructor
  · intro h
    cases hf : findArc tail l (tail a) with
    | some b =>
        rw [walkFun_inl_some hf] at h
        have hba : b = a := (Sigma.mk.inj (Sum.inr.inj h)).1
        rw [← hba]
        exact (findArc_some hf).1
    | none =>
        rw [walkFun_inl_none hf] at h
        split_ifs at h <;> cases h
  · intro ha
    rw [walkFun_inl_some (findArc_of_mem F.tail_inj ha)]

/-- **From a path to a route.**  Every path from `s` to `t` in the original (acyclic) graph is
the set of used arcs of a designated permutation that selects the return entry. -/
theorem exists_designated_of_walk {N : ℕ} (rank : V → Fin N)
    (hA : ∀ a, rank (tail a) < rank (head a)) (hst : s ≠ t) (W : IsWalk tail head s t l) :
    ∃ σ : Equiv.Perm (Vertex V A length),
      Designated (Edge tail head length) (Sum.inl s) (Sum.inl t) σ ∧
      σ (Sum.inl t) = Sum.inl s ∧ ∀ a, Used tail length σ a ↔ a ∈ l :=
  ⟨walkPerm tail head length s t l (walkFacts rank hA hst W),
    walkPerm_designated tail head length s t l _,
    walkPerm_return tail head length s t l _,
    walkPerm_used tail head length s t l _⟩

end FromWalk

end Subdivision
end DagCycleAssignment
