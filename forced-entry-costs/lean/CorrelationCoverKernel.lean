import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
The known Kaibel--Weltge combinatorial cover bound, formalized here as a
ternary-word theorem. A letter is absent, in the first set, or in the second
set; hence every word represents a disjoint pair of sets.

Source: the induction in the proof of Theorem 1 of the corrected preprint
https://arxiv.org/pdf/1307.3543v6 (25 February 2016). We use a disjoint
partition refinement of the two-subfamily covering argument.

This is an attributed classical ingredient, not a new proof method. The
assignment adapter, polyhedral factorization theorem, and extension-complexity
transfer are separate written arguments and are not formalized in this file.
-/

set_option autoImplicit false

namespace SapioCorrelationCover

inductive Letter where
  | zero
  | a
  | b
  deriving DecidableEq

def Word : ℕ → Type
  | 0 => PUnit
  | n + 1 => Letter × Word n

instance wordDecidableEq : (n : ℕ) → DecidableEq (Word n)
  | 0 => by
    change DecidableEq PUnit
    infer_instance
  | n + 1 => by
    letI := wordDecidableEq n
    change DecidableEq (Letter × Word n)
    infer_instance

/-- Number of coordinates with A in the first word and B in the second. -/
def cross : (n : ℕ) → Word n → Word n → ℕ
  | 0, _, _ => 0
  | n + 1, x, y =>
    (if x.1 = Letter.a ∧ y.1 = Letter.b then 1 else 0) + cross n x.2 y.2

@[simp] theorem cross_self (n : ℕ) (x : Word n) : cross n x x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨head, tail⟩
    cases head <;> simp [cross, ih]

/-- No ordered pair in the family has cross-intersection size exactly one. -/
def Valid (n : ℕ) (R : Finset (Word n)) : Prop :=
  ∀ x ∈ R, ∀ y ∈ R, cross n x y ≠ 1

def chooseLeft {n : ℕ} (R : Finset (Word (n + 1))) (x : Word (n + 1)) : Prop :=
  x.1 = Letter.a ∨ (x.1 = Letter.zero ∧ (Letter.a, x.2) ∉ R)

instance chooseLeftDecidable {n : ℕ} (R : Finset (Word (n + 1))) :
    DecidablePred (chooseLeft R) := by
  intro x
  unfold chooseLeft
  infer_instance

theorem left_head_not_b {n : ℕ} {R : Finset (Word (n + 1))}
    {x : Word (n + 1)} (h : chooseLeft R x) : x.1 ≠ Letter.b := by
  rcases x with ⟨head, tail⟩
  cases head <;> simp_all [chooseLeft]

theorem right_head_not_a {n : ℕ} {R : Finset (Word (n + 1))}
    {x : Word (n + 1)} (h : ¬ chooseLeft R x) : x.1 ≠ Letter.a := by
  intro heq
  exact h (Or.inl heq)

theorem no_equal_tail_ab {n : ℕ} {R : Finset (Word (n + 1))}
    (hR : Valid (n + 1) R) (tail : Word n) :
    ¬ ((Letter.a, tail) ∈ R ∧ (Letter.b, tail) ∈ R) := by
  rintro ⟨ha, hb⟩
  have h := hR (Letter.a, tail) ha (Letter.b, tail) hb
  simp [cross] at h

theorem left_tail_injective {n : ℕ} (R : Finset (Word (n + 1))) :
    Set.InjOn Prod.snd (R.filter (chooseLeft R) : Set (Word (n + 1))) := by
  classical
  intro x hx y hy hxy
  rcases x with ⟨headx, tailx⟩
  rcases y with ⟨heady, taily⟩
  change tailx = taily at hxy
  subst taily
  have hxR := (Finset.mem_filter.mp hx).1
  have hyR := (Finset.mem_filter.mp hy).1
  have hxL := (Finset.mem_filter.mp hx).2
  have hyL := (Finset.mem_filter.mp hy).2
  cases headx <;> cases heady <;> simp_all [chooseLeft]

theorem right_tail_injective {n : ℕ} (R : Finset (Word (n + 1)))
    (hR : Valid (n + 1) R) :
    Set.InjOn Prod.snd (R.filter (fun x => ¬ chooseLeft R x) : Set (Word (n + 1))) := by
  classical
  intro x hx y hy hxy
  rcases x with ⟨headx, tailx⟩
  rcases y with ⟨heady, taily⟩
  change tailx = taily at hxy
  subst taily
  have hxR := (Finset.mem_filter.mp hx).1
  have hyR := (Finset.mem_filter.mp hy).1
  have hxL := (Finset.mem_filter.mp hx).2
  have hyL := (Finset.mem_filter.mp hy).2
  have hab := no_equal_tail_ab hR tailx
  cases headx <;> cases heady <;> simp_all [chooseLeft]

theorem left_tails_valid {n : ℕ} (R : Finset (Word (n + 1)))
    (hR : Valid (n + 1) R) :
    Valid n ((R.filter (chooseLeft R)).image Prod.snd) := by
  classical
  intro tx htx ty hty
  rcases Finset.mem_image.mp htx with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hty with ⟨y, hy, rfl⟩
  have hxy := hR x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
  have hyb := left_head_not_b (Finset.mem_filter.mp hy).2
  simpa [cross, hyb] using hxy

theorem right_tails_valid {n : ℕ} (R : Finset (Word (n + 1)))
    (hR : Valid (n + 1) R) :
    Valid n ((R.filter (fun x => ¬ chooseLeft R x)).image Prod.snd) := by
  classical
  intro tx htx ty hty
  rcases Finset.mem_image.mp htx with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hty with ⟨y, hy, rfl⟩
  have hxy := hR x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
  have hxa := right_head_not_a (Finset.mem_filter.mp hx).2
  simpa [cross, hxa] using hxy

/-- Kaibel--Weltge's valid-family cardinality bound in ternary-word form. -/
theorem valid_card_le (n : ℕ) (R : Finset (Word n)) (hR : Valid n R) :
    R.card ≤ 2 ^ n := by
  classical
  induction n with
  | zero =>
    have hsub : R ⊆ ({PUnit.unit} : Finset (Word 0)) := by
      intro x _
      cases x
      simp
    simpa using Finset.card_le_card hsub
  | succ n ih =>
    let L := R.filter (chooseLeft R)
    let S := R.filter (fun x => ¬ chooseLeft R x)
    have hL : L.card ≤ 2 ^ n := by
      have hb := ih (L.image Prod.snd) (left_tails_valid R hR)
      have hc : (L.image Prod.snd).card = L.card :=
        Finset.card_image_of_injOn (left_tail_injective R)
      omega
    have hS : S.card ≤ 2 ^ n := by
      have hb := ih (S.image Prod.snd) (right_tails_valid R hR)
      have hc : (S.image Prod.snd).card = S.card :=
        Finset.card_image_of_injOn (right_tail_injective R hR)
      omega
    have hsum : L.card + S.card = R.card :=
      Finset.filter_card_add_filter_neg_card_eq_card (chooseLeft R)
    rw [Nat.pow_succ]
    omega

def allWords : (n : ℕ) → Finset (Word n)
  | 0 => {PUnit.unit}
  | n + 1 =>
      (allWords n).image (fun tail => (Letter.zero, tail)) ∪
      (allWords n).image (fun tail => (Letter.a, tail)) ∪
      (allWords n).image (fun tail => (Letter.b, tail))

theorem mem_allWords (n : ℕ) (x : Word n) : x ∈ allWords n := by
  induction n with
  | zero => cases x; simp [allWords]
  | succ n ih =>
    rcases x with ⟨head, tail⟩
    cases head <;> simp [allWords, ih]

theorem tagged_image_card {n : ℕ} (R : Finset (Word n)) (head : Letter) :
    (R.image (fun tail => (head, tail))).card = R.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  exact (Prod.mk.inj hxy).2

theorem tagged_images_disjoint {n : ℕ} (R : Finset (Word n))
    {head₁ head₂ : Letter} (hne : head₁ ≠ head₂) :
    Disjoint (R.image (fun tail => (head₁, tail)))
      (R.image (fun tail => (head₂, tail))) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_image.mp hx with ⟨tx, _, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨ty, _, hxy⟩
  exact hne (congrArg Prod.fst hxy).symm

theorem allWords_card (n : ℕ) : (allWords n).card = 3 ^ n := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    have h0a := tagged_images_disjoint (allWords n)
      (show Letter.zero ≠ Letter.a by decide)
    have h0b := tagged_images_disjoint (allWords n)
      (show Letter.zero ≠ Letter.b by decide)
    have hab := tagged_images_disjoint (allWords n)
      (show Letter.a ≠ Letter.b by decide)
    have hu := Finset.disjoint_union_left.mpr ⟨h0b, hab⟩
    rw [allWords, Finset.card_union_of_disjoint hu,
      Finset.card_union_of_disjoint h0a]
    rw [tagged_image_card, tagged_image_card, tagged_image_card, ih, Nat.pow_succ]
    omega

def coverUnion {n : ℕ} : List (Finset (Word n)) → Finset (Word n)
  | [] => ∅
  | R :: rest => R ∪ coverUnion rest

theorem mem_coverUnion_of_mem {n : ℕ} {R : Finset (Word n)} {x : Word n}
    (L : List (Finset (Word n))) (hR : R ∈ L) (hx : x ∈ R) : x ∈ coverUnion L := by
  induction L with
  | nil => simp at hR
  | cons T rest ih =>
    simp only [List.mem_cons] at hR
    rcases hR with rfl | hR
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (ih hR)

theorem coverUnion_card_le (n : ℕ) (L : List (Finset (Word n)))
    (hvalid : ∀ R ∈ L, Valid n R) :
    (coverUnion L).card ≤ L.length * 2 ^ n := by
  induction L with
  | nil => simp [coverUnion]
  | cons R rest ih =>
    have hR := valid_card_le n R (hvalid R (by simp))
    have hrest : ∀ T ∈ rest, Valid n T := by
      intro T hT
      exact hvalid T (by simp [hT])
    have hb := ih hrest
    have hu := Finset.card_union_le R (coverUnion rest)
    simp only [coverUnion, List.length_cons, Nat.succ_mul]
    omega

/-- Every finite list of valid families covering all words satisfies the
classical exponential cover inequality. The list length counts repetitions. -/
theorem covering_inequality (n : ℕ) (L : List (Finset (Word n)))
    (hvalid : ∀ R ∈ L, Valid n R)
    (hcover : ∀ x : Word n, ∃ R ∈ L, x ∈ R) :
    3 ^ n ≤ L.length * 2 ^ n := by
  have hsub : allWords n ⊆ coverUnion L := by
    intro x _
    rcases hcover x with ⟨R, hR, hx⟩
    exact mem_coverUnion_of_mem L hR hx
  calc
    3 ^ n = (allWords n).card := (allWords_card n).symm
    _ ≤ (coverUnion L).card := Finset.card_le_card hsub
    _ ≤ L.length * 2 ^ n := coverUnion_card_le n L hvalid

end SapioCorrelationCover

#print axioms SapioCorrelationCover.cross_self
#print axioms SapioCorrelationCover.valid_card_le
#print axioms SapioCorrelationCover.allWords_card
#print axioms SapioCorrelationCover.covering_inequality
