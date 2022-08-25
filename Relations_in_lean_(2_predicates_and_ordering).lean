import tactic

-- References: Schmidt, G. (2010) Relational Mathematics. Cambridge: Cambridge University Press (Encyclopedia of Mathematics and its Applications). doi: 10.1017/CBO9780511778810.

namespace myrelation
variables {α β γ : Type*}

def union (r : α → β → Prop) (s : α → β → Prop) (a : α) (b : β) : Prop := r a b ∨ s a b
def intersect (r : α → β → Prop) (s : α → β → Prop) (a : α) (b : β) : Prop := r a b ∧ s a b
def transpose (r : α → β → Prop) (b : β) (a : α) : Prop := r a b
def complement (r : α → β → Prop) (a : α) (b : β) : Prop := ¬(r a b)
def comp (r : α → β → Prop) (p : β → γ → Prop) (a : α) (c : γ) : Prop := ∃ (b : β), r a b ∧ p b c

variables {A B C : Type*}

-- Section 2: Common predicates on binary relations on the SAME set
def reflexive (R : A → A → Prop) : Prop := ∀ x, R x x

def irreflexive (R : A → A → Prop) : Prop := ∀ x, ¬ R x x

def symmetric (R : A → A → Prop) : Prop := ∀ x y, R x y → R y x

def asymmetric (R : A → A → Prop) : Prop := ∀ (a b : A), R a b → ¬(R b a)

def transitive (R : A → A → Prop) : Prop := ∀ x y z, R x y → R y z → R x z

def anti_symmetric (R : A → A → Prop) : Prop := ∀ x y, R x y → R y x → x = y

example (R : A → A → Prop) (h : reflexive R) (x : A) : R x x := h x

example (R : A → A → Prop) (h : symmetric R) (x y : A) (h1 : R x y) : R y x := h x y h1

example (R : A → A → Prop) (h : transitive R) (x y z : A) (h1 : R x y) (h2 : R y z) : R x z := h x y z h1 h2

example (R : A → A → Prop) (h : anti_symmetric R) (x y : A) (h1 : R x y) (h2 : R y x) :
  x = y := h x y h1 h2

-- Preorder is a binary relation that is reflexive and transitive
def preorder (R : A → A → Prop) : Prop := reflexive R ∧ transitive R

-- Exercise 5.3.2 (GS)
example (R : A → A → Prop) : (∀ x y : A, R x y → x = y) → symmetric R :=
begin
  intros h x y hRxy,
  specialize h x y,
  have h1 : x = y, apply h, exact hRxy,
  rw h1 at *,
  exact hRxy,
end

-- Section 3: Orderings
def total (R : A → A → Prop) : Prop := ∀ x y, R x y ∨ R y x

def partial_order (R : A → A → Prop) : Prop := preorder R ∧ anti_symmetric R

def total_order (R : A → A → Prop) : Prop := partial_order R ∧ total R

def strict_order (R : A → A → Prop) : Prop := transitive R ∧ asymmetric R

lemma strict_order_iff_trans_irrefl (R : A → A → Prop) : strict_order R ↔ transitive R ∧ irreflexive R :=
begin
  split,
  { intro h,
    cases h with transR asymmR,
    split,
    exact transR,
    intros x hRxx,
    apply asymmR x x,
    exact hRxx,
    exact hRxx},
  { intro h,
    cases h with transR irrflR,
    split,
    exact transR,
    intros a b hRab hRba,
    apply irrflR a,
    apply transR a b a hRab hRba},
end

-- Exercise 14.4 Q1 (create partial order R' out of a strict partial order R)
example (R : A → A → Prop) : strict_order R → partial_order (λ a b : A, (R a b ∨ a = b)) :=
begin
  intro h,
  cases h with transR asymmR,
  split,
  split,
  -- prove reflexivity
  { intro a,
    right,
    refl},
  -- prove transitivity
  { intros a b c h1 h2,
    cases h1 with hRab hab,
    cases h2 with hRbc hbc,
    { left, apply transR a b c hRab hRbc},
    { rw ← hbc, left, exact hRab},

    cases h2 with hRbc hbc,
    { rw hab, left, exact hRbc},
    { right, rw hab, exact hbc},
    },
  -- prove anti-symmetry
  { intros a b h1 h2,
    cases h1 with hRab hab,
    cases h2 with hRba hba,
    { exfalso, apply asymmR a b hRab, exact hRba},
    { rw hba},

    exact hab,
    },
end

-- Exercise 5.3.3 (GS)
-- A property of a preorder relation (i.e. reflexive & transitive)
example (R : A → A → Prop) (E : A → A → Prop) : preorder E → comp (transpose E) (complement (comp E R)) = complement (comp E R) :=
begin
  intro h,
  cases h with reflE transE,
  ext a b,
  split,
  { intros h1 h2,
    cases h1 with c hc,
    cases h2 with d hd,
    cases hc with hEca hc,
    apply hc,
    use d, -- d is the required intermediate element
    split,
    apply transE c a d hEca hd.1,
    exact hd.2},
  { intro h,
    use a, -- a is the required intermediate element
    split,
    apply reflE a,
    exact h},
end

end myrelation
