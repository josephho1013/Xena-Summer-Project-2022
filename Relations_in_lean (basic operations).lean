import tactic

-- References: Schmidt, G. (2010) Relational Mathematics. Cambridge: Cambridge University Press (Encyclopedia of Mathematics and its Applications). doi: 10.1017/CBO9780511778810.

namespace myrelation
variables {α β γ : Type*}

-- Section 1: Common operations
def union (r : α → β → Prop) (s : α → β → Prop) (a : α) (b : β) : Prop := r a b ∨ s a b
def intersect (r : α → β → Prop) (s : α → β → Prop) (a : α) (b : β) : Prop := r a b ∧ s a b

/- Define transpose of binary relation r : α → β → Prop:
Transpose of R is the binary relation β → α → Prop such that for a ∈ α, b ∈ β, R_transpose b a ↔ R a b. -/
def transpose (r : α → β → Prop) (b : β) (a : α) : Prop := r a b
def comp (r : α → β → Prop) (p : β → γ → Prop) (a : α) (c : γ) : Prop := ∃ (b : β), r a b ∧ p b c -- same as definition of relation.comp in mathlib

def complement (r : α → β → Prop) (a : α) (b : β) : Prop := ¬(r a b)

variables {A B C : Type*}

namespace basics
-- Commutativity
lemma union_comm (r : A → B → Prop) (s : A → B → Prop) : union r s = union s r :=
begin
  ext a b, repeat {rw union}, rw or_comm,
end

lemma intersect_comm (r : A → B → Prop) (s : A → B → Prop) : intersect r s = intersect s r :=
begin
  ext a b, repeat {rw intersect}, rw and_comm,
end

-- Associativity
lemma union_assoc (r : A → B → Prop) (s : A → B → Prop) (t : A → B → Prop) : union (union r s) t = union r (union s t) :=
begin
  ext a b, repeat {rw union}, rw or_assoc,
end

lemma intersect_assoc (r : A → B → Prop) (s : A → B → Prop) (t : A → B → Prop) : intersect (intersect r s) t = intersect r (intersect s t) :=
begin
  ext a b, repeat {rw intersect}, rw and_assoc,
end

-- Distributivity
lemma union_intersect_distri (r : A → B → Prop) (s : A → B → Prop) (t : A → B → Prop) : union r (intersect s t) = intersect (union r s) (union r t) :=
begin
  ext a b,
  repeat {rw union at *},
  repeat {rw intersect at *},
  repeat {rw union at *},
  exact or_and_distrib_left,
end

lemma intersect_union_distri (r : A → B → Prop) (s : A → B → Prop) (t : A → B → Prop) : intersect r (union s t) = union (intersect r s) (intersect r t) :=
begin
  ext a b,
  repeat {rw intersect at *},
  repeat {rw union at *},
  repeat {rw intersect at *},
  exact and_or_distrib_left,
end

-- Absorption
lemma self_union (r : A → B → Prop) : union r r = r :=
begin
  ext a b,
  rw union,
  exact or_self (r a b),
end

lemma self_intersect (r : A → B → Prop) : intersect r r = r :=
begin
  ext a b,
  rw intersect,
  exact and_self (r a b),
end

lemma union_intersect_absorp (r : A → B → Prop) (s : A → B → Prop) : union r (intersect r s) = r :=
begin
  ext a b,
  split,
  { intro h,
    cases h with hr hrs,
    exact hr,
    cases hrs with hr hs,
    exact hr},
  { intro hr,
    left,
    exact hr},
end

lemma intersect_union_absorp (r : A → B → Prop) (s : A → B → Prop) : intersect r (union r s) = r :=
begin
  ext a b,
  split,
  { intro h,
    cases h with hr hrs,
    exact hr},
  { intro hr,
    split,
    exact hr,
    left, exact hr},
end

lemma transpose_transpose_self (r : A → B → Prop) : transpose (transpose r) = r :=
begin
  refl, --definitional equality
end

lemma complement_complement_self (r : A → B → Prop) : complement (complement r) = r :=
begin
  ext x y,
  split,
  { intro h,
    repeat {rw complement at h}, -- reduces to the simple logic lemma ¬(¬P) → P
    by_contra h1,
    apply h,
    exact h1,
  },
  { intro h,
    repeat {rw complement}, -- reduces to the simple logic lemma P → ¬(¬P)
    by_contra h1,
    apply h1,
    exact h,
    },
end

lemma transpose_complement_comm (r : A → B → Prop) : transpose (complement r) = complement (transpose r) :=
begin
  refl, --definitional equality
end

lemma transpose_union_comm (r : A → B → Prop) (s : A → B → Prop): transpose (union r s) = union (transpose r) (transpose s) :=
begin
  refl, --definitional equality
end

lemma transpose_intersect_comm (r : A → B → Prop) (s : A → B → Prop) : transpose (intersect r s) = intersect (transpose r) (transpose s) :=
begin
  refl, --definitional equality
end

lemma inclusion_transpose_iff (r : A → B → Prop) (s : A → B → Prop) (a : A) (b : B) : (r a b → s a b) ↔ (transpose r b a → transpose s b a) :=
begin
  refl, --definitional equality
end

end basics

end myrelation