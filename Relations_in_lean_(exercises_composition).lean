import tactic

-- References: Schmidt, G. (2010) Relational Mathematics. Cambridge: Cambridge University Press (Encyclopedia of Mathematics and its Applications). doi: 10.1017/CBO9780511778810.

namespace myrelation
variables {α β γ A B C: Type*}

def union (r : α → β → Prop) (s : α → β → Prop) (a : α) (b : β) : Prop := r a b ∨ s a b
def intersect (r : α → β → Prop) (s : α → β → Prop) (a : α) (b : β) : Prop := r a b ∧ s a b
def transpose (r : α → β → Prop) (b : β) (a : α) : Prop := r a b
def complement (r : α → β → Prop) (a : α) (b : β) : Prop := ¬(r a b)
def comp (r : α → β → Prop) (p : β → γ → Prop) (a : α) (c : γ) : Prop := ∃ (b : β), r a b ∧ p b c

def reflexive (R : A → A → Prop) : Prop := ∀ x, R x x
def irreflexive (R : A → A → Prop) : Prop := ∀ x, ¬ R x x
def symmetric (R : A → A → Prop) : Prop := ∀ x y, R x y → R y x
def asymmetric (R : A → A → Prop) : Prop := ∀ (a b : A), R a b → ¬(R b a)
def transitive (R : A → A → Prop) : Prop := ∀ x y z, R x y → R y z → R x z
def anti_symmetric (R : A → A → Prop) : Prop := ∀ x y, R x y → R y x → x = y

def preorder (R : A → A → Prop) : Prop := reflexive R ∧ transitive R
def total (R : A → A → Prop) : Prop := ∀ x y, R x y ∨ R y x
def partial_order (R : A → A → Prop) : Prop := preorder R ∧ anti_symmetric R
def total_order (R : A → A → Prop) : Prop := partial_order R ∧ total R
def strict_order (R : A → A → Prop) : Prop := transitive R ∧ asymmetric R

-- Miscellaneous problems related to composition

-- For relations (R S : A → A → Prop), 
-- (1)  if R and S are reflexive, is R ∘ S reflexive?
-- (2)  if R and S are symmetric, is R ∘ S symmetric?
-- (3)  if R and S are transitive, is R ∘ S transitive?
-- (4)  if R and S are anti-symmetric, is R ∘ S anti-symmetric?
-- (5)  if R and S are asymmetric, is R ∘ S asymmetric?
-- (6)  if R and S are irreflexive, is R ∘ S irreflexive?
-- (7)  if R and S are total, is R ∘ S total?

-- (1) Reflexivity: Preserved under composition
example (R S : A → A → Prop) (reflR : reflexive R) (reflS : reflexive S) : reflexive (comp R S) :=
begin
  intro x,
  use x, -- x is the required intermediate element
  split,
  { apply reflR x}, -- show R x x true, followed from reflexivity of R
  { apply reflS x}, -- show S x x true, followed from reflexivity of S
end

-- (2) Symmetry: Not preserved under composition
-- Counterexample: R, S are relations that
                -- R(a,b), R(b,a) true, else false
                -- S(a,a) true, else false

namespace symmetry

inductive X : Type
| a : X
| b : X

namespace X

-- Define binary relation R such that 
-- R(a,b), R(b,a) true, else false
def R : X → X → Prop
| a a := false
| a b := true
| b a := true
| b b := false

-- Define binary relation S such that 
-- S(a,a) true, else false
def S : X → X → Prop
| a a := true
| a b := false
| b a := false
| b b := false

def U : X → X → Prop := comp R S

-- R is symmetric
lemma R_symm : symmetric R :=
begin
  intros x y hxy,
  rcases x,
    -- x = a
    rcases y,
      exact hxy, -- the case y = a
      triv, -- the case y = b; `R b a` is true
    -- x = b
    rcases y,
      triv, -- the case y = a; `R a b` is true
      exact hxy, -- the case y = b
end

-- S is symmetric
lemma S_symm : symmetric S :=
begin
  intros x y hxy,
  rcases x,
    -- x = a
    rcases y,
      exact hxy, -- the case y = a
      exfalso, exact hxy, -- the case y = b
    -- x = b
    rcases y,
      exfalso, exact hxy, -- the case y = a
      exact hxy, -- the case y = b
end

-- U is NOT symmetric
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), symmetric R → symmetric S → symmetric U) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { exact R_symm}, -- Prove R is symmetric
  { have h1 : symmetric U, {apply h, exact S_symm},
    have h2 : U b a, -- show hypothesis that U b a is true
      {use a, split, triv, triv},
    have h3 : ¬(U a b), -- show hypothesis that U a b is false
      {intro hUab, cases hUab with x hx, rcases x, apply hx.2, apply hx.2},
    specialize h1 b a h2, -- focus on the specific case with h1, h2
    apply h3, exact h1,
  },
end

end X
end symmetry

-- (3) Transitivity: Not preserved under composition
-- Counterexample: R, S are relations that
                -- R(a,b), R(b,c), R(c,a) true, else false
                -- S(a,a) true, else false

namespace transitivity

inductive X : Type
| a : X
| b : X
| c : X

namespace X

-- Define binary relation R such that 
-- R(a,b), R(b,c), R(c,a) true, else false
def R : X → X → Prop
| a b := true
| b c := true
| a c := true
| a a := false
| b a := false
| b b := false
| c a := false
| c b := false
| c c := false

-- Define binary relation S such that 
-- S(b,c), S(c,a), S(b,a) true, else false
def S : X → X → Prop
| b c := true
| c a := true
| b a := true
| a a := false
| a b := false
| a c := false
| b b := false
| c b := false
| c c := false

def U : X → X → Prop := comp R S

-- R is transitive
lemma R_trans : transitive R :=
begin
  intros x y z hxy hyz,
  rcases x,
    -- x = a
    rcases y,
      -- y = a
      rcases z,
        exact hxy, -- the case z = a
        exact hyz, -- the case z = b
        exact hyz, -- the case z = c
      -- y = b
      rcases z,
        exact hyz, -- the case z = a; `R b a` is false
        exact hxy, -- the case z = b
        triv,      -- the case z = c; `R a c` is true
      -- y = c
      rcases z,
        exact hyz, -- the case z = a; `R c a` is false
        triv,      -- the case z = b; `R a b` is true
        exact hxy, -- the case z = c
    -- x = b
    rcases y,
      -- y = a
      rcases z,
        exact hxy, -- the case z = a 
        exact hxy, -- the case z = b; `R b a` is false
        triv,      -- the case z = c; `R b c` is true
      -- y = b
      rcases z,
        exact hyz, -- the case z = a
        exact hxy, -- the case z = b
        exact hyz, -- the case z = c
      -- y = c
      rcases z,
        exact hyz, -- the case z = a; `R c a` is false
        exact hyz, -- the case z = b; `R c b` is false
        exact hxy, -- the case z = c
    -- x = c
    rcases y,
      -- y = a
      rcases z,
        exact hxy, -- the case z = a 
        exact hxy, -- the case z = b; `R c a` is false
        exact hxy, -- the case z = c; `R c a` is false
      -- y = b
      rcases z,
        exact hyz, -- the case z = a; `R b a` is false
        exact hxy, -- the case z = b
        exact hxy, -- the case z = c; `R c b` is false
      -- y = c
      rcases z,
        exact hyz, -- the case z = a
        exact hyz, -- the case z = b
        exact hxy, -- the case z = c
end

-- S is transitive
lemma S_trans : transitive S :=
begin
  intros x y z hxy hyz,
  rcases x,
    -- x = a
    rcases y,
      -- y = a
      rcases z,
        exact hxy, -- the case z = a
        exact hyz, -- the case z = b
        exact hyz, -- the case z = c
      -- y = b
      rcases z,
        exact hxy, -- the case z = a; `S a b` is false
        exact hxy, -- the case z = b
        exact hxy, -- the case z = c; `S a b` is false
      -- y = c
      rcases z,
        exact hxy, -- the case z = a; `S a c` is false
        exact hxy, -- the case z = b; `S a c` is false
        exact hxy, -- the case z = c
    -- x = b
    rcases y,
      -- y = a
      rcases z,
        exact hxy, -- the case z = a 
        exact hyz, -- the case z = b; `S a b` is false
        triv,      -- the case z = c; `S b c` is true
      -- y = b
      rcases z,
        exact hyz, -- the case z = a
        exact hxy, -- the case z = b
        exact hyz, -- the case z = c
      -- y = c
      rcases z,
        triv,      -- the case z = a; `S b a` is true
        exact hyz, -- the case z = b; `S c b` is false
        exact hxy, -- the case z = c
    -- x = c
    rcases y,
      -- y = a
      rcases z,
        exact hxy, -- the case z = a 
        exact hyz, -- the case z = b; `S a b` is false
        exact hyz, -- the case z = c; `S a c` is false
      -- y = b
      rcases z,
        triv,      -- the case z = a; `S c a` is true
        exact hxy, -- the case z = b
        exact hxy, -- the case z = c; `S c b` is false
      -- y = c
      rcases z,
        exact hyz, -- the case z = a
        exact hyz, -- the case z = b
        exact hyz, -- the case z = c
end

-- U is NOT transitive
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), transitive R → transitive S → transitive U) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { exact R_trans}, -- Prove R is transitive
  { have h1 : transitive U, {apply h, exact S_trans},
    have h2 : U b a, -- show hypothesis that U b a is true
      {use c, split, triv, triv},
    have h3 : U a c, -- show hypothesis that U a c is true
      {use b, split, triv, triv},
    specialize h1 b a c h2 h3, -- focus on the specific case with h1, h2
    { cases h1 with x hx,
      rcases x,
      exact hx.1, exact hx.1, exact hx.2}, -- check `U b c` is false
  },
end

end X
end transitivity

-- (4) Antisymmetry: Not preserved under composition
-- Counterexample: R, S are relations on X = {a,b} that
                -- R(a,b), R(b,b) true, else false
                -- S(b,a), S(b,b) true, else false
namespace antisymmetry

inductive X : Type
| a : X
| b : X

namespace X

-- Define binary relation R such that 
-- R(a,b), R(b,b) true, else false
def R : X → X → Prop
| a a := false
| a b := true
| b a := false
| b b := true

-- Define binary relation S such that 
-- S(b,a), S(b,b) true, else false
def S : X → X → Prop
| a a := false
| a b := false
| b a := true
| b b := true

def U : X → X → Prop := comp R S

-- R is anti-symmetric
lemma R_antisymm : anti_symmetric R :=
begin
  intros x y hxy hyx,
  rcases x,
    -- x = a
    rcases y,
      refl,               -- y = a
      exfalso, apply hyx, -- y = b
    -- x = b
    rcases y,
      exfalso, apply hxy, -- y = a
      refl,               -- y = b
end

-- S is anti-symmetric
lemma S_antisymm : anti_symmetric S :=
begin
  intros x y hxy hyx,
  rcases x,
    -- x = a
    rcases y,
      refl,               -- y = a
      exfalso, apply hxy, -- y = b
    -- x = b
    rcases y,
      exfalso, apply hyx, -- y = a
      refl,               -- y = b
end

-- U is NOT anti-symmetric
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), anti_symmetric R → anti_symmetric S → anti_symmetric U) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { exact R_antisymm}, -- Prove R is antisymmetric
  { have h1 : anti_symmetric U, {apply h, exact S_antisymm},
    have h2 : U a b, -- show hypothesis that U b a is true
      {use b, split, triv, triv},
    have h3 : U b a, -- show hypothesis that U a b is true
      {use b, split, triv, triv},
    specialize h1 a b h2 h3, -- focus on the specific case with h1, h2
    rcases h1, -- check that h1 is false
  },
end

end X
end antisymmetry

-- (5) Asymmetry: Not preserved under composition
-- Counterexample: R, S are relations on X = {a,b} that
                -- R(a,b) true, else false
                -- S(b,a) true, else false
namespace asymmetry

inductive X : Type
| a : X
| b : X

namespace X

-- Define binary relation R such that 
-- R(a,b) true, else false
def R : X → X → Prop
| a a := false
| a b := true
| b a := false
| b b := false

-- Define binary relation S such that 
-- S(b,a) true, else false
def S : X → X → Prop
| a a := false
| a b := false
| b a := true
| b b := false

def U : X → X → Prop := comp R S

-- R is asymmetric
lemma R_asymm : asymmetric R :=
begin
  intros x y hxy hyx,
  rcases x,
    -- x = a
    rcases y,
      exact hxy, -- y = a; `R a a` is false
      exact hyx, -- y = b; `R b a` is false
    -- x = b
    rcases y,
      exact hxy, -- y = a; `R b a` is false
      exact hyx, -- y = b; `R b b` is false
end

-- S is asymmetric
lemma S_asymm : asymmetric S :=
begin
  intros x y hxy hyx,
  rcases x,
    -- x = a
    rcases y,
      exact hxy, -- y = a; `S a a` is false
      exact hxy, -- y = b; `S a b` is false
    -- x = b
    rcases y,
      exact hyx, -- y = a; `S a b` is false
      exact hyx, -- y = b; `R b b` is false
end

-- U is NOT asymmetric
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), asymmetric R → asymmetric S → asymmetric U) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { exact R_asymm}, -- Prove R is antisymmetric
  { have h1 : asymmetric U, {apply h, exact S_asymm},
    have h2 : U a a, {use b, split, triv, triv}, -- show hypothesis that U a a is true
    specialize h1 a a, -- focus on the specific case with h1, h2
    apply h1, exact h2, exact h2, -- check that h1 is false
  },
end

end X
end asymmetry

-- (6) Irreflexivity: Not preserved under composition
-- Counterexample: R, S are relations on X = {a,b} that
                -- R(a,b) true, else false
                -- S(b,a) true, else false
namespace irreflexivity

inductive X : Type
| a : X
| b : X

namespace X

-- Define binary relation R such that 
-- R(a,b) true, else false
def R : X → X → Prop
| a a := false
| a b := true
| b a := false
| b b := false

-- Define binary relation S such that 
-- S(b,a) true, else false
def S : X → X → Prop
| a a := false
| a b := false
| b a := true
| b b := false

def U : X → X → Prop := comp R S

-- R is irreflexive
lemma R_irrfl : irreflexive R :=
begin
  intro x,
  rcases x,
    repeat { intro h, exact h},
end

-- S is irreflexive
lemma S_irrfl : irreflexive S :=
begin
  intro x,
  rcases x,
    repeat { intro h, exact h},
end

-- U is NOT irreflexive
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), irreflexive R → irreflexive S → irreflexive U) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { exact R_irrfl}, -- Prove R is antisymmetric
  { have h1 : irreflexive U, {apply h, exact S_irrfl},
    have h2 : U a a, {use b, split, triv, triv}, -- show hypothesis that U a a is true
    specialize h1 a, -- focus on the specific case with h1, h2
    apply h1, exact h2, -- check that h1 is false
  },
end

end X
end irreflexivity

-- (7) Totality: Preserved under composition
example (R S : A → A → Prop) (totalR : total R) (totalS : total S) : total (comp R S) :=
begin
  intros x y,
  have h1 : R x x ∨ R x x, apply totalR x x,
  have h2 : R y y ∨ R y y, apply totalR y y,
  specialize totalS x y,
  cases totalS with hSxy hSyx,
    {left, use x, split, rcases h1, exact h1, exact h1, exact hSxy},
    {right, use y, split, rcases h2, exact h2, exact h2, exact hSyx},
end

end myrelation