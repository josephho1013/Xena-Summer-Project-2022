import tactic

-- References: Schmidt, G. (2010) Relational Mathematics. Cambridge: Cambridge University Press (Encyclopedia of Mathematics and its Applications). doi: 10.1017/CBO9780511778810.

namespace myrelation
variables {α β γ A: Type*}

def union (r : α → β → Prop) (s : α → β → Prop) (a : α) (b : β) : Prop := r a b ∨ s a b
def intersect (r : α → β → Prop) (s : α → β → Prop) (a : α) (b : β) : Prop := r a b ∧ s a b

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

-- 2021 IUM Final Q1c
    -- R, S two binary relations on set {A : Type}. 
    -- Define relations `def T (a b : A) : Prop := R a b ∧ S a b`, 
    -- `def U (a b : A) : Prop := R a b ∨ S a b`
    -- (i)    If R, S equivalence relations, then T is equivalence relation
    -- (ii)   If R, S equivalence relations, then U may not be an equivalence relation.
    -- (iii)  If R, S antisymmetric, then T is also antisymmetric.
    -- (iv)   If R, S antisymmetric, then U may not be antisymmetric.

-- Extension
-- (1) Reflexivity: preserved under ∪ and ∩. (shown in (i)(ii))
example (R S : A → A → Prop) (reflR : reflexive R) (reflS : reflexive S) : reflexive (intersect R S) :=
begin
  intro x,
  split,
  apply reflR x,
  apply reflS x,
end

example (R S : A → A → Prop) (reflR : reflexive R) (reflS : reflexive S) : reflexive (union R S) :=
begin
  intro x,
  left,
  apply reflR x,
end

-- (2) Symmetry: preserved under ∪ and ∩. (shown in (i)(ii))
example (R S : A → A → Prop) (symmR : symmetric R) (symmS : symmetric S) : symmetric (intersect R S) :=
begin
  intros x y h,
  cases h with hRxy hSxy,
  split,
  apply symmR x y hRxy,
  apply symmS x y hSxy,
end

example (R S : A → A → Prop) (symmR : symmetric R) (symmS : symmetric S) : symmetric (union R S) :=
begin
  intros x y h,
  cases h with hRxy hSxy,
  left, apply symmR x y hRxy,
  right, apply symmS x y hSxy,
end

-- (3) Transitivity: preserved only under ∩, but not ∪ (shown in (i)(ii))
example (R S : A → A → Prop) (transR : transitive R) (transS : transitive S) : transitive (intersect R S) :=
begin
  intros x y z h1 h2,
  cases h1 with hRxy hSxy,
  cases h2 with hRyz hSyz,
  split,
  { apply transR x y z hRxy hRyz},
  { apply transS x y z hSxy hSyz},
end

-- Counterexample for `∪`: Idea (For a,b,c, we construct R and S that
                     -- R(a,b), S(b,c) true, R(b,c), S(a,b) false, R(a,c), S(a,c) false)
                     -- In fact, such R and S exist
                     -- Let X = {a,b,c}
                     -- R(a,a), R(b,b), R(c,c), R(a,b), R(b,a) true, else false
                     -- S(a,a), S(b,b), S(c,c), S(b,c), S(b,c) true, else false

namespace transitivity

inductive X : Type
| a : X
| b : X
| c : X

namespace X

-- Define binary relation R such that 
-- R(a,a), R(b,b), R(c,c), R(a,b), R(b,a) true, else false
def R : X → X → Prop
| a a := true
| b b := true
| c c := true
| a b := true
| b a := true
| b c := false
| c b := false
| a c := false
| c a := false

-- Define binary relation S such that 
-- S(a,a), S(b,b), S(c,c), S(b,c), S(b,c) true, else false
def S : X → X → Prop
| a a := true
| b b := true
| c c := true
| a b := false
| b a := false
| b c := true
| c b := true
| a c := false
| c a := false

def U (x y : X) : Prop := R x y ∨ S x y

-- R is transitive
lemma R_trans : transitive R :=
begin
  rintros x y z,
    rcases x,
      -- x = a
      rcases y,
        -- y = a
          rcases z, -- 3 cases
            repeat {intros h1 h2, triv}, -- solves first two T → T cases
            intros h1 h2, exact h2, -- solve last case
        -- y = b
          rcases z, -- 3 cases
            repeat {intros h1 h2, triv}, -- solves first two T → T cases
            intros h1 h2, exact h2, -- solve last case
        -- y = c
          rcases z, -- 3 cases
            repeat {intros h1 h2, triv}, -- solves first two T → T cases
            intros h1 h2, exact h1, -- solve last case
      
      -- x = b
      rcases y,  
        -- y = a
          rcases z,
            repeat {intros h1 h2, triv},
            intros h1 h2, exact h2,
        -- y = b
          rcases z,
            repeat {intros h1 h2, triv},
            intros h1 h2, exact h2,
        -- y = c
          rcases z,
            repeat {intros h1 h2, triv},
            intros h1 h2, exact h1,
      -- x = c
      rcases y,
        -- y = a
          rcases z, 
            intros h1 h2, exact h1,
            intros h1 h2, by_contra h3, exact h1,
            intros h1 h2, triv,
        -- y = b
          rcases z,
            intros h1 h2, by_contra h3, exact h1, 
            intros h1 h2, exact h1,
            intros h1 h2, triv,
        -- y = c
          rcases z,
            repeat {intros h1 h2, exact h2},
end

-- S is transitive
lemma S_trans : transitive S :=
begin
  rintros x y z,
    rcases x,
      -- x = a
      rcases y,
        -- y = a
          rcases z, -- 3 cases
            intros h1 h2, triv,
            repeat {intros h1 h2, exact h2},
        -- y = b
          rcases z, -- 3 cases
            intros h1 h2, triv,
            repeat {intros h1 h2, exact h1},
        -- y = c
          rcases z, -- 3 cases
            intros h1 h2, triv, -- solves first two T → T cases
            repeat {intros h1 h2, exact h1}, -- solve last case
      
      -- x = b
      rcases y,  
        -- y = a
          rcases z,
            intros h1 h2, exact h1,
            repeat {intros h1 h2, triv},
        -- y = b
          rcases z,
            repeat {intros h1 h2, triv},
            intros h1 h2, exact h2,
        -- y = c
          rcases z,
            repeat {intros h1 h2, triv},
            intros h1 h2, by_contra h3, exact h2,
      -- x = c
      rcases y,
        -- y = a
          rcases z, 
            intros h1 h2, exact h1,
            intros h1 h2, by_contra h3, exact h1,
            intros h1 h2, triv,
        -- y = b
          rcases z,
            intros h1 h2, by_contra h3, exact h2, 
            intros h1 h2, exact h1,
            intros h1 h2, triv,
        -- y = c
          rcases z,
            repeat {intros h1 h2, exact h2},
end

-- U is not transitive
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), (transitive R → transitive S) → transitive U) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { intro transR,
    exact S_trans}, -- Prove S is equivalence relation
  { -- rw transitive at h,
    have h1 : U a b, -- show hypothesis that U a b is true
      {left, triv},
    have h2 : U b c, -- show hypothesis that U b c is true
      {right, triv},
    specialize h a b c h1 h2, -- focus on the specific case with h1, h2
    rcases h, repeat {exact h}, -- since U a c = R a c ∨ S a c, use the fact that R a c and S a c are false
  },
end

end X
end transitivity
-- The above is also a counter-example to the following question in 2021 IUM Q1c:
-- (ii) If R, S equivalence relations, then U may not be an equivalence relation.

-- (4) Anti-symmetry: preserved only under ∩, but not ∪ (shown in (iii)(iv))

example (R S : A → A → Prop) (antisymmR : anti_symmetric R) (antisymmS : anti_symmetric S) : anti_symmetric (intersect R S) :=
  begin
    intros a b hab hba,
    cases hab with hRab hSab,
    cases hba with hRba hSba,
    apply antisymmR a b hRab hRba,
  end

-- Counterexample for `∪`: Let X = {a,b}
                        -- R(a,b) true, else false
                        -- S(b,a) true, else false
                        -- Then U(a,b) and U(b,a) are true, but a ≠ b

namespace antisymmetry

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

-- Define binary relation R such that 
-- S(b,a) true, else false
def S : X → X → Prop
| a a := false
| a b := false
| b a := true
| b b := false


def U (x y : X) : Prop := R x y ∨ S x y

-- R is antisymmetric
lemma Q_iv_R_antisymm : anti_symmetric R :=
begin
  intros x y hXY hYX,
  rcases x,
    -- x = a
    rcases y,
      refl, -- the case y = a
      exfalso, exact hYX, -- the case y = b
    -- x = b
    rcases y,
      exfalso, exact hXY, -- the case y = a
      refl, -- the case y = b
end

-- S is antisymmetric
lemma Q_iv_S_antisymm : anti_symmetric S :=
begin
  intros x y hXY hYX,
  rcases x,
    -- x = a
    rcases y,
      refl, -- the case y = a
      exfalso, exact hXY, -- the case y = b
    -- x = b
    rcases y,
      exfalso, exact hYX, -- the case y = a
      refl, -- the case y = b
end

-- U is NOT antisymmetric
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), (anti_symmetric R → anti_symmetric S) → anti_symmetric U) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { intro antisymmR,
    exact Q_iv_S_antisymm}, -- Prove S is antisymmetric
  { rw anti_symmetric at h,
    have h1 : U a b, -- show hypothesis that U a b is true
      {left, triv},
    have h2 : U b a, -- show hypothesis that U b a is true
      {right, triv},
    specialize h a b h1 h2, -- focus on the specific case with h1, h2
    rcases h, -- check that `h` is false
  },
end

end X
end antisymmetry

-- (5) Asymmetry: preserved only under ∩, but not ∪.
example (R S : A → A → Prop) (asymmR : asymmetric R) (asymmS : asymmetric S) : asymmetric (intersect R S) :=
begin
  intros x y h1 h2,
  cases h1 with hRxy hSxy,
  cases h2 with hRyx hSyx,
  apply asymmR x y hRxy hRyx,
end

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

-- Define binary relation R such that 
-- S(b,a) true, else false
def S : X → X → Prop
| a a := false
| a b := false
| b a := true
| b b := false


def U (x y : X) : Prop := R x y ∨ S x y

-- R is asymmetric
lemma R_asymm : asymmetric R :=
begin
  intros x y hxy hyx,
  rcases x,
    -- x = a
    rcases y,
      exact hxy, -- the case y = a; follows that `R a a` is false
      exact hyx, -- the case y = b; follows that `R b a` is false

    -- x = b
    rcases y,
      exact hxy, -- the case y = a; follows that `R b a` is false
      exact hxy, -- the case y = b; follows that `R b b` is false
end

-- S is asymmetric
lemma S_asymm : asymmetric S :=
begin
  intros x y hxy hyx,
  rcases x,
    -- x = a
    rcases y,
      exact hxy, -- the case y = a; follows that `R a a` is false
      exact hxy, -- the case y = b; follows that `R b a` is false

    -- x = b
    rcases y,
      exact hyx, -- the case y = a; follows that `R b a` is false
      exact hxy, -- the case y = b; follows that `R b b` is false
end

-- U is NOT asymmetric
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), (asymmetric R → asymmetric S) → asymmetric U) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { intro asymmR,
    exact S_asymm}, -- Prove S is antisymmetric
  { rw asymmetric at h,
    have h1 : U a b, -- show hypothesis that U a b is true
      {left, triv},
    have h2 : U b a, -- show hypothesis that U b a is true
      {right, triv},
    specialize h a b h1 h2, -- focus on the specific case with h1, h2
    rcases h, -- check that `h` is false
  },
end

end X
end asymmetry

-- (6) Irreflexivity: preserved under ∪ and ∩.
example (R S : A → A → Prop) (irrflR : irreflexive R) (irrflS : irreflexive S) : irreflexive (intersect R S) :=
begin
  intros x h,
  cases h with hR hS,
  apply irrflS x hS,
end

example (R S : A → A → Prop) (irrflR : irreflexive R) (irrflS : irreflexive S) : irreflexive  (union R S) :=
begin
  intros x h,
  cases h with hR hS,
  apply irrflR x hR,
  apply irrflS x hS,
end

-- (7) Totality: preserved only under ∪, but not ∩.

example (R S : A → A → Prop) (totalR : total R) (totalS : total S) : total (union R S) :=
begin
  intros x y,
  specialize totalR x y,
  specialize totalS x y,
  cases totalR with hRxy hRyx,
  { cases totalS with hSxy hSyx,
    left, left, exact hRxy,
    right, right, exact hSyx},
  { cases totalS with hSxy hSyx,
    right, left, exact hRyx,
    right, right, exact hSyx},
end

namespace totality

inductive X : Type
| a : X
| b : X

namespace X

-- Define binary relation R such that 
-- R(a,b) true, else false
def R : X → X → Prop
| a a := true
| a b := true
| b a := false
| b b := true

-- Define binary relation R such that 
-- S(b,a) true, else false
def S : X → X → Prop
| a a := true
| a b := false
| b a := true
| b b := true

def T (x y : X) : Prop := R x y ∧ S x y

-- R is total
lemma R_total : total R :=
begin
  intros x y,
  rcases x,
    -- x = a
    rcases y,
      left, triv, -- the case y = a; follows that `R a a` is true
      left, triv, -- the case y = b; follows that `R a b` is true

    -- x = b
    rcases y,
      right, triv, -- the case y = a; follows that `R a b` is true
      right, triv, -- the case y = b; follows that `R b b` is true
end

-- S is total
lemma S_total : total S :=
begin
  intros x y,
  rcases x,
    -- x = a
    rcases y,
      left, triv, -- the case y = a; follows that `R a a` is true
      right, triv, -- the case y = b; follows that `R b a` is true

    -- x = b
    rcases y,
      left, triv, -- the case y = a; follows that `R b a` is true
      right, triv, -- the case y = b; follows that `R b b` is true
end

-- T is NOT asymmetric
example : ¬(∀ A : Type, ∀ (R: A → A → Prop) (S: A → A → Prop), (total R → total S) → total T) := 
begin
  intro h, -- change to `hypothesis → false`
  specialize h X R S _, -- focus on the specific example we construct
  { intro totalR,
    exact S_total}, -- Prove S is antisymmetric
  { rw total at h,
    have h1 : ¬(T a b), -- show hypothesis that T a b is false
      {intro hTab, cases hTab with hRab hSab, apply hSab},
    have h2 : ¬(T b a), -- show hypothesis that T b a is false
      {intro hTba, cases hTba with hRba hSba, apply hRba},
    specialize h a b, -- focus on the specific case with x = a, y = b
    rcases h, -- check that `h` is false
    {apply h1, exact h},
    {apply h2, exact h},
  },
end

end X
end totality

end myrelation