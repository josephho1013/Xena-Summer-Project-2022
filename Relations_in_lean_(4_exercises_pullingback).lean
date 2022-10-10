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

-- Miscellaneous problems related to pulling back relations

-- Pulling back binary relations
namespace Q6
def R {X Y : Type*} (f : X → Y) (S : Y → Y → Prop) (a b : X) : Prop := S (f a) (f b)

-- (1) Reflexivity: Preserved under pushing-back
lemma Q6a (X Y : Type*) (f : X → Y) (S : Y → Y → Prop) : reflexive S → ∀ (x : X), R f S x x :=
begin
  intros reflS x,
  apply reflS (f x),
end

-- (2) Symmetry: Preserved under pushing-back
lemma Q6b (X Y : Type*) (f : X → Y) (S : Y → Y → Prop) : 
symmetric S → ∀ (x y : X), R f S x y → R f S y x :=
begin
  intros symmS x y hxy,
  unfold R at *,
  apply symmS (f x) (f y) hxy,
end

-- (3) Transitivity: Preserved under pushing-back
lemma Q6c (X Y : Type*) (f : X → Y) (S : Y → Y → Prop) : 
transitive S → ∀ (x y z : X), R f S x y ∧ R f S y z → R f S x z :=
begin
  intros transS x y z h,
  cases h with hxy hyz,
  apply transS (f x) (f y) (f z) hxy hyz,
end

-- (4) Anti-symmetry: NOT preserved under pushing-back
inductive X : Type u_1
| a : X
| b : X

namespace X

inductive Y : Type u_2
| c : Y

namespace Y

-- Define surjective map
def f : X → Y
| a := c
| b := c

-- Define binary relations R and S
def S : Y → Y → Prop
| c c := true

lemma S_anti_symm : anti_symmetric S :=
begin
  intros a b hSab hSba,
  rcases a, -- consider cases of values of a (only 'c')
  rcases b, -- consider cases of values of b (only 'c')
  refl,
end

lemma Q6d : ¬(∀ (X Y : Type*), ∀ (f : X → Y), ∀ (S : Y → Y → Prop), 
anti_symmetric S → (∀ (x y : X), R f S x y ∧ R f S y x → x = y)) :=
begin
  intro h, -- change to `hypothesis → false`
  specialize h X Y f S, -- focus on the specific example we construct
  have h1 : ∀ (x y : X), R f S x y ∧ R f S y x → x = y, {apply h, exact S_anti_symm},
  have h2 : R f S a b, -- show hypothesis that R a b is true
    {trivial}, -- since R a b = S c c is true
  have h3 : R f S b a, -- show hypothesis that R b a is true
    {trivial}, -- since R b a = S c c is true
  specialize h1 a b, -- focus on the specific case with h2, h3
  have h4 : a = b, {apply h1, split, exact h2, exact h3},
  rcases h4, -- check that `h4` is false
end

end Y
end X

-- (5) Asymmetry: Preserved under pushing-back
lemma Q6e (X Y : Type*) (f : X → Y) (S : Y → Y → Prop) : asymmetric S → ∀ (x y : X), R f S x y → ¬(R f S y x) :=
begin
  intros asymmS x y hxy hyx,
  apply asymmS (f x) (f y) hxy hyx,
end

-- (6) Irreflexivity: Preserved under pushing-back
lemma Q6f (X Y : Type*) (f : X → Y) (S : Y → Y → Prop) : irreflexive S → ∀ (x : X), ¬(R f S x x) :=
begin
  intros irreflS x hxx,
  apply irreflS (f x) hxx,
end

-- (7) Totality: Preserved under pushing-back
lemma Q6g (X Y : Type*) (f : X → Y) (S : Y → Y → Prop) : 
total S → ∀ (x y : X), R f S x y ∨ R f S y x :=
begin
  intros totalS x y,
  cases totalS (f x) (f y),
  {left, exact h},
  {right, exact h},
end

end Q6
end myrelation
