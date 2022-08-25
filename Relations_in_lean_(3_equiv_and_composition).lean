import tactic

-- References: Schmidt, G. (2010) Relational Mathematics. Cambridge: Cambridge University Press (Encyclopedia of Mathematics and its Applications). doi: 10.1017/CBO9780511778810.

namespace myrelation
variables {α β γ A B C: Type*}
variable (R : A → A → Prop)

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

-- Section 4: Equivalence relations
def equivalence (R : A → A → Prop) := reflexive R ∧ symmetric R ∧ transitive R

-- Using preorder, we describe a partial order as an antisymmetric preorder,
-- and an equivalence relation as a symmetric preorder

example (R : A → A → Prop):
  equivalence R ↔ preorder R ∧ symmetric R :=
begin
  split,
  { intro equivR,
    cases equivR with reflR h1,
    split,
    split,
    exact reflR,
    exact h1.2, -- transitive R
    exact h1.1}, -- symmetric R
  { intro h,
    cases h with h1 symmR,
    split,
    exact h1.1, -- reflexive R
    split,
    exact symmR,
    exact h1.2}, -- transitive R
end

-- another way of defining equivalence relations
example (R : A → A → Prop) (reflR : reflexive R) (h : ∀ (a b c : A), R a b ∧ R c b → R a c) : equivalence R :=
begin
  split,
  -- prove reflexivity
  exact reflR,

  split,
  -- prove symmetry
  intros a b hRab,
  have h1 : R b b := reflR b,
  specialize h b b a,
  apply h,
  split,
  exact h1, exact hRab,

  -- prove transitivity
  intros a b c hRab hRbc,
  have h2 : R a b ∧ R c b → R a c := h a b c,
  have h3 : R c c ∧ R b c → R c b := h c c b,
  apply h2,
  split,
  exact hRab,
  apply h3,
  split,
  exact reflR c,
  exact hRbc,
end

-- If E is a equivalence relation, then E ∘ ((E ∘ R) ∩ S) = (E ∘ R) ∩ (E ∘ S)
example (E : A → A → Prop) (R : A → A → Prop) (S : A → A → Prop) (equivE : equivalence E) : comp E (intersect (comp E R) S) = intersect (comp E R) (comp E S) :=
begin
  cases equivE with reflE equivE,
  cases equivE with symmE transE,

  ext a b,
  split,
  { intro h,
    cases h with c hc,
    cases hc with hEac hc,
    cases hc with hER hScb,
    cases hER with d hcd,
    split,
    { use d,
      split,
      apply transE a c d hEac hcd.1,
      exact hcd.2},
    { use c,
      split,
      exact hEac,
      exact hScb},
    },
  { intro h,
    cases h with hER hES,
    cases hER with c hc,
    cases hES with d hd,
    use d,
    split,
    exact hd.1,
    split,
    { use c,
      split,
      have hEda : E d a, apply symmE a d hd.1,
      apply transE d a c hEda hc.1,
      exact hc.2},
    exact hd.2,
    },
end
-- Since R, S are arbitrary, we can use similar arguments to show `E ∘ ((E ∘ S) ∩ R) = (E ∘ R) ∩ (E ∘ S)`.

-- Section 5: Compositions
namespace composition_relations
/-
Define composition of relations (analogous to friend of a friend):
For relations R,S on set A, the composition `R ∘ S` is the relation that, for a,b ∈ A, (R ∘ S)(a,b) is the proposition that `∃ (y : A), R a y ∧ S y b`.

If R = S, we write the composition as R₂.
-/
def R₂ (a b : A) : Prop := ∃ (y : A), R a y ∧ R y b
-- ∃ (y : A), R a y ∧ R y b
-- (∀ (a b : A), (∃ (y : A), R a y ∧ R y b) → R a b)

-- The composition operation on binary relations is associative.
lemma relation_comp_assoc (R : A → A → Prop) (S : A → A → Prop) (T : A → A → Prop) : comp (comp R S) T = comp R (comp S T) :=
begin
  ext a b,
  split,
  { intro h,
    cases h with y h, -- unfold relation.comp & let such element be y
    cases h with h1 h2, -- split conjunction ∧
    cases h1 with z h1, -- unfold relation.comp & let such element be z
    use z,
    split,
    exact h1.1,
    { use y,
      split,
      exact h1.2,
      exact h2},
    },
  { intro h,
    rw comp at *,
    cases h with y h, -- unfold relation.comp & let such element be y
    cases h with h1 h2,
    cases h2 with z h2, -- unfold relation.comp & let such element be y
    use z,
    split,
    { use y,
      split,
      exact h1,
      exact h2.1},
    exact h2.2,
  },
end

-- A relation R is transitive iff R_2 is transitive.
lemma trans_iff_closure (R : A → A → Prop) : transitive R ↔ (∀ (a b : A), (∃ (y : A), R a y ∧ R y b) → R a b) :=
begin
  split,
  { intros transR a b h1,
    cases h1 with y h1,
    apply transR a y b h1.1 h1.2,
    },
  { intro h,
    intros a b c hRab hRbc,
    specialize h a c,
    apply h,
    use b,
    split,
    exact hRab,
    exact hRbc,
    },
end

def idempotent (R : A → A → Prop) : Prop := 
∀ (a b : A), (∃ (y : A), R a y ∧ R y b) ↔ R a b

lemma refl_trans_implies_idempotence (reflR : reflexive R) (transR : transitive R) : idempotent R :=
begin
  intros a b,
  split,
  { intro h,
    cases h with y h,
    apply transR a y b h.1 h.2},
  { intro Rab,
    use a,
    split,
    apply reflR a,
    exact Rab},
end 

def R_transpose (a b : A) : Prop := R b a

end composition_relations

namespace relations_2
--variables {a b : A}

/- Schröder's rule
For binary relations (a : A → B → Prop) (b : B → C → Prop) (c : A → C → Prop), the following are equivalent:
1)  A ∘ B ⊆ C
2)  A.transpose ∘ C.complement ⊆ B.complement
3)  C.complement ∘ B.transpose ⊆ A.complement
-/

theorem schroder_rule_1 (a : A → B → Prop) (b : B → C → Prop) (c : A → C → Prop) : (∀ (x : A) (z : C), relation.comp a b x z → c x z) ↔ (∀ (y : B) (z : C), relation.comp (transpose a) (complement c) y z → complement b y z) :=
begin
  split,
  { intro h,
    intros y z h1, -- fix y ∈ B and z ∈ C
    --rw relation.comp at h1, -- unfold relation composition
    cases h1 with x h1, -- let such element be x ∈ A
    cases h1 with haxy hncxz, -- simplify `and` conjunction
    specialize h x z,
    intro hbyz, -- change complement def into `b y z → false`
    apply hncxz,
    apply h,
    use y, -- y is the required intermediate element
    split,
    exact haxy,
    exact hbyz,
    },
  { intro h,
    intros x z h1, -- fix x ∈ A and z ∈ C
    cases h1 with y h1, -- let such intermediate element be y
    cases h1 with haxy hbyz, -- simplify `and` conjunction
    specialize h y z,
    by_contra hncxz,
    apply h,
    { use x, -- x is the required intermediate element
      split,
      exact haxy,
      exact hncxz},
    exact hbyz,
    },
end

theorem schroder_rule_2 (a : A → B → Prop) (b : B → C → Prop) (c : A → C → Prop) : (∀ (x : A) (z : C), comp a b x z → c x z) ↔ (∀ (x : A) (y : B), comp (complement c) (transpose b) x y → complement a x y) :=
begin
  split,
  { intro h,
    intros x y h1, -- fix x ∈ A and y ∈ B
    cases h1 with z h1, -- let such element be z ∈ C
    cases h1 with hncxz hbzy, -- simplify `and` conjunction
    specialize h x z,
    intro haxy,
    apply hncxz,
    apply h,
    use y, -- y is the required intermediate element
    split,
    exact haxy,
    exact hbzy},
  { intro h,
    intros x z h1, -- fix x ∈ A and z ∈ C
    cases h1 with y h1, -- let such element be y ∈ B
    cases h1 with haxy hbyz,
    specialize h x y,
    by_contra hncxz,
    apply h,
    { use z,  -- z is the required intermediate element
      split,
      exact hncxz,
      exact hbyz},
    exact haxy},
end

lemma transpose_comp (a : A → B → Prop) (b : B → C → Prop) : transpose (comp a b) = comp (transpose b) (transpose a) :=
begin
  ext z x,
  split,
  { intro h,
    -- rw relation_transpose at h,
    cases h with y hy, -- let such element in the composition be y ∈ B
    use y,
    split,
    exact hy.2,
    exact hy.1},
  { intro h,
    cases h with y hy,
    use y,
    split,
    exact hy.2,
    exact hy.1},
end

/- Dedekind rule
For binary relations (a : A → B → Prop) (b : B → C → Prop) (c : A → C → Prop), x ∈ A, y ∈ B,
((a ∘ b) ∩ c) x y → ((a ∩ (c ∘ b.transpose)) ∘ (b ∩ (a.transpose ∘ c))) x y
-/

theorem dedekind_rule (a : A → B → Prop) (b : B → C → Prop) (c : A → C → Prop) : ∀ (x : A) (z : C), intersect (comp a b) c x z → comp (intersect a (comp c (transpose b))) (intersect b (comp (transpose a) c)) x z :=
begin
  intros x z h,
  cases h with h1 hcxz,
  cases h1 with y h1_y,
  use y,
  split,
  { split,
    { exact h1_y.1},
    { use z,
      split,
      exact hcxz,
      exact h1_y.2},
    },
  { split,
    { exact h1_y.2},
    { use x,
      split,
      exact h1_y.1,
      exact hcxz},
    },
end

-- Exercise 4.3.1 (Relational Mathematics) (R ⊆ R ∘ R.transpose ∘ R)
example (r : A → B → Prop) (x : A) (y : B): r x y → comp (comp r (transpose r)) r x y :=
begin
  intro rxy,
  use x,
  split,
  { use y,
    split,
    exact rxy,
    exact rxy},
  { exact rxy},
end

-- Exercise 4.3.2 (Relational Mathematics) (A.transpose ∘ C ⊆ D → (A ∘ B) ∩ C ⊆ A ∘ (B ∩ D))
example (a : A → B → Prop) (b : B → C → Prop) (c : A → C → Prop) (d : B → C → Prop) : 
(∀ (y : B) (z : C), comp (transpose a) c y z → d y z) → (∀ (x : A) (z : C), intersect (comp a b) c x z  → comp a (intersect b d) x z) :=
begin
  intro h,
  intros x z h1,
  cases h1 with h2 hcxz,
  cases h2 with y h2,
  cases h2 with haxy hbyz,
  specialize h y z,
  use y,
  split,
  exact haxy,
  split,
  { exact hbyz},
  { apply h,
    use x,
    split,
    exact haxy,
    exact hcxz},
end

end relations_2

end myrelation
