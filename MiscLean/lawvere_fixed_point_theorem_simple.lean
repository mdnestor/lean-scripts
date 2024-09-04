/-

A simplified version of Lawvere's fixed point theorem in the category of types.

The full argument in Cartesian closed categories is located in `lawvere_fixed_point_theorem.lean`

Ref: "Diagonal arguments and cartesian closed categories" by Lawvere (1969) http://tac.mta.ca/tac/reprints/articles/15/tr15.pdf

-/

@[simp]
def fixed_point {Y: Type} (t: Y → Y) (y: Y): Prop :=
  t y = y

@[simp]
def has_fixed_point {Y: Type} (t: Y → Y): Prop :=
  ∃ y: Y, t y = y

-- a type has the fixed point property if every map from it to itself has a fixed point
-- for types, this is equivalent to saying it only has one element!
def fixed_point_property (Y: Type): Prop :=
  ∀ t: Y → Y, has_fixed_point t

-- not sure how to prove it though
theorem fixed_point_property_iff_all_equal {Y: Type}: fixed_point_property Y ↔ ∀ y1 y2: Y, y1 = y2 := by
  sorry

-- Lawvere uses the notion of "weak point surjectivity"
def weak_surjective {A X Y: Type} (g: X → A → Y): Prop :=
  ∀ f: A → Y, ∃ x: X, ∀ a: A, (g x) a = f a

-- this is weaker than the notion of surjectivity (weak point surjective implies surjective)
def surjective {X Y: Type} (f: X → Y) : Prop :=
  ∀ y: Y, ∃ x: X, f x = y

theorem weak_surjective_of_surjective {A X Y: Type} {g: X → A → Y} (h: surjective g): weak_surjective g := by
  intro f
  obtain ⟨x, hx⟩ := h f
  exists x
  intro
  rw [hx]

-- Lawvere's fixed point theorem:
-- if there exists a weakly point surjective map g: A → Y^A then Y has the fixed point property
theorem lawvere_fixed_point {A Y: Type} {g: A → A → Y} (h: weak_surjective g): fixed_point_property Y := by
  intro t
  obtain ⟨x, hx⟩ := h (fun a => t (g a a))
  exists g x x
  rw [←hx x]

-- the diagonal argument is the contrapositive
theorem lawvere_diagonal {A Y: Type} (h: ¬ fixed_point_property Y) (g: A → A → Y): ¬ weak_surjective g :=
  mt lawvere_fixed_point h

-- we can prove Cantor's theorem as a special case
-- first by showing the type `Prop` does not have the fixed point property
-- namely take the map Not: Prop → Prop which switches True and False
theorem prop_not_fixed_point_property: ¬ fixed_point_property Prop := by
  simp [fixed_point_property]
  exists Not
  simp

def Set (X: Type): Type :=
  X → Prop

theorem Cantor (f: X → Set X): ¬ surjective f := by
  apply mt weak_surjective_of_surjective
  apply lawvere_diagonal
  exact prop_not_fixed_point_property

-- here is a generalization due to "A universal approach to self-referential paradoxes, incompleteness and fixed points" by Yanofsky (2003) https://arxiv.org/pdf/math/0305282.pdf

-- we will say f is representable by g if there exists x such that g x = f
def representable {A Y: Type} (g: X → A → Y) (f: A → Y): Prop :=
  ∃ x: X, g x  = f

-- yanofsky's theorem: if Y doesn't have a fixed point then for all f: T x S -> Y there exists a function not representable by f

-- this is known as Surjective.hasRightInverse
theorem surjective_has_right_inverse {X Y: Type} {f: X → Y} (hf: surjective f): ∃ f': Y → X, ∀ y: Y, f (f' y) = y := by
  sorry

theorem yanofsky_fixed_point {A X Y: Type} {t: Y → Y} (h: ¬ has_fixed_point t) {g: X → A → Y} {b: A → X} (hb: surjective b): ∃ f: A → Y, ¬ representable g f := by
  let f := fun a: A => t (g (b a) a)
  exists f
  apply Not.intro
  intro h0
  obtain ⟨b', hb'⟩ := surjective_has_right_inverse hb
  obtain ⟨a, ha⟩ := h0
  have h1: has_fixed_point t := by
    exists g a (b' a)
    calc
      t (g a (b' a)) = t (g (b (b' a)) (b' a)) := by rw [hb']
      _ = f (b' a) := by rfl
      _ = g a (b' a) := by rw [ha]
  contradiction

-- todo: direct proof and show implies lawvere
