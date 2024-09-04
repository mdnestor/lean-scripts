-- in this file we define the free monoid over a type
-- we show any function between types extends to a homomorphism between free monoids, namely `map`
-- we also show the free monoid over the unit type is isomorphic to the monoid of natural numbers

-- definition of a monoid
structure Monoid where
  element: Type
  op: element → element → element
  unit: element
  assoc: ∀ x y z: element, op (op x y) z = op x (op y z)
  unit_left: ∀ x: element, op unit x = x
  unit_right: ∀ x: element, op x unit = x

-- the monoid of natural numbers with addition
def NatMonoid: Monoid := {
  element := Nat
  op := Nat.add
  unit := Nat.zero
  assoc := Nat.add_assoc
  unit_left := Nat.zero_add
  unit_right := Nat.add_zero
}

-- the free monoid over an alphabet
def FreeMonoid (X: Type): Monoid := {
  element := List X
  op := List.append
  unit := List.nil
  assoc := List.append_assoc
  unit_left := List.nil_append
  unit_right := List.append_nil
}

-- monoid homomorphism
structure Homomorphism (M N: Monoid) where
  func: M.element → N.element
  preserve: ∀ x y: M.element, func (M.op x y) = N.op (func x) (func y)

-- a function between alphabets extends to a homomorphism between free monoids
def FreeHomomorphism {X Y: Type} (f: X → Y): Homomorphism (FreeMonoid X) (FreeMonoid Y) := {
  func := List.map f
  preserve := by simp [FreeMonoid]
}

-- the length homomorphism from a free monoid to the monoid of natural numbers
def LengthHomomorphism (X: Type): Homomorphism (FreeMonoid X) NatMonoid := {
  func := List.length
  preserve := List.length_append
}

def injective (f: X → Y): Prop :=
  ∀ x1 x2: X, f x1 = f x2 → x1 = x2

def surjective (f: X → Y): Prop :=
  ∀ y: Y, ∃ x: X, f x = y

def bijective (f: X → Y): Prop :=
  injective f ∧ surjective f

-- monoid isomorphism
structure Isomorphism (M N: Monoid) extends Homomorphism M N where
  bijective: bijective func

-- Unit is a type containing one element (aka a singleton set)
-- if two lists containing units have the same length, they are equal
theorem unit_list_lemma {L1 L2 : List Unit} (h: L1.length = L2.length): L1 = L2 := by
  induction L1 generalizing L2 with
  | nil =>
    cases L2 with
    | nil => rfl
    | cons _ _ => contradiction
  | cons _ _ ih =>
    cases L2 with
    | nil => contradiction
    | cons _ _ =>
      simp [List.beq]
      simp at h
      exact ih h

-- the free monoid on a one-element set is isomorphic to the monoid of natural numbers
example: Isomorphism (FreeMonoid Unit) NatMonoid := {
  func := List.length
  preserve := List.length_append
  bijective := by
    apply And.intro
    intro L1 L2 h
    exact unit_list_lemma h
    intro n
    exists List.replicate n Unit.unit
    simp
}
