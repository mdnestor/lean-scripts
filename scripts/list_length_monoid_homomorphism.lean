structure Monoid (X: Type) where
  op: X → X → X
  unit: X
  assoc: ∀ x0 x1 x2: X, op (op x0 x1) x2 = op x0 (op x1 x2)
  unit_left: ∀ x: X, op unit x = x
  unit_right: ∀ x: X, op x unit = x

def ListMonoid (α: Type): Monoid (List α) := {
  op := List.append
  unit := []
  assoc := List.append_assoc
  unit_left := List.nil_append
  unit_right := List.append_nil
}

structure MonoidHomomorphism (M0: Monoid X0) (M1: Monoid X1) where
  func: X0 → X1
  preserve: ∀ x y: X0, func (M0.op x y) = M1.op (func x) (func y)

-- monoid of natural numbers
def NatMonoid: Monoid Nat := {
  op := Nat.add
  unit := Nat.zero
  assoc := Nat.add_assoc
  unit_left := Nat.zero_add
  unit_right := Nat.add_zero
}

-- the monoid homomorphism that sends a list to its length
def Length (α: Type): MonoidHomomorphism (ListMonoid α) NatMonoid := {
  func := List.length
  preserve := List.length_append
}
