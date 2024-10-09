import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Data.Finite.Defs

class CommRing (X: Type u) where
  add: X → X → X
  mul: X → X → X
  zero: X
  one: X
  add_assoc: ∀ x y z: X, add (add x y) z = add x (add y z)
  add_comm: ∀ x y: X, add x y = add y x
  add_zero: ∀ x: X, add x zero = x
  zero_add: ∀ x: X, add zero x = x
  inv: X → X
  add_inv_left: ∀ x: X, add (inv x) x = zero
  add_inv_right: ∀ x: X, add x (inv x) = zero
  mul_assoc: ∀ x y z: X, mul (mul x y) z = mul x (mul y z)
  mul_one: ∀ x: X, mul x one = x
  one_mul: ∀ x: X, mul one x = x
  left_distrib: ∀ x y z: X, mul x (add y z) = add (mul x y) (mul x z)
  right_distrib: ∀ x y z: X, mul (add x y) z = add (mul x z) (mul y z)

open CommRing

class Ideal {X: Type u} [CommRing X] (I: Set X): Prop where
  h1: zero ∈ I
  h2: ∀ x y: X, x ∈ I → y ∈ I → add x y ∈ I
  h3: ∀ x y: X, x ∈ I → mul x y ∈ I

class PrimeIdeal {X: Type u} [CommRing X] (I: Set X) extends Ideal I: Prop where
  h4: ∀ x y: X, mul x y ∈ I → x ∈ I ∨ y ∈ I
  h5: I ⊂ Set.univ

def Ideals (X: Type u) [CommRing X]: Set (Set X) := 
  fun I => Ideal I

def PrimeIdeals (X: Type u) [CommRing X]: Set (Set X) := 
  fun I => PrimeIdeal I

class TopologicalSpace (X: Type u) where
  opensets: Set (Set X)
  empty_isOpen: ∅ ∈ opensets
  univ_isOpen: Set.univ ∈ opensets
  union_isOpen: ∀ S: Set (Set X), S ⊆ opensets → Set.sUnion S ∈ opensets
  inter_isOpen: ∀ S: Set (Set X), S ⊆ opensets ∧ Finite S → Set.sInter S ∈ opensets

def V {X: Type u} [CommRing X] (I: Set X): Set (PrimeIdeals X) :=
  fun ⟨P, _⟩ => I ⊆ P

def Spec {X: Type u} [CommRing X]: TopologicalSpace (PrimeIdeals X) := {
  opensets := fun S => ∃ I ∈ Ideals X, S = Set.compl (V I)
  empty_isOpen := by
    sorry
  univ_isOpen := by sorry
  union_isOpen := by
    intro S h
    sorry
  inter_isOpen := by
    intro S h
    sorry
}
