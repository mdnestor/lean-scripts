import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

open CategoryTheory

-- category of indexed sets
class ISet where
  X: Type u1
  A: X → Type u2

class ISetHom (I1 I2: ISet) where
  f: I1.X → I2.X
  α (x: I1.X): I1.A x → I2.A (f x)   

def ISetId (I: ISet): ISetHom I I := {
  f := id
  α := fun _ a => a 
}

def ISetComp {I1 I2 I3: ISet} (h1: ISetHom I1 I2) (h2: ISetHom I2 I3): ISetHom I1 I3 := {
  f := h2.f ∘ h1.f
  α := fun x a => h2.α (h1.f x) (h1.α x a)
}

instance: Category ISet := {
  Hom := ISetHom
  id := ISetId
  comp := ISetComp
}

-- ISet is cocomplete
instance: Limits.HasColimits ISet := by
  simp [Limits.HasColimits]
  constructor
  intro J _
  constructor
  intro F
  -- given functor `F : J ⥤ ISet` show that `Limits.HasColimit F`
  sorry

-- equivalence between ISet and Arrow(Set)
def eqv: CategoryTheory.Equivalence ISet (Arrow (Type u)) := sorry

-- given category T lift to functor from [T, ISet] to [T, Arrow(Set)] via the equivalence
def eqv_comp (T: Type u1) [Category T]: Functor (T ⥤ ISet) (T ⥤ (Arrow (Type u2))) := {
  obj := fun F => F ⋙ eqv.functor
  map := fun η => whiskerRight η eqv.functor -- not 100% this is corect
}

-- Arrow(Set) is cocomplete
instance: Limits.HasColimits (Arrow (Type u)) := CategoryTheory.Arrow.hasColimits

-- if f: T ⥤ T' is a functor between small categories and C is cocomplete then every functor F: T ⥤ C has a left kan extension along f
instance {T: Type u1} {T': Type u2} {C: Type u3} [SmallCategory T] [SmallCategory T'] [Category C] [Limits.HasColimits C] {f: Functor T T'}: ∀ F: Functor T C, f.HasLeftKanExtension F := sorry

theorem main {T: Type u1} {T': Type u2} [SmallCategory T] [SmallCategory T'] (f: Functor T T'):
  IsIsomorphic (Functor.lan f ⋙ eqv_comp T') (eqv_comp T ⋙ Functor.lan f) -- isomorphism in the functor category
  := by sorry
