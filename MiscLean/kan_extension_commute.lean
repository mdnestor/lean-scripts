
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

-- there is an equivalence between this category and the arrow category of Set
def eqv: CategoryTheory.Equivalence ISet (Arrow (Type u)) := sorry

-- given category T lift to functor from [T, ISet] to [T, Arrow(Set)] via the equivalence
def eqv_comp (T: Type u1) [Category T]: Functor (T ⥤ ISet) (T ⥤ (Arrow (Type u2))) := {
  obj := fun F => F ⋙ eqv.functor
  map := fun η => whiskerRight η eqv.functor -- not 100% this is correct
}

instance: Limits.HasColimits ISet := sorry

instance: Limits.HasColimits (Arrow (Type u3)) := sorry

instance {T: Type u1} {C: Type u2} [SmallCategory T] [Category C] [Limits.HasColimits C] {f: Functor T C}: ∀ F: Functor T C, f.HasLeftKanExtension F := sorry

theorem main {T: Type u1} {T': Type u2} [SmallCategory T] [SmallCategory T']
  (f: Functor T T')
  [∀ F: Functor T ISet, f.HasLeftKanExtension F]
  [∀ F: Functor T (Arrow (Type u3)), f.HasLeftKanExtension F]: -- these should be inferred since T is small and C is cocomplete
  IsIsomorphic (Functor.lan f ⋙ eqv_comp T') (eqv_comp T ⋙ Functor.lan f)  -- isomorphism in the functor category
  sorry
