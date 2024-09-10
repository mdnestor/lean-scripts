
-- given a functor f: T → T'
-- and a category C with all small colimits
-- there is a functor Lan_f(-) : [T, C] → [T, C']

import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Equivalence

open CategoryTheory

universe u1 u2 u3

noncomputable def left_kan
  {T: Type u1} {T': Type u2}
  [SmallCategory T]
  [Category T']
  (f: Functor T T')
  (C: Type u3)
  [Category C]
  -- [Limits.HasColimits C]
  [∀ F: Functor T C, f.HasLeftKanExtension F]: -- should be automatically inferred since T is small and C is cocomplete
  Functor (T ⥤ C) (T' ⥤ C) := {
    obj := fun M => CategoryTheory.Functor.leftKanExtension f M
    map := by
      intro M M' η
      simp
      #check (CategoryTheory.Functor.leftKanExtension f M)

      -- F and F' are functors from T to C
      -- a is a natural transformation from F to F'
      #check f.leftKanExtension M
      #check f.leftKanExtension M'

      -- i need a natural transformation from
      -- f.ext M: T' ⥤ C to f.ext M' : T' ⥤ C

      sorry
  }
-- I am trying to construct the functor from [T, C] to [T', C]. I know that it sends a functor M: T ⥤ C to Lan_f(M): T' ⥤ C
-- but what does it do to natural transformations? I have functors M and M' : T ⥤ C and a natural transformation η : M ⟶ M and I need to return a natural transformation Lan_f(M) ⟶ Lan_f(M')?

-- define the category of indexed sets
class ISet where
  X: Type u
  A: X → Type v

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

-- there is an equivalence between this category
-- and the arrow category of Set
def eqv: CategoryTheory.Equivalence ISet (Arrow (Type u3)) := {
  functor := {
    obj := fun I => {
        left := sorry
        right := sorry
        hom := sorry
      }
    map := sorry
  }
  inverse := {
    obj := sorry
    map := sorry
  }
  unitIso := sorry
  counitIso := sorry
}

def eqv_comp (T: Type u1) [Category T]: Functor (T ⥤ ISet) (T ⥤ (Arrow (Type u3))) := {
  obj := fun F => F ⋙ eqv.functor
  map := fun η => whiskerRight η eqv.functor
}

theorem main {T: Type u1} {T': Type u2}
  [Category T]
  [Category T']
  (f: Functor T T')
  [∀ F: Functor T ISet, f.HasLeftKanExtension F]
  [∀ F: Functor T (Arrow (Type u3)), f.HasLeftKanExtension F]:
  IsIsomorphic
  ((left_kan f ISet) ⋙ (eqv_comp T'))
  ((eqv_comp T) ⋙ (left_kan f (Arrow (Type u3)))) := by
  simp [left_kan]
  aesop_cat
