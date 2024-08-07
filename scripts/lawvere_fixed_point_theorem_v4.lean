-- actually using mathlib this time :)
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Closed.Cartesian

open CategoryTheory Limits MonoidalCategory CartesianClosed

def fixed_point_property {C : Type u} [Category.{v} C] [HasFiniteProducts C] [MonoidalCategoryStruct C] [CartesianClosed C] (Y: C): Prop :=
  ∀ t: Y ⟶ Y, ∃ y: 𝟙_C ⟶ Y, y ≫ t = y

def weakly_point_surjective {C : Type u} [Category.{v} C] [HasFiniteProducts C] [MonoidalCategoryStruct C] [CartesianClosed C] {A X Y: C} (g: X ⟶ (exp A).obj Y): Prop :=
  ∀ f: A ⟶ Y, ∃ x: 𝟙_C ⟶ X, ∀ a: 𝟙_C ⟶ A, a ≫ (uncurry (x ≫ g)) = a ≫ f

/-
error:

```
application type mismatch
  a ≫ uncurry (x ≫ g)
argument
  uncurry (x ≫ g)
has type
  A ⨯ 𝟙_ C ⟶ Y : Type v
but is expected to have type
  A ⟶ Y : Type v
```

so I need to compose with the (obvious) map A ⟶ A ⨯ 𝟙_ C
-/
