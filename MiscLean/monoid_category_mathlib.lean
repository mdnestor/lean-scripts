import Mathlib.CategoryTheory.Monoidal.Category
namespace CategoryTheory

universe u v
axiom C (T: Type u): Category T
axiom M (T: Type u) [Category T]: MonoidalCategory T
