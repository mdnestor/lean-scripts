import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

def finite_compl (X: Type) [Fintype X] [DecidableEq X] (A: Finset X): Finset X := Aᶜ

def product_measure (p: Real) (X: Type) [Fintype X] [DecidableEq X] (A: Finset X): Real := p^(Finset.card A) * (1-p)^(Finset.card Aᶜ)

