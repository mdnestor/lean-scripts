import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Real -- allows defining continuous function on ℝ
import Mathlib.Order.Monotone.Basic -- for StrictMono


def increasing_property {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)): Prop :=
  ∀ A B: Finset X, A ⊆ B ∧ A ∈ F → B ∈ F

-- state that property is nontrivial
def trivial_property {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)): Prop :=
  sorry

def finite_compl (X: Type) [Fintype X] [DecidableEq X] (A: Finset X): Finset X := Aᶜ

def product_measure (p: Real) (X: Type) [Fintype X] [DecidableEq X] (A: Finset X): Real := p^(Finset.card A) * (1-p)^(Finset.card Aᶜ)

-- now I need to sum up all the subsets

def total_measure {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)) (p: Real): Real := sorry

-- state that the total measure is continuous and strictly increasing
theorem total_measure_continuous {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)): Continuous (fun p => total_measure F p) := sorry

-- state that the total measure is strictly increasing
theorem total_measure_strictly_increasing {X: Type} [Fintype X] [DecidableEq X] (F: Finset (Finset X)) (h1: increasing_property F): StrictMono (fun p => total_measure F p) := sorry

