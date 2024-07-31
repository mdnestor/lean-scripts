/-
Contraction mapping theorem aka the Banach fixed point theorem
-/
import Mathlib.Data.Real.Basic

structure Metric (X: Type) where
  dist: X → X → Real
  nonneg: ∀ x y: X, dist x y ≥ 0
  eq_iff_dist_zero: ∀ x y: X, x = y ↔ dist x y = 0
  symm: ∀ x y: X, dist x y = dist y x
  tri: ∀ x y z: X, dist x z ≤ dist x y + dist y z

def continuous (M1: Metric X1) (M2: Metric X2) (f: X1 → X2): Prop :=
  ∀ x: X1, ∀ ε : Real, ε > 0 → ∃ δ : Real, δ > 0 ∧ ∀ y: X1, M1.dist x y < δ → M2.dist (f x) (f y) < ε

def converges (M: Metric X) (a: Nat → X) (x: X): Prop :=
  sorry

def convergent (M: Metric X) (a: Nat → X): Prop :=
  ∃ x: X, converges M a x

def limit_unique (M: Metric X) (a: Nat → X) (h: convergent M a): ∃! x: X, converges M a x := by
  sorry

noncomputable def limit (M: Metric X) (a: Nat → X) (h: convergent M a): X :=
  Classical.choose (limit_unique M a h)

def cauchy (M: Metric X) (a: Nat → X): Prop :=
  sorry

def complete (M: Metric X): Prop :=
  ∀ a: Nat → X, cauchy M a → convergent M a

def contraction (M: Metric X) (T: X → X): Prop :=
  ∃ c: Real, 0 ≤ c ∧ c < 1 ∧ ∀ x y: X, M.dist (T x) (T y) ≤ c * (M.dist x y)

def recursive {X: Type} (f: X → X) (x: X) : Nat → X := fun n => match n with
  | Nat.zero => x
  | Nat.succ p => f ((recursive f x) p)

-- theorem: if recursive converges, the result is a fixed point
theorem recursive_converge_to_fixed_point (M: Metric X) (f: X → X) (h: continuous M M f) (x L: X):
  converges M (recursive f x) L → f L = L := by
  sorry

theorem contraction_continuous (M: Metric X) (T: X → X) (h: contraction M T): continuous M M T := by
  sorry

-- https://www.math.ucdavis.edu/~hunter/book/ch3.pdf
theorem contraction_mapping_theorem {X: Type} {M: Metric X} (T: X → X) (h1: complete M) (h2: contraction M T): ∃! x: X, T x = x := by
  let x0: X := Classical.choice sorry -- assume X is nonempty
  -- define a sequence
  let a: Nat → X := recursive T x0
  -- show it is cauchy (hard)
  have h3 : cauchy M a := sorry
  -- since the sequence is cauchy it has a limit
  obtain ⟨x, h4⟩ := h1 a h3
  exists x
  apply And.intro
  -- need to show x is indeed a fixed point
  simp
  have h5 := recursive_converge_to_fixed_point M T (contraction_continuous M T h2) x0 x
  exact h5 h4
  -- now show point is unique
  intro y
  simp
  intro h5
  obtain ⟨c, ⟨h6, h7, h8⟩⟩ := h2
  have h9 := calc
    M.dist x y = M.dist (T x) (T y) := by sorry
               _ ≤ c * (M.dist x y) := by sorry
  have h10: M.dist x y = 0 := sorry
  have h11 := (M.eq_iff_dist_zero x y).mpr h10
  simp [h11]
