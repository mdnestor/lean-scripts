/-
Contraction mapping theorem aka the Banach fixed point theorem

Follows the proof given in Ch. 3 of Applied Analysis by Hunter and Nachtergaele
https://www.math.ucdavis.edu/~hunter/book/ch3.pdf
-/

import Mathlib.Data.Real.Basic

structure MetricSpace (X: Type) where
  dist: X → X → Real
  nonneg: ∀ x y: X, dist x y ≥ 0
  eq_iff_dist_zero: ∀ x y: X, x = y ↔ dist x y = 0
  symm: ∀ x y: X, dist x y = dist y x
  tri: ∀ x y z: X, dist x z ≤ dist x y + dist y z

def continuous (M1: MetricSpace X1) (M2: MetricSpace X2) (f: X1 → X2): Prop :=
  ∀ x: X1, ∀ ε: Real, ε > 0 → ∃ δ: Real, δ > 0 ∧ ∀ y: X1, M1.dist x y < δ → M2.dist (f x) (f y) < ε

def converges (M: MetricSpace X) (a: Nat → X) (x: X): Prop :=
  ∀ ε: Real, ε > 0 → ∃ N: Nat, ∀ n: Nat, N ≤ n → M.dist (a n) x < ε

def cauchy (M: MetricSpace X) (a: Nat → X): Prop :=
  ∀ ε: Real, ε > 0 → ∃ N: Nat, ∀ m n: Nat, N ≤ m ∧ N ≤ n → M.dist (a m) (a n) < ε

def complete (M: MetricSpace X): Prop :=
  ∀ a: Nat → X, cauchy M a → ∃ x: X, converges M a x

theorem limit_unique (h1: converges M a x1) (h2: converges M a x2): x1 = x2 := by
  sorry

-- If a(0), a(1), a(2), ... converges to x and f is continuous then f(a(0)), f(a(1)), f(a(2)), ... converges to f(x)
theorem apply_continuous_function_to_convergent_sequence (h1: converges M1 a x) (h2: continuous M1 M2 f): converges M2 (f ∘ a) (f x) := by
  intro ε h3
  obtain ⟨δ, ⟨h4, h5⟩⟩ := h2 x ε h3
  obtain ⟨N, h6⟩ := h1 δ h4
  exists N
  intro n h7
  have h8 := h5 (a n)
  have h9 := h6 n h7
  rw [M1.symm] at h9
  have h10 := h8 h9
  rw [M2.symm] at h10
  exact h10

-- The t-th tail of a sequence a(0), a(1), a(2) ... is the sequence a(t), a(t+1), a(t+2), ...
def tail {X: Type} (a: Nat → X) (t: Nat): Nat → X :=
  fun n => a (n + t)

-- If a sequence converges to x then so does every tail
theorem tail_converge (h: converges M a x) (t: Nat): converges M (tail a t) x := by
  intro ε h1
  obtain ⟨N, h2⟩ := h ε h1
  exists N - t
  intro n
  simp
  rw [tail]
  exact h2 (n + t)

-- Given a function f: X → X and a point x: X, the orbit is the sequence x, f(x), f(f(x))), ...
def orbit (f: X → X) (x: X) : Nat → X :=
  fun n =>
  match n with
  | Nat.zero => x
  | Nat.succ p => f ((orbit f x) p)

theorem orbit_tail (f: X → X) (x: X): f ∘ (orbit f x) = tail (orbit f x) 1 := by
  ext
  rw [tail, orbit]
  rfl

-- If an orbit of f converges, the limit is a fixed point of f
theorem orbit_converge_to_fixed_point (h1: continuous M M f) (h2: converges M (orbit f x) L): f L = L := by
  have h3 := apply_continuous_function_to_convergent_sequence h2 h1
  rw [orbit_tail] at h3
  have h4 := tail_converge h2 1
  exact limit_unique h3 h4

def contraction (M: MetricSpace X) (T: X → X): Prop :=
  ∃ c: Real, 0 ≤ c ∧ c < 1 ∧ ∀ x y: X, M.dist (T x) (T y) ≤ c * (M.dist x y)

theorem contraction_continuous (M: MetricSpace X) (T: X → X) (h: contraction M T): continuous M M T := by
  obtain ⟨c, ⟨h1, h2, h3⟩⟩ := h
  intro x ε h4
  by_cases h5: c = 0
  sorry
  exists ε/c
  sorry

theorem contraction_mapping_theorem {M: MetricSpace X} (h1: complete M) (h2: contraction M T): ∃! x: X, T x = x := by
  -- assume X is nonempty, pick an arbitrary point
  let x0: X := Classical.choice sorry
  -- define a sequence
  let a: Nat → X := orbit T x0
  -- show it is cauchy (hard)
  have h3 : cauchy M a := sorry
  -- since the sequence is cauchy it has a limit
  obtain ⟨x, h4⟩ := h1 a h3
  exists x
  apply And.intro
  -- need to show x is indeed a fixed point
  exact orbit_converge_to_fixed_point (contraction_continuous M T h2) h4
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
