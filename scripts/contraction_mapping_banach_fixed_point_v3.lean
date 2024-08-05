/-
Contraction mapping theorem aka the Banach fixed point theorem

Follows the proof given in Ch. 3 of Applied Analysis by Hunter and Nachtergaele
https://www.math.ucdavis.edu/~hunter/book/ch3.pdf

Notation: f^[n] refers to the n-th iterate of f
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic

def Contraction [Dist X] (T: X → X): Prop :=
  ∃ c: Real, 0 ≤ c ∧ c < 1 ∧ ∀ x y: X, dist (T x) (T y) ≤ c * dist x y

theorem contraction_continuous [MetricSpace X] {T: X → X} (h: Contraction T): Continuous T := by
  rw [Metric.continuous_iff]
  obtain ⟨c, ⟨c_nonneg, _, contr_ineq⟩⟩ := h
  intro x ε ε_pos
  by_cases c_case: c = 0
  -- case 1: c = 0
  exists ε
  apply And.intro
  exact ε_pos
  intro y _
  simp [c_case] at contr_ineq
  rw [contr_ineq x y, dist_self]
  exact ε_pos
  -- case 2: c ≠ 0
  have c_pos: c > 0 := lt_of_le_of_ne c_nonneg (ne_comm.mp c_case)
  exists ε/c
  apply And.intro
  exact div_pos_iff.mpr (Or.inl ⟨ε_pos, c_pos⟩)
  intro y x_y_within_eps_div_c
  calc
    dist (T y) (T x) ≤ c * dist y x := by apply contr_ineq
                   _ < c * (ε / c)  := (mul_lt_mul_left c_pos).mpr x_y_within_eps_div_c
                   _ = ε            := by rw [mul_div_cancel₀ ε c_case]


def converge [TopologicalSpace X] (a: Nat → X) (x: X): Prop :=
  Filter.Tendsto a Filter.atTop (nhds x)

def limit_unique {X: Type} [TopologicalSpace X] [T2Space X] {a: Nat → X} {x y: X} (h1: converge a x) (h2: converge a y): x = y := by
  exact tendsto_nhds_unique h1 h2

theorem tail_converge [TopologicalSpace X] {a: Nat → X} {x: X} (h: converge a x) (t: Nat): converge (fun n => a (n + t)) x := by
  sorry

theorem apply_continuous_function_to_convergent_sequence [TopologicalSpace X1] [TopologicalSpace X2] {f: X1 → X2} {a: Nat → X1} (h1: converge a x) (h2: Continuous f): converge (f ∘ a) (f x) := by
  sorry

theorem IterConvergeToFixedPoint {X: Type} {T: X → X} {x x0: X} [MetricSpace X] [CompleteSpace X] (h1: Continuous T) (h2: converge (fun n: Nat => T^[n] x0) x): T x = x := by
  have h3 := apply_continuous_function_to_convergent_sequence h2 h1
  have h4: T ∘ (fun n: Nat => T^[n] x0) = (fun n: Nat => T^[n+1] x0) := by
    ext n
    simp
    rw [Function.Commute.iterate_left]
    rfl
  rw [h4] at h3
  have h5 := tail_converge h2 1
  exact limit_unique h3 h5

theorem iter_cauchy_lemma1 {X: Type} {T: X → X} [MetricSpace X] {c: Real} (c_nonneg: c ≥ 0) (contr_ineq: ∀ (x y : X), dist (T x) (T y) ≤ c * dist x y): ∀ x y: X, ∀ n: Nat, dist (T^[n] x) (T^[n] y) ≤ c^n * dist x y := by
  intro x y n
  induction n with
  | zero => simp
  | succ p h => calc
    dist (T^[p+1] x) (T^[p+1] y)
    = dist (T (T^[p] x)) (T (T^[p] y)) := by rw [Function.iterate_succ', Function.comp]
    _ ≤ c * dist (T^[p] x) (T^[p] y)   := by apply contr_ineq
    _ ≤ c * (c^p * dist x y)           := mul_le_mul_of_nonneg_left h c_nonneg
    _ = c^(p+1) * dist x y             := by ring

theorem easy_lemma {a b: Real} (h1: a ≤ b * a) (h2: a ≥ 0) (h3: b < 1): a = 0 := by
  apply Classical.not_not.mp
  apply Not.intro
  intro a_neq_zero
  have a_gt_zero := lt_of_le_of_ne h2 (ne_comm.mp a_neq_zero)
  have a_div_a_leq_b := (div_le_iff a_gt_zero).mpr h1
  rw [div_self a_neq_zero] at a_div_a_leq_b
  have b_not_lt_one := not_lt.mpr a_div_a_leq_b
  contradiction

theorem ContractionMappingTheorem {X: Type} {T: X → X} [MetricSpace X] [CompleteSpace X] (h0: Nonempty X) (h1: Contraction T): ∃! x: X, T x = x := by
  -- select x0 arbitrarily
  let x0: X := Classical.choice h0
  -- define the recursive sequence
  let a: Nat → X := fun n => T^[n] x0
  -- assume it satisfies contractive property
  have T_continuous := contraction_continuous h1
  obtain ⟨c, ⟨c_nonneg, c_lt_one, contr_ineq⟩⟩ := h1

  have h2: ∀ n: Nat, dist (a n) (a (n + 1)) ≤ dist x0 (T x0) * c^n := by
    intro n
    calc
      dist (a n) (a (n + 1)) = dist (T^[n] x0) (T^[n] (T x0)) := by rfl
                          _ ≤ c^n * dist x0 (T x0)            := by apply iter_cauchy_lemma1 c_nonneg contr_ineq x0 (T x0)
                          _ ≤ dist x0 (T x0) * c^n            := by rw [mul_comm]

  have cauchy := cauchySeq_of_le_geometric c (dist x0 (T x0)) c_lt_one h2
  obtain ⟨x, converges_to_x⟩ := CompleteSpace.complete cauchy
  exists x
  simp
  have x_fixed_point: T x = x := by
    apply IterConvergeToFixedPoint T_continuous
    simp [a] at converges_to_x

    exact converges_to_x
  apply And.intro
  exact x_fixed_point
  -- show it is unique
  intro y y_fixed_point
  apply eq_comm.mp
  have x_y_dist_leq_c_mul_x_y_dist := calc
    dist x y = dist (T x) (T y) := by rw [x_fixed_point, y_fixed_point]
               _ ≤ c * (dist x y) := by apply contr_ineq
  have x_y_dist_zero: dist x y = 0 := easy_lemma x_y_dist_leq_c_mul_x_y_dist dist_nonneg c_lt_one
  exact eq_of_dist_eq_zero x_y_dist_zero
