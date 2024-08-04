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

def continuous [MetricSpace X1] [MetricSpace X2] (f: X1 → X2): Prop :=
  ∀ x: X1, ∀ ε: Real, ε > 0 → ∃ δ: Real, δ > 0 ∧ ∀ y: X1, dist x y < δ → dist (f x) (f y) < ε

def converges [MetricSpace X] (a: Nat → X) (x: X): Prop :=
  ∀ ε: Real, ε > 0 → ∃ N: Nat, ∀ n: Nat, N ≤ n → dist (a n) x < ε

def cauchy [MetricSpace X] (a: Nat → X): Prop :=
  ∀ ε: Real, ε > 0 → ∃ N: Nat, ∀ m n: Nat, N ≤ m ∧ N ≤ n → dist (a m) (a n) < ε

def complete {X: Type} (_: MetricSpace X): Prop :=
  ∀ a: Nat → X, cauchy a → ∃ x: X, converges a x

theorem arbitrarily_close_eq (x: Real) (h: 0 ≤ x): (∀ ε: Real, ε > 0 → x < ε) → x = 0 := by
  sorry

theorem limit_unique [MetricSpace X] {a: Nat → X} (h1: converges a x1) (h2: converges a x2): x1 = x2 := by
  -- we can show for every ε > 0 that dist x1 x2 < ε
  have x1_x2_arbitrarily_close: ∀ ε: Real, ε > 0 → dist x1 x2 < ε := by
    intro ε ε_pos
    have ε_div_2_pos: ε/2 > 0 := div_pos_iff.mpr (Or.inl ⟨ε_pos, two_pos⟩)
    obtain ⟨N1, conv_impl1⟩ := h1 (ε/2) ε_div_2_pos
    obtain ⟨N2, conv_impl2⟩ := h2 (ε/2) ε_div_2_pos
    let n := max N1 N2
    have an_near_x1 := conv_impl1 n (by apply le_max_left)
    have an_near_x2 := conv_impl2 n (by apply le_max_right)
    calc
      dist x1 x2 ≤ dist x1 (a n) + dist (a n) x2 := by apply dist_triangle
                 _ = dist (a n) x1 + dist (a n) x2 := by rw [dist_comm]
                 _ < ε/2 + ε/2                         := by linarith [an_near_x1, an_near_x2]
                 _ = ε                                 := by simp
  have dist_x1_x2_zero := arbitrarily_close_eq (dist x1 x2) dist_nonneg x1_x2_arbitrarily_close
  exact eq_of_dist_eq_zero dist_x1_x2_zero

-- If a(0), a(1), a(2), ... converges to x and f is continuous then f(a(0)), f(a(1)), f(a(2)), ... converges to f(x)
theorem apply_continuous_function_to_convergent_sequence [MetricSpace X1] [MetricSpace X2] {f: X1 → X2} {a: Nat → X1} (h1: converges a x) (h2: continuous f): converges (f ∘ a) (f x) := by
  intro ε ε_pos
  obtain ⟨δ, ⟨δ_pos, ε_δ_impl⟩⟩ := h2 x ε ε_pos
  obtain ⟨N, a_conv_impl⟩ := h1 δ δ_pos
  exists N
  intro n N_leq_n
  have ε_δ_impl_an := ε_δ_impl (a n)
  have dist_an_x_lt_δ := a_conv_impl n N_leq_n
  rw [dist_comm] at dist_an_x_lt_δ
  have dist_fan_fx_lt_ε := ε_δ_impl_an dist_an_x_lt_δ
  rw [dist_comm] at dist_fan_fx_lt_ε
  exact dist_fan_fx_lt_ε

-- The t-th tail of a sequence a(0), a(1), a(2) ... is the sequence a(t), a(t+1), a(t+2), ...
def tail {X: Type} (a: Nat → X) (t: Nat): Nat → X :=
  fun n => a (n + t)

-- If a sequence converges to x then so does every tail
theorem tail_converge [MetricSpace X] {a: Nat → X} {x: X} (h: converges a x) (t: Nat): converges (tail a t) x := by
  intro ε ε_pos
  obtain ⟨N, conv_impl⟩ := h ε ε_pos
  exists N - t
  intro n
  simp
  rw [tail]
  exact conv_impl (n + t)

theorem iter_tail {X: Type} (f: X → X) (x: X): f ∘ (fun n => f^[n] x) = tail (fun n => f^[n] x) 1 := by
  ext
  rw [tail]
  simp
  rw [Function.Commute.iterate_self]

-- if f is continuous and the sequence of iterates x, f(x), f(f(x)), ... converges then it converges to a fixed point of f
theorem iter_converge_to_fixed_point {X: Type} [MetricSpace X] {x L: X} {f: X → X} (h1: continuous f) (h2: converges (fun n => f^[n] x) L): f L = L := by
  have h3 := apply_continuous_function_to_convergent_sequence h2 h1
  rw [iter_tail] at h3
  have h4 := tail_converge h2 1
  exact limit_unique h3 h4

def contraction {X: Type} [MetricSpace X] (T: X → X): Prop :=
  ∃ c: Real, 0 ≤ c ∧ c < 1 ∧ ∀ x y: X, dist (T x) (T y) ≤ c * dist x y

-- https://math.stackexchange.com/a/1800125
theorem contraction_continuous [MetricSpace X] {T: X → X} (h: contraction T): continuous T := by
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
    dist (T x) (T y) ≤ c * dist x y  := by apply contr_ineq
                     _ < c * (ε / c) := by apply (mul_lt_mul_left c_pos).mpr x_y_within_eps_div_c
                     _ = ε           := by rw [mul_div_cancel₀ ε c_case]

theorem easy_lemma {a b: Real} (h1: a ≤ b * a) (h2: a ≥ 0) (h3: b < 1): a = 0 := by
  apply Classical.not_not.mp
  apply Not.intro
  intro a_neq_zero
  have a_gt_zero := lt_of_le_of_ne h2 (ne_comm.mp a_neq_zero)
  have a_div_a_leq_b := (div_le_iff a_gt_zero).mpr h1
  rw [div_self a_neq_zero] at a_div_a_leq_b
  have b_not_lt_one := not_lt.mpr a_div_a_leq_b
  contradiction

theorem geom_series_bound (c: Real) (n: Nat): 0 ≤ c → c < 1 → (∑ i in Finset.range n, c^i) ≤ (1 - c)⁻¹ := by
  sorry

theorem pow_reverse {c: Real} {m n: Nat}: 0 ≤ c → c < 1 → m ≤ n → c^n ≤ c^m := by
  sorry

-- if T is a contraction then dist(T^n(x), T^n(y)) ≤ c^n * dist(x, y)
theorem iter_cauchy_lemma1 [MetricSpace X] {c: Real} (c_nonneg: c ≥ 0) (contr_ineq: ∀ (x y : X), dist (T x) (T y) ≤ c * dist x y): ∀ x y: X, ∀ n: Nat, dist (T^[n] x) (T^[n] y) ≤ c^n * dist x y := by
  intro x y n
  induction n with
  | zero => simp
  | succ p h => calc
    dist (T^[p+1] x) (T^[p+1] y)
    = dist (T (T^[p] x)) (T (T^[p] y)) := by rw [Function.iterate_succ', Function.comp]
    _ ≤ c * dist (T^[p] x) (T^[p] y)   := by apply contr_ineq
    _ ≤ c * (c^p * dist x y)           := mul_le_mul_of_nonneg_left h c_nonneg
    _ = c^(p+1) * dist x y             := by ring

theorem finset_range_sum_lemma [AddCommMonoid X] (n: Nat) (f: Nat → X): (∑ i ∈ Finset.range n, f i) + (f n) = ∑ i ∈ Finset.range (n+1), f i := by
  sorry

theorem iter_cauchy_lemma2 [MetricSpace X] (x: X) (n: Nat) (c: Real) (c_nonneg: c ≥ 0) (contr_ineq: ∀ (x y : X), dist (T x) (T y) ≤ c * dist x y): dist x (T^[n] x) ≤ (∑ i in Finset.range n, c^i) * dist x (T x) := by
  induction n with
  | zero => simp [eq_of_dist_eq_zero]
  | succ p h_induction => {
    calc
      dist x (T^[p+1] x)
      _ ≤ dist x (T^[p] x) + dist (T^[p] x) (T^[p+1] x)      := by apply dist_triangle
      _ ≤ (∑ i ∈ Finset.range p, c^i) * dist x (T x) + dist (T^[p] x) (T^[p+1] x)
                                                             := by apply add_le_add_right h_induction
      _ ≤ (∑ i ∈ Finset.range p, c^i) * dist x (T x) + c^p * dist x (T x)
                                                             := by apply add_le_add_left (by apply iter_cauchy_lemma1 c_nonneg contr_ineq)
      _ = ((∑ i ∈ Finset.range p, c^i) + c^p) * dist x (T x) := by rw [right_distrib]
      _ = (∑ i ∈ Finset.range (p+1), c^i) * dist x (T x)     := by rw [finset_range_sum_lemma p (fun i => c^i)]
  }

-- if T is a contraction then dist(x, T^n(x)) ≤ (1 - c)⁻¹ * dist(x, Tx)
theorem iter_cauchy_lemma3 [MetricSpace X] {c: Real} (c_nonneg: c ≥ 0) (c_lt_one: c < 1) (contr_ineq: ∀ (x y : X), dist (T x) (T y) ≤ c * dist x y): ∀ x: X, ∀ n: Nat, dist x (T^[n] x) ≤ (1 - c)⁻¹ * dist x (T x) := by
  intro x n
  calc
    dist x (T^[n] x) ≤ (∑ i in Finset.range n, c^i) * dist x (T x) := iter_cauchy_lemma2 x n c c_nonneg contr_ineq
    _ ≤ (1 - c)⁻¹ * dist x (T x) := mul_le_mul_of_nonneg_right (geom_series_bound c n c_nonneg c_lt_one) dist_nonneg

theorem iter_lemma {T: X → X} {n: Nat} (h1: n ≥ 1): (T^[n] x) = T (T^[n-1] x) := by
  sorry

theorem easy_lemma2 {c: Real} (h: c < 1): (1 - c)⁻¹ > 0 := by
  sorry

theorem iter_cauchy {X: Type} [MetricSpace X] {T: X → X} {x0: X} (h1: contraction T): cauchy (fun n => T^[n] x0) := by
  intro ε ε_pos
  obtain ⟨c, ⟨c_nonneg, c_lt_one, contr_ineq⟩⟩ := h1
  by_cases h2: c = 0
  -- case 1: c = 0
  simp [h2] at contr_ineq
  exists 1
  intro m n ⟨one_leq_m, one_leq_n⟩
  calc
    dist (T^[m] x0) (T^[n] x0)
    _ = dist (T (T^[m-1] x0)) (T (T^[n-1] x0)) := by rw [iter_lemma one_leq_m, iter_lemma one_leq_n]
    _ = dist (T (T^[m-1] x0)) (T (T^[m-1] x0)) := by rw [contr_ineq]
    _ ≤ 0 := by rw [dist_self]
    _ < ε := ε_pos
  -- case 2: c > 0
  let N: Nat := sorry -- should be greater than log_c(2 * ε * (1-c) / (M.dist x0 (T x0)))
  have h6: c^N * (1 - c)⁻¹ * dist x0 (T x0) < ε := sorry
  exists N
  intro m n ⟨N_leq_m, N_leq_n⟩
  have c_pow_m_nonneg := pow_nonneg c_nonneg m
  have c_pow_n_nonneg := pow_nonneg c_nonneg n
  have one_minus_c_inv_nonneg: (1 - c)⁻¹ ≥ 0 := le_of_lt (easy_lemma2 c_lt_one)
  by_cases h7: m ≤ n
  -- case 2.1: m ≤ n
  let d := n - m
  have h8: n = m + d := by rw [← Nat.sub_add_cancel h7, add_comm]
  rw [h8]
  calc
    dist (T^[m] x0) (T^[m + d] x0)
      = dist (T^[m] x0) (T^[m] (T^[d] x0)) := by rw [Function.iterate_add, Function.comp_apply]
    _ ≤ c^m * dist x0 (T^[d] x0)           := by apply iter_cauchy_lemma1 c_nonneg contr_ineq
    _ ≤ c^m * ((1 - c)⁻¹ * dist x0 (T x0)) := mul_le_mul_of_nonneg_left (by apply iter_cauchy_lemma3 c_nonneg c_lt_one contr_ineq) c_pow_m_nonneg
    _ ≤ c^N * ((1 - c)⁻¹ * dist x0 (T x0)) := mul_le_mul_of_nonneg_right (pow_reverse c_nonneg c_lt_one N_leq_m) (mul_nonneg one_minus_c_inv_nonneg dist_nonneg)
    _ = c^N * (1 - c)⁻¹ * dist x0 (T x0)   := by rw [mul_assoc]
    _ < ε                                  := h6
  -- case 2.2: m > n
  -- generalize to n ≤ m
  let d := m - n
  have h7: m ≥ n := Nat.le_of_lt (Nat.not_le.mp h7)
  have h8: m = n + d := by rw [← Nat.sub_add_cancel h7, add_comm]
  rw [h8]
  calc
    dist (T^[n+d] x0) (T^[n] x0)
      = dist (T^[n] (T^[d] x0)) (T^[n] x0) := by rw [Function.iterate_add, Function.comp_apply]
    _ ≤ c^n * dist (T^[d] x0) x0           := by apply iter_cauchy_lemma1 c_nonneg contr_ineq
    _ = c^n * dist x0 (T^[d] x0)           := by rw [dist_comm]
    _ ≤ c^n * ((1 - c)⁻¹ * dist x0 (T x0)) := mul_le_mul_of_nonneg_left (by apply iter_cauchy_lemma3 c_nonneg c_lt_one contr_ineq) c_pow_n_nonneg
    _ ≤ c^N * ((1 - c)⁻¹ * dist x0 (T x0)) := mul_le_mul_of_nonneg_right (pow_reverse c_nonneg c_lt_one N_leq_n) (mul_nonneg one_minus_c_inv_nonneg dist_nonneg)
    _ = c^N * (1 - c)⁻¹ * dist x0 (T x0)   := by rw [mul_assoc]
    _ < ε                                  := h6

theorem contraction_mapping_theorem {X: Type} {M: MetricSpace X} {T: X → X} (h0: Nonempty X) (h1: complete M) (h2: contraction T): ∃! x: X, T x = x := by
  -- assume X is nonempty, pick an arbitrary point
  let x0: X := Classical.choice h0
  -- define a sequence
  let a: Nat → X := fun n => T^[n] x0
  -- show it is cauchy (hard)
  have a_cauchy: cauchy a := iter_cauchy h2
  -- since the sequence is cauchy it has a limit
  obtain ⟨x, a_converges_to_x⟩ := h1 a a_cauchy
  exists x
  -- need to show x is indeed a fixed point
  have x_fixed_point := iter_converge_to_fixed_point (contraction_continuous h2) a_converges_to_x
  apply And.intro
  exact x_fixed_point
  -- now show point is unique
  intro y
  simp
  intro y_fixed_point
  apply eq_comm.mp
  obtain ⟨c, ⟨c_geq_zero, c_lt_one, contr_ineq⟩⟩ := h2
  have x_y_dist_leq_c_mul_x_y_dist := calc
    M.dist x y = M.dist (T x) (T y) := by rw [x_fixed_point, y_fixed_point]
               _ ≤ c * (M.dist x y) := by apply contr_ineq
  have x_y_dist_zero: M.dist x y = 0 := easy_lemma x_y_dist_leq_c_mul_x_y_dist dist_nonneg c_lt_one
  exact M.eq_of_dist_eq_zero x_y_dist_zero
