def converges (a: Nat -> Float) (L: Float): Prop :=
  forall epsilon: Float, exists N: Nat, forall n: Nat,
  (0 < epsilon) ∧ (N < n) -> Float.abs (a n - L) < epsilon

def convergent (a: Nat -> Float) : Prop :=
  exists L: Float, converges a L

def partial_sums (a: Nat -> Float): Nat -> Float := by
  intro n
  exact match n with
  | Nat.zero => 0
  | Nat.succ m => a n + (partial_sums a) m

def series_convergent (a: Nat -> Float): Prop :=
  convergent (partial_sums a)

theorem partial_sums_convergent_implies_limit_zero (a: Nat -> Float):
  series_convergent a -> converges a 0 := 
  sorry
