/- https://www.math.ucdavis.edu/~hunter/book/ch3.pdf -/

/- axiomatizing necessary properties of real numbers -/

axiom R: Type

axiom R.zero: R
axiom R.one: R
axiom R.add: R -> R -> R
axiom R.leq: R -> R -> Prop

infix:0 " + " => R.add
infix:0 " ≤ " => R.leq

def R.lt: R -> R -> Prop := fun x y => (x ≤ y) ∧ (x ≠ y)

infix:0 " < " => R.lt

/- onward to metric space -/

structure MetricSpace (X: Type) where
  distance: X -> X -> R
  d1: forall x: X, distance x x = R.zero
  d2: forall x y: X, distance x y = distance y x
  d3: forall x y z: X, (distance x z) ≤ (distance x y + distance y z)

def contraction_mapping (M: MetricSpace X) (f: X -> X): Prop :=
  exists c: R, (R.zero ≤ c) ∧ (c < R.one) ∧ forall x y: X, M.distance (f x) (f y) < M.distance x y

def Cauchy (M: MetricSpace X) (a: Nat -> X): Prop :=
  forall epsilon: R, (R.zero < epsilon) -> exists N: Nat, forall m n: Nat, (m ≥ N) ∧ (n ≥ N) -> ((M.distance (a n) (a m)) < epsilon)

def converges_to (M: MetricSpace X) (a: Nat -> X) (x: X): Prop :=
  forall epsilon: R, (R.zero < epsilon) -> exists N: Nat, forall n: Nat, n ≥ N -> ((M.distance (a n) x) < epsilon)

def convergent (M: MetricSpace X) (a: Nat -> X): Prop :=
  exists x: X, converges_to M a x

def complete (M: MetricSpace X): Prop :=
  forall a: Nat -> X, Cauchy M a -> convergent M a

structure existsunique (p: X -> Prop): Prop where
  exist: exists x: X, p x
  unique: forall x y: X, p x ∧ p y -> x = y

def run {X: Type} (f: X -> X) (x: X): Nat -> X :=
  fun n => match n with
  | Nat.zero => x
  | Nat.succ n_prev => f ((run f x) n_prev)

theorem lemma1 (M: MetricSpace X) (f: X -> X) (h: contraction_mapping M f): forall x: X, Cauchy M (run f x) := sorry

theorem ContractionMappingTheorem (M: MetricSpace X) (f: X -> X) (h1: complete M) (h2: contraction_mapping M f): existsunique (fun x => f x = x) := {
  exist := by
    have h3 := lemma1 M f h2
    have x0: X := sorry
    have h4 : Cauchy M (run f x0) := by apply h3
    have h5 : convergent M (run f x0) := by apply h1; exact h4
    sorry
  unique := sorry
}
