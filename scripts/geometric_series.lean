/- Geometric series -/

/- first axiomatize the real numbers! -/

axiom R: Type
def R.zero: R := sorry
def R.one: R := sorry

def R.add: R -> R -> R := sorry
def R.mul: R -> R -> R := sorry
def R.abs: R -> R := sorry
def R.lt: R -> R -> Prop := sorry
def R.sub: R -> R -> R := sorry
def R.neg: R -> R := sorry
def R.div (_ y: R) (h: y ≠ R.zero): R := sorry
def R.exp: R -> Nat -> R := sorry

infix:0 "^" => R.exp
infix:0 "+" => R.add
infix:0 "*" => R.mul
infix:0 "<" => R.lt
infix:0 "-" => R.sub

/- now introduce sequences -/

def seq (X: Type): Type := Nat -> X

def head (a: seq R): R := a 0

def tail (a: seq R): seq R := fun n => a (n + 1)

def geometric_sequence (x: R): seq R := fun n => x^n

def converges_to (a: seq R) (x: R): Prop := sorry

def convergent (a: seq R): Prop := exists x: R, converges_to a x

def limit (a: seq R) (h: convergent a): R := sorry

theorem converges_to_limit (a: seq R) (h: convergent a): converges_to a (limit a h) := sorry 

def lmul (x: R) (a: seq R): seq R := fun n => x * (a n)

axiom a1 (x: R) (n: Nat): (x*(x^n)) = (x^(n+1))

example: forall x: R, lmul x (geometric_sequence x) = tail (geometric_sequence x) := by intro; funext; apply a1

example: forall a: seq R, forall x: R, converges_to a x -> converges_to (tail a) x := sorry

/- finally series -/

def partial_sums (a: seq R): seq R := fun n => match n with
| 0 => R.zero
| Nat.succ n_previous => (a n_previous) + (partial_sums a) n_previous

def summable (a: seq R): Prop := convergent (partial_sums a)

def sum (a: seq R) (h: summable a): R := sorry

def const_zero_summable: summable (fun n => R.zero) := sorry

def const_zero_sum_zero: sum (fun n => R.zero) const_zero_summable = R.zero := sorry

def tail_summable (a: seq R) (h: summable a): summable (tail a) := sorry

def sum_head_tail (a: seq R) (h: summable a): sum a h = ((head a) + (sum (tail a) (tail_summable a h))) := sorry

def lmul_summable (a: seq R) (h: summable a) (x: R): summable (lmul x a) := sorry

def sum_lmul (x: R) (a: seq R) (h: summable a): sum (lmul x a) (by apply lmul_summable; exact h) = (x * (sum a h)) := sorry

/- I sense theorem T1 could be weaker in settings other than real numbers, but here it is equivalent to T2 -/

theorem T1 (r: R) (h: summable (geometric_sequence r)): sum (geometric_sequence r) h = (R.one + (r * (sum (geometric_sequence r) h))) := sorry

theorem lemma1 (x: R): (R.abs r < R.one) -> (R.one - r) ≠ R.zero := sorry

theorem T2 (r: R) (h1: summable (geometric_sequence r)) (h2: (R.abs r) < R.one): sum (geometric_sequence r) h1 = R.div R.one (R.one - r) (by apply lemma1; exact r; exact h2) := sorry
