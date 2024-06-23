/-
The naive way to check if a number n is prime is to check for divisors in the range 1,...,n.
A wellknown speedup is to only check in the range 1,...,sqrt(n),
since every divisor d which is greater than sqrt(n) corresponds to another divisor n/d which is less than sqrt(n).
Can we implement both functions and prove they are equal on all inputs?
-/

def is_prime (n : Nat) : Bool :=
  let divisors := List.range (n + 1)
  let divisors := divisors.filter (fun m => n % m == 0)
  divisors.length == 2

def is_prime_fast (n : Nat) : Bool :=
  if n < 2 then
    false
  else
    let floor_sqrt_n := USize.toNat (Float.toUSize (Float.sqrt (Nat.toFloat n)))
    let divisors := List.range (floor_sqrt_n + 1)
    let divisors := divisors.filter (fun m => n % m == 0)
    divisors.length == 1

example: ∀ n: Nat, is_prime n = is_prime_fast n := by
  intro n
  rw [is_prime, is_prime_fast]
  simp
  -- no clue xd
  sorry
