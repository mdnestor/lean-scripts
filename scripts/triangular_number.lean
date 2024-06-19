-- baby's first inductive proof: 1+2+3+...+n = n*(n+1)/2
-- https://en.wikipedia.org/wiki/Triangular_number

-- natural numbers are the quintessential inductive type
-- https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html
inductive Natural where
| zero: Natural
| next: Natural → Natural

-- next we define addition and multiplication by cases
def add (a b: Natural): Natural :=
  match a with
  -- by cases: if a=0, then a+b = 0+b = b
  | Natural.zero => b
  -- otherwise, if a = n+1, then a+b = (n+1)+b = (n+b)+1
  | Natural.next n => Natural.next (add n b)

def mul (a b: Natural): Natural :=
  match a with
  -- again by cases: if a=0, then a*b = 0
  | Natural.zero => Natural.zero
  -- otherwise, if a = n+1, then a * b = (n+1) * b = n*b + b
  | Natural.next n => add (mul n b) b

-- some basic helper theorems, not worth proving here
theorem add_comm (a b: Natural): add a b = add b a := sorry
theorem mul_comm (a b: Natural): mul a b = mul b a := sorry
theorem add_assoc (a b c: Natural): add a (add b c) = add (add a b) c := sorry
theorem mul_assoc (a b c: Natural): mul a (mul b c) = mul (mul a b) c := sorry
theorem distrib (a b c: Natural): mul a (add b c) = add (mul a b) (mul a c) := sorry

-- define the n-th triangular number to be 0+1+...+n
def triangular (n: Natural): Natural :=
  match n with
  -- the "zeroth" triangular number is zero
  | Natural.zero => Natural.zero
  -- if n = m+1, then the n-th triangular number is the m-th triangular number + n
  | Natural.next m => add (triangular m) n

-- aliases
def one: Natural := Natural.next Natural.zero
def two: Natural := Natural.next one

-- add local theorems to the simplifier
attribute [local simp] add mul add_comm mul_comm add_assoc mul_assoc distrib

-- to avoid defining (possibly non-integer) division, the theorem is stated as 2*(1+2+3+...+n) = n*(n+1)
theorem sum_of_first_n: ∀ n: Natural, mul two (triangular n) = mul n (Natural.next n) := by
  intro n
  -- proof by induction
  induction n with
  -- base case is simple
  | zero => {
    rw [triangular]
    simp
  }
  -- the inductive step with hyp = the inductive hypothesis on n
  | next n hyp => {
    rw [triangular, distrib, hyp]
    -- once the inductive hypothesis is applied successfully, brute force tree search :D
    simp
    rw [mul_comm, mul]
    have h1: add n n.next = add n.next n := by apply add_comm
    rw [h1, add]
    have h2: mul n n.next.next = mul n.next.next n := by apply mul_comm
    rw [h2, mul, mul]
    rw [add_comm, add, add, add_comm, add_assoc, add_comm]
  }
