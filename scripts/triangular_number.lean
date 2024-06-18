-- baby's first inductive proof: 1+2+3+...+n = n*(n+1)/2
-- https://en.wikipedia.org/wiki/Triangular_number

inductive Natural where
| first: Natural
| next: Natural → Natural

axiom P1: ∀ a b: Natural, Natural.next a = Natural.next b → a = b
axiom P2: ∀ a: Natural, Natural.next a ≠ Natural.first

def add (a b: Natural): Natural :=
  match a with
  | Natural.first => b
  | Natural.next a_previous => Natural.next (add a_previous b)

def mul (a b: Natural): Natural :=
  match a with
  | Natural.first => Natural.first
  | Natural.next a_previous => add (mul a_previous b) b

def triangular (n: Natural): Natural :=
  match n with
  | Natural.first => Natural.first
  | Natural.next n_previous => add (triangular n_previous) n

def zero: Natural := Natural.first
def one: Natural := Natural.next Natural.first
def two: Natural := Natural.next one


theorem sum_of_first_n: ∀ n: Natural, mul two (triangular n) = mul n (Natural.next n) := by
  intro n
  induction n with
  | first => {
    rw [triangular, mul, two, one, mul, mul, mul, add, add] -- ez
  }
  | next n_previous h => {
    sorry -- damnit this is hard.. think i need distributive property xd
  }
