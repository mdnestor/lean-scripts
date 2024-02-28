/-
Constructing the real numbers.
- natural numbers are defined by hand
- integers are defined as equivalence classes of pairs of naturals
- rationals are classes of pairs of integers
- reals are classes of sequences of rationals
This is standard construction in an introductory proofs course.
-/

inductive Natural where
| zero : Natural
| next (x : Natural) : Natural

def nat_eq (x y : Natural) : Prop :=
  match x with
  | Natural.zero => match y with
    | Natural.zero => True
    | Natural.next _ => False
  | Natural.next x_prev => match y with
    | Natural.zero => False
    | Natural.next y_prev => nat_eq x_prev y_prev

def add (x y : Natural) : Natural :=
  match x with
  | Natural.zero => y
  | Natural.next x_prev => Natural.next (add x_prev y)

def multiply (x y : Natural) : Natural :=
  match x with
  | Natural.zero => Natural.zero
  | Natural.next x_prev => add (multiply x_prev y) y

structure Integer where
  x : Natural
  y : Natural
  
def add_int (a b : Integer) : Integer :=
{
  x := add a.x b.x,
  y := add a.y b.y
}

def multiply_int (a b : Integer) : Integer :=
{
  x := add (multiply a.x b.x) (multiply a.y b.y),
  y := add (multiply a.x b.y) (multiply a.y b.x)
}

def zero: Natural := Natural.zero
def one: Natural := Natural.next zero
def two: Natural := Natural.next one 

def neg_one : Integer := { x := zero , y := one }

def main : IO Unit :=
  if (nat_eq one two) then 
    IO.println "Rejoice! One is not equal to two."
  else
    IO.println "One is equal to two. All is lost."
