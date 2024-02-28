
inductive N where
| zero: N
| next: N -> N

def N.eq (x y: N): Prop :=
  match x with
  | N.zero => match y with
    | N.zero => True
    | N.next _ => False
  | N.next x_previous => match y with
    | N.zero => False
    | N.next y_previous => N.eq x_previous y_previous

theorem N.eq_reflexive: forall x: N, N.eq x x := by
  intro x
  match x with
  | N.zero => exact by rw [eq]; simp
  | N.next x_previous => exact by rw [eq]; simp; apply N.eq_reflexive
theorem N.eq_is_symmetric: forall x y: N, N.eq x y -> N.eq y x := sorry
theorem N.eq_is_transitive: forall x y z: N, (N.eq x y) ∧ (N.eq y z) -> N.eq x z := sorry

def N.add (x y: N): N :=
  match x with
  | N.zero => y
  | N.next x_previous => N.next (N.add x_previous y)

theorem N.add.associative: forall x y z: N, N.eq (N.add x (N.add y z)) (N.add (N.add x y) z) := sorry
theorem N.add.zero: forall x: N, N.eq (N.add x N.zero) x := sorry
theorem N.add.commutative: forall x y: N, N.eq (N.add x y) (N.add y x) := sorry

def N.mul (x y: N): N :=
  match x with
  | N.zero => N.zero
  | N.next x_prev => N.add (N.mul x_prev y) y
def N.one: N := N.next N.zero

theorem N.mul.associative: forall x y z: N, N.eq (N.mul x (N.mul y z)) (N.mul (N.mul x y) z) := sorry
theorem N.mul.one: forall x: N, N.eq (N.mul x N.one) x := sorry
theorem N.mul.commutative: forall x y: N, N.eq (N.mul x y) (N.mul y x) := sorry
theorem N.distributive: forall x y z: N, N.eq (N.mul x (N.add y z)) (N.add (N.mul x y) (N.mul x z)) := srorry

def Z: Type := N × N
def Z.eq (x y: Z): Prop := N.eq (N.add x.1 y.2) (N.add x.2 y.1)

theorem Z.eq_reflexive: forall x: Z, Z.eq x x := sorry
theorem Z.eq_is_symmetric: forall x y: Z, Z.eq x y -> Z.eq y x := sorry
theorem Z.eq_is_transitive: forall x y z: Z, (Z.eq x y) ∧ (Z.eq y z) -> Z.eq x z := sorry


def N.toZ (x: N): Z := (x, N.zero)
def Z.zero: Z := N.toZ N.zero
def Z.one: Z := N.toZ N.one

def Z.add (x y: Z): Z := (N.add x.1 y.1, N.add x.2 y.2)
def Z.neg (x: Z): Z := (x.2, x.1)

def Z.mul (x y: Z): Z := (N.add (N.mul x.1 y.1) (N.mul x.2 y.2), N.add (N.mul x.1 y.2) (N.mul x.2 y.1))


def Q: Type := Z × Z
def Q.eq (x y: Q): Prop := Z.eq (Z.mul x.1 y.2) (Z.mul x.2 y.1)
/- a/b + c/d = (a*b + b*c)/ (b*d)-/
def Q.add (x y: Q): Q := (Z.add (Z.mul x.1 y.2) (Z.mul x.2 y.1), Z.mul x.2 y.2)
def Q.mul (x y: Q): Q := (Z.mul x.1 y.1, Z.mul x.2 y.2)
def Q.inv (x: Q): Q := (x.2, x.1)

def Z.toQ (x: Z): Q := (x, Z.one)
def N.toQ (x: N): Q := Z.toQ (N.toZ x)
def Q.zero: Q := Z.toQ Z.zero
def Q.one: Q := Z.toQ Z.one

theorem Q.add_associative: forall x y z: Q, Q.eq (Q.add x (Q.add y z)) (Q.add (Q.add x y) z) := sorry
theorem Q.mul_associative: forall x y z: Q, Q.eq (Q.add x (Q.add y z)) (Q.add (Q.add x y) z) := sorry
theorem Q.add_inverse: forall x: Q, ¬ (Q.eq x Q.zero) -> Q.eq (Q.mul x (Q.inv x)) Q.one := sorry
