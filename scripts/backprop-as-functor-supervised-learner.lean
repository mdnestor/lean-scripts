/- https://arxiv.org/pdf/1711.10455.pdf -/

/- Definition II.1 -/
structure Learner (A B: Type) where
  param: Type
  implement: param -> A -> B
  update: param -> A -> B -> param
  request: param -> A -> B -> A

def Learner.equiv (L1 L2: Learner A B): Prop :=
  exists f: L1.param -> L2.param,
  forall p: L1.param,
  forall a: A,
  forall b: B,
  L2.implement (f p) a = L1.implement p a ∧
  L2.update (f p) a b = f (L1.update p a b) ∧
  L2.request (f p) a b = L1.request p a b

def Learner.id {A: Type}: Learner A A := {
  param := Unit,
  implement := by
    intro _ a
    exact a
  update := by
    intros
    exact ()
  request := by
    intro _ _ a
    exact a
}

def Learner.compose (L1: Learner A B) (L2: Learner B C): Learner A C := {
  param := L1.param × L2.param,
  implement := by
    intro (p1, p2) a
    exact L2.implement p2 (L1.implement p1 a)
  update := by
    intro (p1, p2) a c
    exact (
      L1.update p1 a (L2.request p2 (L1.implement p1 a) c),
      L2.update p2 (L1.implement p1 a) c
    )
  request := by
    intro (p1, p2) a c
    exact L1.request p1 a (L2.request p2 (L1.implement p1 a) c)
}

def Learner.product (L1: Learner A B) (L2: Learner C D): Learner (A × C) (B × D) := {
  param := L1.param × L2.param,
  implement := by
    intro (p1, p2) (a, c)
    exact (L1.implement p1 a, L2.implement p2 c)
  update := by
    intro (p1, p2) (a, c) (b, d)
    exact (L1.update p1 a b, L2.update p2 c d)
  request := by
    intro (p1, p2) (a, c) (b, d)
    exact (L1.request p1 a b, L2.request p2 c d)
}

def Learner.braid {A B: Type}: Learner (A × B) (B × A) := {
  param := Unit,
  implement := by
    intro _ (a, b)
    exact (b, a)
  update := by
    intros
    exact ()
  request := by
    intro _ _ (b, a)
    exact (a, b)
}

/- todo: equivalence of learners -/
/- and proof of symmetric monoidal category https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monoidal/Category.html -/

universe u
def is_equiv (T: Type u) (R: T -> T -> Prop): Prop :=
  (forall x: T, R x x) ∧
  (forall x y: T, R x y ↔ R y x) ∧
  (forall x y z: T, ((R x y) ∧ (R y z)) -> R x z)

theorem Learner.equiv.is_equiv: forall A B: Type, is_equiv (Learner A B) Learner.equiv :=
  sorry
