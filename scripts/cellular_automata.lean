
/- what are gliders in a Cellular Automata like Game of Life? -/
/- first off they are field configurations, meaning we need a domain and codomain -/

def subset (X: Type): Type := X -> Prop

def singleton {X: Type} (x0: X): subset X := fun x => x = x0

def compact (_: subset X): Prop := sorry

def neighborhood_of_influence {X Y: Type} (F: (X -> Y) -> (X -> Y)) (x: X): subset X := sorry

def local_rule {X Y: Type} (F: (X -> Y) -> (X -> Y)): Prop := forall x: X, compact (neighborhood_of_influence F x)

/- a field configuration is compact if it's nonzero on a compact set
this means we need a notion of zero in the target space -/

def support {X Y: Type} (u: X -> Y) (y0: Y): subset X := sorry

def ucompact {X Y: Type} (u: X -> Y) (y0: Y): Prop := compact (support u y0)

theorem local_rule_preserves_compact {X Y: Type} (F: (X -> Y) -> (X -> Y)) (u: X -> Y) (y0: Y) (h1: local_rule F) (h2: ucompact u y0): ucompact (F u) y0 := sorry

/- now I need translation rules -/

structure Group (T: Type) where
  op: T -> T -> T
  id: T
  inv: T -> T

theorem Group.inv_id (G: Group X): G.inv G.id = G.id := sorry

structure GroupAction (G: Group T1) (T2: Type) where
  act: T1 -> T2 -> T2
  h1: forall x: T2, act G.id x = x
  h2: forall x y: T1, forall z: T2, act (G.op x y) z = act x (act y z)
  h3: forall x: T1, forall y: T2, act x (act (G.inv x) y) = y

def transitive {X Y: Type} {G: Group X} (A: GroupAction G Y): Prop :=
  forall y1 y2: Y, exists x: X, A.act x y1 = y2

def equivariant {X Y: Type} {G: Group X} (f: Y -> Y) (A: GroupAction G Y): Prop :=
  forall x: X, forall y: Y, f (A.act x y) = A.act x (f y)

def invariant {X Y: Type} {G: Group X} (f: Y -> Y) (A: GroupAction G Y): Prop :=
  forall x: X, forall y: Y, f (A.act x y) = (f y)

def invariant_subset {X Y: Type} {G: Group X} (S: subset Y) (A: GroupAction G Y): Prop :=
  forall x: X, forall y: Y, S y -> S (A.act x y)

def smallest_containing_invariant_subset {X Y: Type} {G: Group X} (S: subset Y) (A: GroupAction G Y): subset Y :=
  fun y => exists x: X, S (A.act x y)

example {X Y: Type} {G: Group X} (A: GroupAction G Y): forall S: subset Y, invariant_subset (smallest_containing_invariant_subset S A) A := by {intro S; rw [invariant_subset]; intro x y h; sorry}

def traveling {X Y: Type} {G: Group X} (S: subset Y) (A: GroupAction G Y): subset Y :=
  fun y => exists x: X, S (A.act x y)

def fixed_point {X: Type} (f: X -> X) (x: X): Prop := f x = x

def p_periodic_point {X: Type} (f: X -> X) (x: X) (p: Nat): Prop := sorry /- f^n(x) = x -/

def periodic_point {X: Type} (f: X -> X) (x: X): Prop := exists p: Nat, p_periodic_point f x p

example {X: Type} (f: X -> X) (x: X): fixed_point f x ↔ p_periodic_point f x 1 := sorry

def minimal_period {X: Type} (f: X -> X) (x: X) (h: periodic_point f x): Nat := sorry

def glider {X Y: Type} (F: (X -> Y) -> (X -> Y)) (u: X -> Y) (y0: Y): Prop :=
  ucompact u y0 ∧ periodic_point F u

def extended_action {Z X: Type} {G: Group Z} (A: GroupAction G X) (Y: Type): GroupAction G (X -> Y) := {
  act := fun g f x => f (A.act (G.inv g) x)
  h1 := by {intro f; funext x; simp; sorry}
  h2 := by {intro g1 g2 f; funext x; simp; sorry}
  h3 := by {intro g f; funext x; simp; sorry}
}

def GliderSpace {X Y Z: Type} {G: Group Z} (A: GroupAction G X) (F: (X -> Y) -> (X -> Y)) (u: X -> Y) (y0: Y) (h: glider F u y0): subset (X -> Y) :=
  smallest_containing_invariant_subset (singleton u) (extended_action A Y)

/- Next I guess we want to look at like -/
/- decomposing u: X -> Y into connected components -/

/- we also want to look at "backwards" solutions composed of gliders as t -> -infinity -/

/- want to prove the curtis theorem -/
/- as well as my maybe original theorem, "existence at t=T and uniform random initial data implies ubiquity at t=T" -/

/- definition 1.4.1 -/

structure Group2 where
  T: Type
  op: T -> T -> T
  id: T
  inv: T -> T

structure subtype {X: Type} (S: subset X) where
  x: X
  belongs: S x

def finite {X: Type} (S: subset X): Prop := sorry

def restrict_to_subtype {X Y: Type} (f: X -> Y) (S: subset X): subtype S -> Y := fun x => f x.x

def lmul {A: Type} {G: Group2} (g0: G.T) (x: G.T -> A): G.T -> A := fun g => x (G.op (G.inv g0) g)

/- some sort of composition -/

def cellular_automaton {A: Type} {G: Group2} (F: (G.T -> A) -> (G.T -> A)): Prop := exists S: subset G.T, finite S ∧ exists mu: (subtype S -> A) -> A, forall x: G.T -> A, forall g: G.T, (F x) g = mu (restrict_to_subtype x S)

/-  we need the prodiscrete topology -/

structure TopologicalSpace (X: Type) where

/- suppose we have two types X and Y and for every y a topological space Tx on X -/

def DiscreteTopology (X: Type): TopologicalSpace X := sorry

def FFF {X Y: Type} (f: Y -> TopologicalSpace X): TopologicalSpace (X -> Y) := {

}

def ProdiscreteTopology (X Y: Type): TopologicalSpace (X -> Y) := FFF (fun _ => DiscreteTopology X)


structure TopSpace where


def is_prodiscrete_continuous (f: (X -> Y) -> (X -> Y)): Prop := sorry

def Prodiscrete (A: Type) (G: Group2): TopSpace := sorry

def equivariant2 {A: Type} {G: Group2} (tau: (G.T -> A) -> (G.T -> A)): Prop := forall x: G.T -> A, forall g: G.T, tau (lmul g x) = lmul g (tau x)

def finiteType (X: Type): Prop := sorry

theorem CurtisHedlundLyndon (A: Type) (G: Group2) (h: finiteType A) (tau: (G.T -> A) -> (G.T -> A)):
  (cellular_automaton tau) ↔ (is_prodiscrete_continuous tau) ∧ (equivariant2 tau) := sorry
