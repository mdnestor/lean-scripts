/- Curtis-Hedlund-Lyndon theorem attempt 2 -/

def subset (X: Type): Type := X -> Prop

def finite {X: Type} (S: subset X): Prop := sorry

structure subtype {X: Type} (S: subset X) where
  x: X
  belongs: S x

def restrict_to_subtype {X Y: Type} (f: X -> Y) (S: subset X): (subtype S) -> Y := fun x => f x.x

structure Group where
  element: Type
  op: element -> element -> element
  identity: element
  inv: element -> element

def lmul {A: Type} {G: Group} (g0: G.element) (x: G.element -> A): G.element -> A := fun g => x (G.op (G.inv g0) g)

structure TopologicalSpace where
  point: Type
  openset: subset (subset point)

structure ContinuousMap (X Y: TopologicalSpace) where
  map: X.point -> Y.point

def ProdiscreteTopology (A Gelt: Type): TopologicalSpace := {
  point := Gelt -> A
  openset := sorry
}

structure CellularAutomaton (G: Group) (A: Type) where
  map: (G.element -> A) -> (G.element -> A)
  memoryset: subset G.element
  mu: (subtype memoryset -> A) -> A
  h1: finite memoryset
  h2: forall x: G.element -> A, forall g: G.element, (map x) g = mu (restrict_to_subtype (lmul (G.inv g) x) memoryset)

def equivariant {A: Type} {G: Group} (tau: (G.element -> A) -> (G.element -> A)): Prop := forall x: G.element -> A, forall g: G.element, tau (lmul g x) = lmul g (tau x)

/- Proposition 1.4.4 -/
theorem cellular_automaton_equivariant (C: CellularAutomaton G A): equivariant C.map := by
  rw [equivariant]
  intro x g
  funext g'
  rw [lmul]
  sorry

theorem cellular_automaton_continuous (C: CellularAutomaton G A): exists f: ContinuousMap (ProdiscreteTopology A G.element) (ProdiscreteTopology A G.element), f.map = C.map := sorry

theorem CurtisHedlundLyndon (A: Type) (G: Group) (tau: (G.element -> A) -> (G.element -> A)):
  (exists f: ContinuousMap (ProdiscreteTopology A G.element) (ProdiscreteTopology A G.element), f.map = tau) ∧ (equivariant tau) -> exists C: CellularAutomaton G A, C.map = tau := sorry
