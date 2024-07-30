
-- A semiautomaton consists of a state set, input set, and transition map
structure Semiautomaton where
  state: Type
  input: Type
  update: input → state → state

-- run takes a list of inputs and returns the corresponding state → state map
def run {M: Semiautomaton} (inputs: List M.input): M.state → M.state :=
  match inputs with
  | [] => fun s => s
  | head :: tail => fun s => M.update head (run tail s)

-- appending lists of inputs corresponds to composing run maps
theorem semiautomaton_append_compose (M: Semiautomaton) (inputs0 inputs1: List M.input): run (List.append inputs0 inputs1) = Function.comp (run inputs1) (run inputs0) := by
  funext s
  induction inputs1 with
  | nil =>
    simp [run, List.append, Function.comp]
  | cons head tail ih =>
    sorry

-- the transition monoid
structure Monoid where
  elt: Type
  op: elt → elt → elt
  unit: elt
  assoc: ∀ x y z: elt, op (op x y) z = op x (op y z)
  unit_left: ∀ x: elt, op unit x = x
  unit_right: ∀ x: elt, op x unit = x

structure MonoidAction (M: Monoid) (X: Type) where
  func: M.elt → X → X
  preserve: ∀ m1 m2: M.elt, ∀ x: X, func m1 (func m2 x) = func (M.op m1 m2) x

def FreeMonoid (A: Type): Monoid := {
  elt := List A
  op := List.append
  unit := []
  assoc := sorry
  unit_left := sorry
  unit_right := sorry
}

-- every semiautomaton corresponds to the action of the free monoid on its inputs acting on its state
def InputMonoid (M: Semiautomaton): MonoidAction (FreeMonoid M.input) M.state := {
  func := fun inputs s => run inputs s
  preserve := by
    intro inputs1 inputs2 s
    simp
    sorry
}

-- given states s0 and s1, s0 can reach s1 if there exists a sequence of inputs mapping s0 to s1
def reach {M: Semiautomaton} (s0 s1: M.state): Prop :=
  ∃ inputs: List M.input, run inputs s0 = s1

theorem reach_reflexive {M: Semiautomaton} (s: M.state): reach s s := by
  exists []

theorem reach_transitive {M: Semiautomaton} (s0 s1 s2: M.state): reach s0 s1 ∧ reach s1 s2 → reach s0 s2 := by
  intro ⟨h0, h1⟩
  obtain ⟨as0, h2⟩ := h0
  obtain ⟨as1, h3⟩ := h1
  exists List.append as0 as1
  rw [semiautomaton_append_compose]
  rw [Function.comp]
  rw [h2]
  
-- https://en.wikipedia.org/wiki/Preorder
structure Preorder (X: Type) where
  leq: X → X → Prop
  reflexive: ∀ x: X, leq x x
  transitive: ∀ x y z: X, (leq x y) ∧ (leq y z) → leq x z

-- the reach relation defines a preorder on the states of a semiautomaton
example (M: Semiautomaton): Preorder M.state := {
  leq := reach
  reflexive := reach_reflexive
  transitive := reach_transitive
}
