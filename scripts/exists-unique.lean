def exists_unique (T: Type) (f: T -> Prop): Prop :=
  (exists x: T, f x) ∧ (forall x y: T, (f x) ∧ (f y) -> (x = y))
