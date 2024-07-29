axiom Human: Type

axiom socrates: Human

axiom mortal: Human -> Prop

axiom humans_are_mortal: forall h: Human, mortal h

theorem socrates_is_mortal: mortal socrates := by
  exact humans_are_mortal socrates
