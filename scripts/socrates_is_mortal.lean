axiom Human: Type
axiom is_mortal: Human -> Prop
axiom all_humans_are_mortal: forall h: Human, is_mortal h
axiom socrates: Human
theorem socrates_is_mortal: is_mortal socrates := by apply all_humans_are_mortal
