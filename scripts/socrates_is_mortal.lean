axiom Man: Type
axiom is_mortal: Man -> Prop
axiom all_men_are_mortal: forall x: Man, is_mortal x
axiom socrates: Man
theorem socrates_is_mortal: is_mortal socrates := by apply all_men_are_mortal
