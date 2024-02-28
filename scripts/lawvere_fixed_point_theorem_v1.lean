
/- lawvere's fixed point: Lean version -/
/- this is probably too trivial... -/

def point_surjective (f: A -> B): Prop :=
  forall b: Unit -> B, exists a: Unit -> A, f ∘ a = b

def weakly_point_surjective (f: A -> B -> C): Prop :=
  forall g: B -> C, exists a: A, forall b: B, (f a) b = g b

def fixed_point_property (A: Type): Prop :=
  forall f: A -> A, exists a: Unit -> A, f ∘ a = a

theorem lawvere (Y: Type):
  (exists A: Type, exists g: A -> A -> Y,
  weakly_point_surjective g) -> fixed_point_property Y :=
  sorry
