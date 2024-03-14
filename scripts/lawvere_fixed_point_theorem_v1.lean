/-
"Diagonal arguments and cartesian closed categories" by Lawvere (1969).
http://tac.mta.ca/tac/reprints/articles/15/tr15.pdf
A simple version where we identify A^B with A → B.
Basically a generalized Cantor's theorem for types.
-/

def weakly_point_surjective (g: X → A → Y): Prop :=
  ∀ f: A → Y, ∃ x: X, ∀ a: A, (g x) a = f a

def fixed_point_property (Y: Type): Prop :=
  ∀ t: Y → Y, ∃ y: Y, t y = y

theorem Lawvere: ∀ Y: Type, (∃ g: A → A → Y, weakly_point_surjective g) → fixed_point_property Y := by
  intro Y h1
  rw [fixed_point_property]
  intro t
  obtain ⟨g, h2⟩ := h1
  obtain ⟨f, h3⟩: ∃ f: A → Y, ∀ a: A, f a = t (g a a) := ⟨fun a => t (g a a), by simp⟩
  obtain ⟨x, h4⟩ := h2 f
  exists g x x
  rw [←h3, h4]
