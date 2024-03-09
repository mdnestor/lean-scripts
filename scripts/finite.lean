def finite (X: Type): Prop := ∃ L: List X, ∀ x: X, x ∈ L

example (X Y: Type) (hx: finite X) (hy: finite Y): finite (X × Y) := sorry
example (X Y: Type) (hx: finite X) (hy: finite Y): finite (X → Y) := sorry
example (n: Nat): finite (Fin n) := sorry
example: ¬ finite Nat := sorry
example: finite Bool := sorry
example: ¬ finite Prop := sorry

def injective {X Y: Type} (f: X → Y): Prop := ∀ x1 x2: X, f x2 = f x2 → x1 = x2
def surjective {X Y: Type} (f: X → Y): Prop := ∀ y: Y, ∃ x: X, f x = y
def bijective {X Y: Type} (f: X → Y): Prop := injective f ∧ surjective f

theorem t1 (X Y: Type) (f: X → Y) (h: injective f): finite Y → finite X := sorry
theorem t2 (X Y: Type) (f: X → Y) (h: surjective f): finite X → finite Y := sorry
theorem t3 (X Y: Type) (f: X → Y) (h: bijective f): finite X ↔ finite Y := by
  apply Iff.intro
  intro h1; apply t2; exact h.2; exact h1
  intro h1; apply t1; exact h.1; exact h1
