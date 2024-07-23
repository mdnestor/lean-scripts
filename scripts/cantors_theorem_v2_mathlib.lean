import Mathlib.Init.Set

def surjective {X Y: Type} (f: X → Y) : Prop := forall y: Y, exists x: X, f x = y

theorem Cantor (X : Type) (f: X → Set X): ¬(surjective f) := by
  apply Not.intro
  intro h0
  let S: Set X := (fun x => x ∉ (f x))
  obtain ⟨x0, h1⟩ := h0 S
  have h2: (x0 ∈ S) ↔ (x0 ∉ (f x0)) := by rfl
  rw [h1] at h2
  have h3: (x0 ∉ S) := (fun x => h2.1 x x)
  exact h3 (h2.2 h3)
