/-
Cantor's theorem:
Let A be a set, and let P(A) be its power set.
Then every function f: A → P(A) is non-surjective.

Proof:
Suppose for a contradiction f is surjective.
Define B = {x in A | x ∉ f(x)}.
Then ∃ z ∈ A such that f(z) = B.
This yields the contradiction z ∈ B ↔ z ∉ f(z) = B.
-/

def subset (A: Type): Type := A → Prop

def surjective {A B: Type} (f: A → B): Prop := ∀ b: B, ∃ a: A, f a = b

theorem Cantor: ∀ A: Type, ∀ f: A → subset A, ¬ surjective f := by
  intro A f
  apply Not.intro
  intro h1
  obtain ⟨B, h2⟩: ∃ B: subset A, ∀ x: A, (B x → ¬ (f x) x) ∧ (¬ (f x) x → B x) := by
    exists fun x => ¬ (f x) x
    intros
    exact ⟨id, id⟩ 
  obtain ⟨z, h3⟩ := h1 B
  have h4 := h2 z
  rw [h3] at h4
  have h5 := fun x => h4.1 x x
  exact h5 (h4.2 h5)
