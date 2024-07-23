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

def subset (A : Type) : Type := A → Prop

def surjective {A B : Type} (f : A → B) : Prop := ∀ b : B, ∃ a : A, f a = b

theorem Cantor (A : Type) (f : A → subset A) : ¬ surjective f := by
  apply Not.intro
  intro h0
  let B : subset A := fun x => ¬ (f x) x
  obtain ⟨z, h1⟩ := h0 B
  have h2 : B z ↔ ¬ (f z) z := by rfl
  rw [h1] at h2
  have h3 : B z → False := fun x => h2.1 x x
  exact h3 (h2.2 h3)
