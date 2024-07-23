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

-- useful notation
infix:0 "∈" => fun {X: Type} (x: X) (S: subset X) => S x
infix:0 "∉" => fun {X: Type} (x: X) (S: subset X) => ¬(x ∈ S)

def surjective {X Y: Type} (f: X → Y) : Prop := forall y: Y, exists x: X, f x = y

theorem Cantor (X : Type) (f: X → subset X): ¬(surjective f) := by
  apply Not.intro
  intro h0
  let S: subset X := (fun x => x ∉ (f x))
  obtain ⟨x0, h1⟩ := h0 S
  have h2: (x0 ∈ S) ↔ (x0 ∉ (f x0)) := by rfl
  rw [h1] at h2
  have h3: (x0 ∉ S) := (fun x => h2.1 x x)
  exact h3 (h2.2 h3)
