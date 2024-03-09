/-
Cantor's theorem: Let A be a set, and let P(A) be its power set. Then every function f: A → P(A) is non-surjective.
Proof: Suppose for a contradiction f is surjective. Define B = {x in A | x ∉ f(x)} Then ∃ z ∈ A such that f(z) = B. This yields the contradiction z ∈ B ↔ z ∉ f(z) = B.
-/

def subset (A: Type): Type := A → Prop

def surjective {A B: Type} (f: A → B): Prop := ∀ b: B, ∃ a: A, f a = b

axiom contradiction {P: Prop} (h: ¬ P → False): P

def B (f: A → subset A): subset A := fun x => ¬ (f x) x
 
def prop2 (f: A → subset A) (h: surjective f): ∃ z: A, f z = B f := sorry

def prop3 (f: A → subset A) (h: surjective f) (z: A) (hz: f z = B f): (B f) z → ¬ (B f) z := sorry

def prop4 (f: A → subset A) (x: A): (B f) x → ¬ (f x) x := sorry

def prop5 (f: A → subset A) (x: A): ¬ (B f) x → (f x) x := sorry

def prop6 {P: Prop} (h: P → ¬ P): ¬ P := sorry

def prop7 (f: A → subset A) (x: A) (hx: f x = B f): (B f) x → ¬ (B f) x := sorry

def prop8 (f: A → subset A) (x: A) (hx: f x = B f): ¬ (B f) x := sorry

def prop9 (f: A → subset A) (x: A) (hx: f x = B f): ¬ (B f) x → (B f) x := sorry

def prop10 (f: A → subset A) (x: A) (hx: f x = B f): (B f) x := sorry

def prop11 (f: A → subset A) (x: A) (hx: f x = B f): False := sorry

theorem Cantor: ∀ A: Type, ∀ f: A → subset A, ¬ surjective f := by
  intro A f
  have z: A := sorry
  have hz: f z = B f := sorry
  have hc: surjective f → False := sorry /- use i -/
  have hc2: ¬¬surjective f → False := sorry
  exact contradiction hc2
