/-
"Diagonal arguments and cartesian closed categories" by Lawvere (1969).
http://tac.mta.ca/tac/reprints/articles/15/tr15.pdf
A simple version where we identify A^B with A → B.
Basically a generalized Cantor's theorem for types.
-/
def weakly_point_surjective {A X Y: Type} (g: X → A → Y): Prop :=
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

/-
Generalization due to Yanofsky (2003): "A universal approach to self-referential paradoxes, incompleteness and fixed points" https://arxiv.org/pdf/math/0305282.pdf
-/

def representable {A Y: Type} (g: A → A → Y) (f: A → Y): Prop :=
  ∃ a: A, ∀ a': A, f a' = g a a'

def represents_all {A Y: Type} (g: A → A → Y): Prop :=
  ∀ f: A → Y, representable g f

/-
As Yanofsky said we only need g to be able to represent functions in the form diag;g;t for some endomorphism t.
-/

def represents_some {A Y: Type} (g: A → A → Y): Prop :=
  ∀ t: Y → Y, representable g (fun a => t (g a a))

/-
The following lemmas show "represents all" is a weaker condition than weakly point surjective.
-/

def wps_implies_ra {A Y: Type} (g: A → A → Y): weakly_point_surjective g → represents_all g := by
  intro h1 f
  rw [representable]
  obtain ⟨x, h2⟩ := h1 f
  exists x
  funext
  intro a
  apply Eq.symm
  apply h2

def ra_implies_rs {A Y: Type} (g: A → A → Y): represents_all g → represents_some g := by
  intro h1 _
  apply h1

def wps_implies_rs {A Y: Type} (g: A → A → Y): weakly_point_surjective g → represents_some g := by
  intro h
  apply ra_implies_rs
  apply wps_implies_ra
  exact h
  
theorem Yanofsky: ∀ Y: Type, (∃ g: A → A → Y, represents_some g) → fixed_point_property Y := by
  intro Y h1
  rw [fixed_point_property]
  intro t
  obtain ⟨g, h2⟩ := h1
  obtain ⟨x, h4⟩ := h2 t
  exists g x x
  apply h4

/- Proving Lawvere's theorem using Yanofsky's -/
theorem LawvereProof2: ∀ Y: Type, (∃ g: A → A → Y, weakly_point_surjective g) → fixed_point_property Y := by
  intro Y h1
  obtain ⟨g, h2⟩ := h1
  have h3: represents_some g := (wps_implies_rs g) h2
  apply Yanofsky
  exists g
