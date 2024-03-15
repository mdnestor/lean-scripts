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

/-
Generalizations?
Yanofsky (2003) "A universal approach to self-referential paradoxes, incompleteness and fixed points" https://arxiv.org/pdf/math/0305282.pdf
Roberts (2023) "Substructural fixed-point theorems and the diagonal argument: theme and variations" https://compositionality-journal.org/papers/compositionality-5-8/pdf/
-/

def representable {A Y: Type} (g: A → A → Y) (f: A → Y): Prop :=
  ∃ a: A, f = fun a' => g a a'

def represents_all {A Y: Type} (g: A → A → Y): Prop :=
  ∀ f: A → Y, representable g f

def represents_some {A Y: Type} (g: A → A → Y): Prop :=
  ∀ t: Y → Y, representable g (fun a => t (g a a))

def wps_implies_ra {A Y: Type} (g: A → A → Y): weakly_point_surjective g → represents_all g := by
  intro h1 f
  rw [representable]
  obtain ⟨x, h2⟩ := h1 f
  exists x
  funext
  apply Eq.symm
  apply h2

def ra_implies_rs {A Y: Type} (g: A → A → Y): represents_all g → represents_some g := by
  intro h1 _
  apply h1

def wps_implies_rs {A Y: Type} (g: A → A → Y): weakly_point_surjective g → represents_some g := by
  intros
  apply ra_implies_rs
  apply wps_implies_ra
  
theorem Yanofsky: ∀ Y: Type, (∃ g: A → A → Y, represents_some g) → fixed_point_property Y := by
  intro Y h1
  rw [fixed_point_property]
  intro t
  obtain ⟨g, h2⟩ := h1
  obtain ⟨f, h3⟩: ∃ f: A → Y, ∀ a: A, f a = t (g a a) := ⟨fun a => t (g a a), by simp⟩
  obtain ⟨x, h4⟩ :=  h2 t
  have h5 : ∀ a: A, t (g a a) = g x a := sorry
  exists g x x
  apply h5
