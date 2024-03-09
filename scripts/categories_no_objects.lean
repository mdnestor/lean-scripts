structure Cat where
  map: Type
  dom: map → map
  codom: map → map
  comp (f g: map) (h: codom f = dom g): map
  dom1: ∀ f: map, dom (dom f) = dom f
  dom2: ∀ f: map, codom (dom f) = dom f
  codom3: ∀ f: map, dom (codom f) = codom f
  codom4: ∀ f: map, codom (codom f) = codom f
  id_law_left: ∀ f: map, comp (dom f) f (by apply dom2) = f
  id_law_right: ∀ f: map, comp f (codom f) (by rw [Eq.comm]; apply codom3) = f
  comp1 (f g: map) (h: codom f = dom g): dom (comp f g h) = dom f
  comp2 (f g: map) (h: codom f = dom g): codom (comp f g h) = codom g
  assoc_law (f g h: map) (h1: codom f = dom g) (h2: codom g = dom h): comp (comp f g h1) h (by rw [comp2]; exact h2) = comp f (comp g h h2) (by rw [comp1]; exact h1)

def monomorphism {C: Cat} (f: C.map): Prop :=
  ∀ g1 g2: C.map, ∀ h1: C.codom g1 = C.dom f, ∀ h2: C.codom g2 = C.dom f,
  C.comp g1 f h1 = C.comp g2 f h2 → g1 = g2

def epimorphism {C: Cat} (f: C.map): Prop :=
  ∀ g1 g2: C.map, ∀ h1: C.codom f = C.dom g1, ∀ h2: C.codom f = C.dom g2,
  C.comp f g1 h1 = C.comp f g2 h2 → g1 = g2

def isomorphism {C: Cat} (f: C.map): Prop :=
  monomorphism f ∧ epimorphism f

example (C: Cat) (f: C.map): isomorphism f ↔ ∃ g: C.map, (C.dom f = C.codom g) ∧ (C.codom f = C.dom g) ∧ (C.comp f g sorry = C.dom f) ∧ (C.comp g f sorry = C.codom f) := sorry

/- I hate this definition -/
