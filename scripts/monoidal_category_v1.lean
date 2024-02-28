
structure Cat where
  obj: Type
  hom (x y: obj) : Type
  id (a: obj): hom a a
  comp (f: hom a b) (g: hom b c): hom a c
  id_left (f: hom a b):
    f = comp (id a) f
  id_right (f: hom a b):
    f = comp f (id b)
  assoc (f: hom a b) (g: hom b c) (h: hom c d):
    comp f (comp g h) = comp (comp f g) h

structure Functer (C D: Cat) where
  func0: C.obj -> D.obj
  func1: C.hom x y -> D.hom (func0 x) (func0 y)
  id_preserving (x: C.obj):
    func1 (C.id x) = D.id (func0 x)
  comp_preserving (f: C.hom x y) (g: C.hom y z):
    func1 (C.comp f g) = D.comp (func1 f) (func1 g)

structure NaturalTrans (F G: Functer C D) where
  component (x: C.obj): D.hom (F.func0 x) (G.func0 x)
  ok (x y: C.obj) (f: C.hom x y):
    D.comp (F.func1 f) (component y) = D.comp (component x) (G.func1 f)

def isomorphism {C: Cat} {x y: C.obj} (f: C.hom x y): Prop :=
  exists g: C.hom y x, (C.comp f g = C.id x) ∧ (C.comp g f = C.id y)

def natural_isomorphism {C D: Cat} {F G: Functer C D} (eta: NaturalTrans F G): Prop :=
  forall x: C.obj, isomorphism (eta.component x)

def ProdCat (C D: Cat): Cat := {
  obj := C.obj × D.obj,
  hom := fun (x1, y1) (x2, y2) => (C.hom x1 x2) × (D.hom y1 y2),
  id := fun (x, y) => (C.id x, D.id y),
  comp := fun (f1, g1) (f2, g2) => (C.comp f1 f2, D.comp g1 g2),
  id_left := fun (f, g) => by
    simp
    apply And.intro
    exact C.id_left f
    exact D.id_left g
  id_right := by
    intro _ _ (f, g)
    simp
    apply And.intro
    exact C.id_right f
    exact D.id_right g
  assoc := by
    simp
    intro _ _ _ _ (f1, g1) (f2, g2) (f3, g3)
    simp
    apply And.intro
    exact C.assoc f1 f2 f3
    exact D.assoc g1 g2 g3
}

def Cat.isomorphism {C: Cat} {x y: C.obj} (f: C.hom x y): Prop :=
  exists g: C.hom y x, (C.comp f g = C.id x) ∧ (C.comp g f = C.id y)

def Cat.isomorphic {C: Cat} (x y: C.obj): Prop :=
  exists f: C.hom x y, Cat.isomorphism f

structure StrictMonoidalCat extends Cat where
  prod (_ _: obj): obj
  proj1 {x y: obj}: hom (prod x y) x
  proj2 {x y: obj}: hom (prod x y) y
  unit: obj
  left_prod_unit_law (x: obj): Cat.isomorphic (prod unit x) x
  right_prod_unit_law (x: obj): Cat.isomorphic (prod x unit) x
  prod_assoc (x y z: obj): Cat.isomorphic (prod x (prod y z)) (prod (prod x y) z)
