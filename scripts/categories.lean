
structure Cat where
  obj: Type
  hom: obj -> obj -> Type
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
