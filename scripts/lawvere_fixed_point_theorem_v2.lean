
/- lawvere's fixed point: v2 ... -/

def point_surjective (f: A -> B): Prop :=
  forall b: Unit -> B, exists a: Unit -> A, f ∘ a = b

def weakly_point_surjective (f: A -> B -> C): Prop :=
  forall g: B -> C, exists a: A, forall b: B, (f a) b = g b

def fixed_point_property (A: Type): Prop :=
  forall f: A -> A, exists a: Unit -> A, f ∘ a = a

theorem lawvere (Y: Type):
  (exists A: Type, exists g: A -> A -> Y,
  weakly_point_surjective g) -> fixed_point_property Y :=
  sorry

universe u v

structure Cat where
  obj: Type u
  hom (x y: obj) : Type v
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

/- Lets define a Cartesian closed category! -/
structure CartesianCat extends Cat where
  unit: obj
  prod (_ _: obj): obj
  exp (_ _: obj): obj
  proj1 (A B: obj): hom (prod A B) A
  proj2 (A B: obj): hom (prod A B) B
  eval (A B: obj): hom (prod (exp A B) A) B
  unit_is_terminal: forall x: obj, forall f g: hom x unit, f = g
  prod_prop (A B: obj): forall x: obj, forall f1: hom x A, forall f2: hom x B, exists f: hom x (prod A B), (f1 = comp f (proj1 A B)) ∧ (f2 = comp f (proj2 A B))
