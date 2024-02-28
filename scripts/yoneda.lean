structure Cat (m n: Nat) where
  obj: Type m
  hom (x y: obj) : Type n
  id (a: obj): hom a a
  comp (f: hom a b) (g: hom b c): hom a c
  id_left (f: hom a b):
    f = comp (id a) f
  id_right (f: hom a b):
    f = comp f (id b)
  assoc (f: hom a b) (g: hom b c) (h: hom c d):
    comp f (comp g h) = comp (comp f g) h

/- Functor? Rather get functbyor! -/
structure Functer (C D: Cat m n) where
  func0: C.obj -> D.obj
  func1: C.hom x y -> D.hom (func0 x) (func0 y)
  id_preserving (x: C.obj):
    func1 (C.id x) = D.id (func0 x)
  comp_preserving (f: C.hom x y) (g: C.hom y z):
    func1 (C.comp f g) = D.comp (func1 f) (func1 g)

structure NaturalTrans {m n: Nat} {C D: Cat m n} (F G: Functer C D) where
  component (x: C.obj): D.hom (F.func0 x) (G.func0 x)
  ok (x y: C.obj) (f: C.hom x y):
    D.comp (F.func1 f) (component y) = D.comp (component x) (G.func1 f)

def Set: Cat 1 1 := {
  obj := Type,
  hom := by {intro x y; exact (x -> y)},
  id := by {intro _; exact fun x => x},
  comp := by {intro _ _ _; intro f g; exact fun x => g (f x)},
  id_left := by simp,
  id_right := by simp,
  assoc := by simp
}

def HomSet (C: Cat 1 1) (x y: C.obj): Type := by {exact C.hom x y}

def HomFunctor (C: Cat 1 1) (A: C.obj): Functer C Set := {
  func0 := by {exact fun x => HomSet C A x},
  func1 := by {intro x y; intro f; rw [HomSet, HomSet]; intro g; exact C.comp g f},
  id_preserving := by {intro x; rw [Eq.mpr]; simp; rw [Eq.mpr]; simp; sorry},
  comp_preserving := by {intro x y z f g; rw [Eq.mpr, Eq.mpr, Eq.mpr, Eq.mpr, Eq.mpr, Eq.mpr]; simp; sorry}
}
