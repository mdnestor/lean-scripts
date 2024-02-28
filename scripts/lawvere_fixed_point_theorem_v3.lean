
/- Cartesian closed category -/
structure CCC where
  obj: Type
  hom (_ _: obj): Type

  id (x: obj): hom x x
  comp (f: hom x y) (g: hom y z): hom x z

  left_id (f: hom x y): comp (id x) f = f
  right_id (f: hom x y): comp f (id y) = f

  assoc (f: hom x y) (g: hom y z) (h: hom z w): comp f (comp g h) = comp (comp f g) h

  prod (x y: obj): obj
  unit: obj

  proj1 (x y: obj): hom (prod x y) x
  proj2 (x y: obj): hom (prod x y) y

  /- product properties -/

  exp (x y: obj): obj
  eval (x y: obj): hom (prod (exp x y) x) y
  /- exponential properties -/

def curry {C: CCC} {x y: C.obj} (f: C.hom x y): C.hom C.unit (C.exp x y) := sorry
def uncurry {C: CCC} {x y: C.obj} (f: C.hom C.unit (C.exp x y)): C.hom x y := sorry

def point_surjective (C: CCC) (x y: C.obj) (f: C.hom x y): Prop :=
  forall g: C.hom C.unit y,
  exists h: C.hom C.unit x,
  C.comp h f = g

def weakly_point_surjective {C: CCC} {x y z: C.obj} (f: C.hom x (C.exp y z)): Prop :=
  forall g: C.hom y z,
  exists x: C.hom C.unit x,
  forall h: C.hom C.unit y,
  C.comp h (uncurry (C.comp x f)) = C.comp h g

def fixed_point_property {C: CCC} (x: C.obj) : Prop :=
  forall f: C.hom x x,
  exists g: C.hom C.unit x,
  C.comp g f = g

theorem lawvere_fixed_point_theorem {C: CCC} (x: C.obj):
  (exists y: C.obj, exists f: C.hom y (C.exp y x),
  weakly_point_surjective f) -> fixed_point_property x := sorry
