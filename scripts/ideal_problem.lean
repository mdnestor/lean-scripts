
/- all fields assumed to be real -/
structure MetricSpace where
  point: Type
  distance: point -> point -> Float
  d1: forall x: point, distance x x = 0
  d2: forall x y: point, x ≠ y -> distance x y ≠ 0
  d3: forall x y: point, distance x y = distance y x
  d4: forall x y z: point, distance x z ≤ distance x y + distance y z

def compact (M: MetricSpace): Prop := sorry

def RealMetricSpace: MetricSpace := {
  point := Float
  distance := fun x y => Float.abs (x - y)
  d1 := sorry
  d2 := sorry
  d3 := sorry
  d4 := sorry
}

structure Ring where
  element: Type
  add: element -> element -> element
  mul: element -> element -> element

/- we now need to build the real vector space-/
structure VectorSpace where
  point: Type
  add: point -> point -> point
  scale: Float -> point -> point
  zero: point
  neg: point -> point
  add_assoc: forall x y z: point, add x (add y z) = add (add x y) z
  add_comm: forall x y: point, add x y = add y x
  add_id: forall x: point, add x zero = x
  neg_id: forall x: point, add x (neg x) = zero
  scalar1: forall x: point, forall k1 k2: Float, scale k1 (scale k2 x) = scale (k1 * k2) x
  scalar2: forall x: point, scale 1 x = x
  scalar3: forall x y: point, forall k: Float, scale k (add x y) = add (scale k x) (scale k y)
  scalar4: forall x: point, forall k1 k2: Float, scale (k1 + k2) x = add (scale k1 x) (scale k2 x)

structure NormedVectorSpace where
  point: Type
  add: point -> point -> point
  scale: Float -> point -> point
  zero: point
  neg: point -> point
  add_assoc: forall x y z: point, add x (add y z) = add (add x y) z
  add_comm: forall x y: point, add x y = add y x
  add_id: forall x: point, add x zero = x
  neg_id: forall x: point, add x (neg x) = zero
  scalar1: forall x: point, forall k1 k2: Float, scale k1 (scale k2 x) = scale (k1 * k2) x
  scalar2: forall x: point, scale 1 x = x
  scalar3: forall x y: point, forall k: Float, scale k (add x y) = add (scale k x) (scale k y)
  scalar4: forall x: point, forall k1 k2: Float, scale (k1 + k2) x = add (scale k1 x) (scale k2 x)
  norm: point -> Float
  norm1: forall x: point, norm x ≥ 0
  norm2: forall x: point, norm x = 0 ↔ x = zero
  norm3: forall x: point, forall k: Float, norm (scale k x) = (Float.abs k) * (norm x)
  norm4: forall x y: point, norm (add x y) ≤ (norm x) + (norm y)

def NormToVector (X: NormedVectorSpace): VectorSpace := {
  point := X.point
  add := X.add
  scale := X.scale
  zero := X.zero
  neg := X.neg
  add_assoc := X.add_assoc
  add_comm := X.add_comm
  add_id := X.add_id
  neg_id := X.neg_id
  scalar1 := X.scalar1
  scalar2 := X.scalar2
  scalar3 := X.scalar3
  scalar4 := X.scalar4
}

def NormToMetric (X: NormedVectorSpace): MetricSpace := {
  point := X.point
  distance := fun x y => X.norm (X.add x (X.neg y))
  d1 := by {
    intro x
    simp
    sorry
  }
  d2 := by {
    intro x y
    simp
    sorry
  }
  d3 := by {
    intro x y
    simp
    sorry
  }
  d4 := by {
    intro x y z
    simp
    sorry
  }
}

structure ContinuousMap (M1 M2: MetricSpace) where
  func: M1.point -> M2.point
  ok: forall x y: M1.point, ∀ ε: Float, ∃ δ: Float, M1.distance x y < δ -> M2.distance (func x) (func y) < ε

def SpaceOfFunctions (X: MetricSpace) (h: compact X): NormedVectorSpace := {
  point := ContinuousMap X RealMetricSpace
  add := sorry
  scale := sorry
  zero := sorry
  neg := sorry
  add_assoc := sorry
  add_comm := sorry
  add_id := sorry
  neg_id := sorry
  scalar1 := sorry
  scalar2 := sorry
  scalar3 := sorry
  scalar4 := sorry
  norm := sorry
  norm1 := sorry
  norm2 := sorry
  norm3 := sorry
  norm4 := sorry
}

def asRing (X: NormedRealVectorSpace): Ring := sorry

/- an ideal of a vector space -/
def subset (T: Type): Type := T -> Prop
def subset_of {T: Type} (A B: subset T): Prop := forall x: T, A x -> B x

structure Ideal (R: Ring) where
  set: subset R.element
  subgroup1: sorry
  subgroup2: sorry
  subgroup3: sorry
  absorbing: sorry

def closed {X: MetricSpace} (S: subset X.point): Prop := sorry

def locus (X: MetricSpace) (f: ContinuousMap X RealMetricSpace): subset X.point :=
  fun x => f.func x = by rw [RealMetricSpace]; exact 0

def locus_set (X: MetricSpace) (S: subset (ContinuousMap X RealMetricSpace)): subset X.point :=
  fun x => forall f: ContinuousMap X RealMetricSpace, S f ∧ (locus X f) x

/- there is some problem of not linking up -/
theorem main (X: MetricSpace) (h1: compact X) (J: Ideal (asRing (SpaceOfFunctions X h))) (g: ContinuousMap X RealMetricSpace):
  sorry :=
  sorry
