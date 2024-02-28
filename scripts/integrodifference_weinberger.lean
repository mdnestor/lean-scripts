/- Asymptotic spreading speed of an operator -/
def ScalarField: Type := Float -> Float
def ScalarField.zero: ScalarField := fun _ => 0
def subset (X: Type): Type := X -> Prop
def cup {X: Type} (A B: subset X): subset X := fun x => A x ∨ B x
def cap {X: Type} (A B: subset X): subset X := fun x => A x ∧ B x
axiom CompactSupport (u: ScalarField): Prop
def operator: Type := ScalarField -> ScalarField
def run (Q: operator) (u: ScalarField): Nat -> ScalarField :=
  fun n => match n with
  | Nat.zero => u
  | Nat.succ n_prev => Q ((run Q u) n_prev)
/- We need limsup, liminf, and inf and sup of a function on a subset of its domain -/
def limsup (a: Nat -> Float): Float := sorry
def liminf (a: Nat -> Float): Float := sorry
def inf (u: ScalarField) (S: subset Float): Float := sorry
def sup (u: ScalarField) (S: subset Float): Float := sorry
def interval (a b: Float): subset Float :=
  fun x => a < x ∧ x < b
def infinite_left_interval (a: Float): subset Float :=
  fun x => x < a
def infinite_right_interval (a: Float): subset Float :=
  fun x => x > a
def asFloat (x: Nat): Float := sorry
def ASS1 (Q: operator) (u0: ScalarField) (cstar: Float): Prop :=
  forall eps: Float, (0 < eps) ∧ (eps < cstar) -> limsup (fun t => sup ((run Q u0) t) (cup (infinite_left_interval (-(asFloat t)*(cstar+eps))) (infinite_right_interval ((asFloat t)*(cstar+eps))))) = 0
def ASS2 (Q: operator) (u0: ScalarField) (cstar: Float): Prop :=
  exists beta: Float, forall eps: Float, (0 < eps) ∧ (eps < cstar) ∧ (beta > 0) -> liminf (fun t => inf ((run Q u0) t) (interval (-(asFloat t)*(cstar-eps)) ((asFloat t)*(cstar-eps)))) ≥ beta
/- Asymptotic spreading speed -/
def ASS (Q: operator) (cstar: Float): Prop :=
  forall u0: ScalarField, (u0 ≠ ScalarField.zero) ∧ (CompactSupport u0) -> (ASS1 Q u0 cstar) ∧ (ASS2 Q u0 cstar)

theorem ASS.unique (Q: operator): forall c1 c2: Float, ASS Q c1 ∧ ASS Q c2 -> c1 = c2 := sorry

/- Theorem 5.1 in Lutscher 2019 -/
/- first need to list conditions -/
def translate (u: ScalarField) (a: Float): ScalarField :=
  fun x => u (x - a)
def translation_invariant (Q: operator): Prop :=
  forall u: ScalarField, forall a: Float, Q (translate u a) = translate (Q u) a
def const (a: Float): ScalarField :=
  fun _ => a
def ScalarField.lt (u v: ScalarField): Prop :=
  forall x: Float, u x < v x
def ScalarField.leq (u v: ScalarField): Prop :=
  forall x: Float, u x ≤ v x
def fixedpoint0 (Q: operator): Prop :=
  Q (const 0) = const 0
def fixedpoint1 (Q: operator): Prop :=
  Q (const 1) = const 1
def fixedpoint.lt (Q: operator): Prop :=
  forall a: Float, (0 < a) ∧ (a < 1) -> ScalarField.lt (const a) (Q (const a))
def monotone (Q: operator): Prop :=
  forall u v: ScalarField, ScalarField.leq u v -> ScalarField.leq (Q u) (Q v)
def ConvergesPointwise (a: Nat -> ScalarField) (u: ScalarField): Prop := sorry
def ConvergesUniformlyOnCompactSubsets (a: Nat -> ScalarField) (u: ScalarField): Prop := sorry
def continuity (Q: operator): Prop :=
  forall a: Nat -> ScalarField, forall f: ScalarField, ConvergesUniformlyOnCompactSubsets a f -> ConvergesPointwise (fun n => Q (a n)) (Q f)
def compactness (Q: operator): Prop := sorry

theorem Weinberger (Q: operator):
  translation_invariant Q ∧ fixedpoint0 Q ∧ fixedpoint1 Q ∧ fixedpoint.lt Q ∧ monotone Q ∧ continuity Q ->
  exists cstar: Float, cstar > 0 ∧ ASS Q cstar :=
  sorry

/- What is a traveling wave? -/
def traveling_wave (Q: operator) (u: ScalarField) (c: Float): Prop := Q u = translate u c
axiom has_limits_at_infinity (u: ScalarField): Prop
def left_limit (u: ScalarField) (h: has_limits_at_infinity u): Float := sorry
def right_limit (u: ScalarField) (h: has_limits_at_infinity u): Float := sorry

theorem WeinbergerTravelingWave (Q: operator):
  translation_invariant Q ∧ fixedpoint0 Q ∧ fixedpoint1 Q ∧ fixedpoint.lt Q ∧ monotone Q ∧ continuity Q ∧ compactness Q ->
  exists cstar: Float, ASS Q cstar ∧ forall c: Float, c ≥ cstar ↔ exists u: ScalarField, exists h: has_limits_at_infinity u, traveling_wave Q u c ∧ left_limit u h = 1 ∧ right_limit u h = 0 := sorry

/- There is another version of asymptotic spreading speed -/
def ASS1.v2 (Q: operator) (u0: ScalarField) (cstar: Float): Prop :=
  forall eps: Float, (0 < eps) ∧ (eps < cstar) -> limsup (fun t => sup ((run Q u0) t) (cup (infinite_left_interval (-(asFloat t)*(cstar+eps))) (infinite_right_interval ((asFloat t)*(cstar+eps))))) = 0
def ASS2.v2 (Q: operator) (u0: ScalarField) (cstar: Float): Prop :=
  exists beta: Float, forall eps: Float, (0 < eps) ∧ (eps < cstar) ∧ (beta > 0) -> liminf (fun t => inf ((run Q u0) t) (interval (-(asFloat t)*(cstar-eps)) ((asFloat t)*(cstar-eps)))) ≥ beta
/- Asymptotic spreading speed -/
def ASS.v2 (Q: operator) (cstar: Float): Prop :=
  forall u0: ScalarField, (u0 ≠ ScalarField.zero) ∧ (CompactSupport u0) -> (ASS1 Q u0 cstar) ∧ (ASS2 Q u0 cstar)
/- Todo figure out equation 5.33 -/
