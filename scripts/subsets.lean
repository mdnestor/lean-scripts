def subset (X: Type): Type := X -> Prop

def whole (X: Type): subset X := fun _ => True
def empty (X: Type): subset X := fun _ => False
def complement {X: Type} (S: subset X): subset X := fun x => ¬ S x

example (X: Type): empty X = complement (whole X) := by funext; rw [empty, complement, whole]; simp

def cup {X: Type} (A B: subset X): subset X := fun x => A x ∨ B x
def cap {X: Type} (A B: subset X): subset X := fun x => A x ∧ B x

example (X: Type): forall S: subset X, cup S (empty X) = S := by intros; funext; rw [cup, empty]; simp
example (X: Type): forall S: subset X, cup S (whole X) = whole X := by intros; funext; rw [cup, whole]; simp
example (X: Type): forall S: subset X, cap S (empty X) = empty X := by intros; funext; rw [cap, empty]; simp
example (X: Type): forall S: subset X, cap S (whole X) = S := by intros; funext; rw [cap, whole]; simp

def image {X Y: Type} (f: X -> Y) (S: subset X): subset Y := fun y => exists x: X, S x ∧ f x = y
def preimage {X Y: Type} (f: X -> Y) (S: subset Y): subset X := fun x => S (f x)

def subsetfamily (X: Type): Type := subset (subset X)

def bigcup {X: Type} (F: subsetfamily X): subset X := fun x => exists S: subset X, F S ∧ S x
def bigcap {X: Type} (F: subsetfamily X): subset X := fun x => forall S: subset X, F S ∧ S x

example {X: Type}: forall F: subsetfamily X, F (whole X) -> bigcup F = whole X := by intros; funext; rw [bigcup, whole]; sorry
example {X: Type}: forall F: subsetfamily X, F (empty X) -> bigcap F = empty X := by intros; funext; rw [bigcap, empty]; sorry

