
/- Ch. 1 of "Intro. to Theory of Computation" (3rd ed.) by Sipser -/

def subset (X: Type): Type := X → Prop

structure FiniteAutomaton (alphabet: Type) where
  state: Type
  transition: state × alphabet → state
  initial: state
  final: subset state

def run (M: FiniteAutomaton A) (string: List A): M.state :=
  string.foldl (fun s a => M.transition (s, a)) M.initial

def accept (M: FiniteAutomaton A) (string: List A): Prop :=
  M.final (run M string)

def reject (M: FiniteAutomaton A) (string: List A): Prop :=
  ¬ (accept M string)

def language_of (M: FiniteAutomaton A): subset (List A) :=
  fun string => accept M string

def Language (alphabet: Type): Type := subset (List alphabet)

def regular (L: Language A): Prop :=
  ∃ M: FiniteAutomaton A, language_of M = L

/- define the union, concatenation, and star of languages -/
def union (L1: Language A1) (L2: Language A2): Language (Sum A1 A2) :=
  fun string => sorry

def concat (L1: Language A1) (L2: Language A2): Language (Sum A1 A2) :=
  fun string => sorry

def star (L: Language A): Language (List A) :=
  fun string => sorry

def star2 (L: Language A): Language A :=
  fun string => sorry

structure NondeterministicFiniteAutomaton (alphabet: Type) where
  state: Type
  transition: state × alphabet → subset state
  initial: state
  final: subset state

def NFA.run (M: NondeterministicFiniteAutomaton A) (string: List A): subset M.state :=
  sorry

def NFA.accept (M: NondeterministicFiniteAutomaton A) (string: List A): Prop :=
  ∃ s: M.state, (NFA.run M string) s ∧ M.final s

def NFA.reject (M: NondeterministicFiniteAutomaton A) (string: List A): Prop :=
  ¬ (NFA.accept M string)

def NFA.language_of (M: NondeterministicFiniteAutomaton A): subset (List A) :=
  fun string => NFA.accept M string

theorem equivalence (M: NondeterministicFiniteAutomaton A): ∃ M': FiniteAutomaton A, NFA.language_of M = language_of M' := sorry

theorem corollary (L: Language A): regular L ↔ ∃ M: NondeterministicFiniteAutomaton A, NFA.language_of M = L := sorry

/- next prove regular language are closed under all these -/
theorem union_of_regular_is_regular (L1: Language A1) (L2: Language A2) (h1: regular L1) (h2: regular L2): regular (union L1 L2) := sorry

theorem concat_of_regular_is_regular (L1: Language A1) (L2: Language A2) (h1: regular L1) (h2: regular L2): regular (concat L1 L2) := sorry

theorem star_of_regular_is_regular (L: Language A) (h: regular L): regular (star L) := sorry

/- todo: regular expressions and pumping lemma -/
