def is_even (n : Nat) : Prop :=
  exists k : Nat, n = 2*k

theorem two_is_even : is_even 2 := by {
  rw [is_even];
  exists 1
}

theorem sum_of_even_is_even (n1 n2: Nat) (h1: is_even n1) (h2: is_even n2) : is_even (n1 + n2) :=
  by {
    rw [is_even];
    sorry
  }
