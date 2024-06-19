A collection of mathematical definitions and theorems written in [Lean 4](https://lean-lang.org). Most are self-contained without dependency [mathlib](https://github.com/leanprover-community/mathlib4).

Samples:
- [triangular_number.lean](./scripts/triangular_number.lean) - proof that $1+2+3+...+n = \frac{n(n+1)}{2}$ by induction.
- [cantors_theorem.lean](./scripts/cantors_theorem.lean) - proof of Cantor's theorem. Surprisingly simple!
- [category_of_monoids.lean](./scripts/category_of_monoids.lean) - definition monoids and proof they form a category.
- [noetherian-ring.lean](./scripts/noetherian-ring.lean) - definition of a Noetherian ring.

Want to tinker without installing? **Try Lean online** at [live.lean-lang.org](https://live.lean-lang.org/)!

Alternatively install [elan](https://github.com/leanprover/elan) and use `lean` from the command line:

```sh
lean example.lean
```

## Useful resources
- [Lean4 manual](https://lean-lang.org/lean4/doc/)
- [Lean4 source code](https://github.com/leanprover/lean4)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) (book)
- [Theorem Proving in Lean4](https://lean-lang.org/theorem_proving_in_lean4/) (book)
- [Lean 4 Zulip channel](https://leanprover.zulipchat.com/)
- [live.lean-lang.org](https://live.lean-lang.org/) (online IDE)
- [Mathlib4 docs](https://leanprover-community.github.io/mathlib-overview.html)
- [Mathlib4 source](https://github.com/leanprover-community/mathlib4)
