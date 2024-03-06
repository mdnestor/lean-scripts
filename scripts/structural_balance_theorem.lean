/-
Harary (1953) proved the following theorem:
Let G be a simple undirected graph (every pair of nodes is either connected or not).
Denote x ~ y if x is connected to y and x ≁ y otherwise.
Note that for every 3 nodes x, y, z, there can be either 0, 1, 2, or 3 edges between them in total.
Call x, y, z "locally balanced" if the total number of edges between them is either 1 or 3.
Define G to be (globally) balanced if every 3 nodes are locally balanced. 
Define G to be bipartite complete if it can be partitioned into two complete subgraphs which share no edges.
The balance theorem says that G is balanced iff. it is bipartite complete.

Proof: First, assume G is bipartite complete. We want to show G is globally balanaced.
Let x, y, and z be any 3 nodes, and it suffices to show x, y, z are locally balanced.
Case 1. x ~ y and x ~ z. Then bipartite complete implies y ~ z implies locally balanced.
Case 2. x ~ y and x ≁ z. Then bipartite complete implies y ≁ z implies locally balanced.
Case 3. x ≁ y and x ~ z. Then bipartite complete implies y ≁ z implies locally balanced.
Case 4. x ≁ y and x ≁ z. Then bipartite complete implies y ~ z implies locally balanced.
In each case x, y, z are locally balanced, so G is globally balanced.

Next, assume G is globally balanced.
To show G is bipartite complete, let x be an arbitrary node, let A be the set of neighbors of x and let B = G \ A.
We will now show G is bipartite complete by showing the following hold:
Case 1. y ∈ A and z ∈ A implies (x ∼ y) ∧ (x ∼ z) implies (y ∼ z). 
Case 2. y ∈ A and z ∈ B implies (x ∼ y) ∧ (x ≁ z) implies (y ≁ z).
Case 3. y ∈ B and z ∈ B implies (x ≁ y) ∧ (x ≁ z) implies (y ∼ z).
Therefore G is bipartite complete.

References:
1 "On the notion of balance of a signed graph" by Frank Harary (1953): https://doi.org/10.1307/MMJ%2F1028989917
2 "Networks, Crowds, and Markets: Reasoning about a Highly Connected World" by David Easley and Jon Kleinberg (2010), section 5.2: https://www.cs.cornell.edu/home/kleinber/networks-book/networks-book-ch05.pdf
3 "Signed graph" on Wikipedia: https://en.wikipedia.org/wiki/Signed_graph
4 "Balance theory" on Wikipedia: https://en.wikipedia.org/wiki/Balance_theory
5 "Network Mathematics and Rival Factions" by PBS Infinite Series (2017): https://www.youtube.com/watch?v=qEKNFOaGQcc
-/

structure Graph where
  node: Type
  edge: node → node → Bool
  symmetric: ∀ x y: node, edge x y ↔ edge y x

def three_complete {G: Graph} (x y z: G.node): Prop :=
  G.edge x y ∧ G.edge y z ∧ G.edge x z

def two_connected {G: Graph} (x y z: G.node): Prop :=
  (  G.edge x y ∧ ¬ G.edge y z ∧ ¬ G.edge x z) ∨ /- x y alliance excluding z -/
  (¬ G.edge x y ∧   G.edge y z ∧ ¬ G.edge x z) ∨ /- y z alliance excluding x -/
  (¬ G.edge x y ∧ ¬ G.edge y z ∧   G.edge x z)   /- x z alliance excluding y -/

def locally_balanced {G: Graph} (x y z: G.node): Prop :=
  three_complete x y z ∨ two_connected x y z

def balanced (G: Graph): Prop := ∀ x y z: G.node, locally_balanced x y z

def bipartite_complete (G: Graph): Prop :=
  ∃ f: G.node → Bool, ∀ x y: G.node, G.edge x y ↔ f x = f y

def func {G: Graph} (h: bipartite_complete G): G.node → Bool :=
  sorry

theorem func_fact2 {h: bipartite_complete G} {x y: G.node} (h1: (func h) x = (func h) y): G.edge x y = true := sorry

theorem func_fact3 {h: bipartite_complete G} {x y: G.node} (h1: (func h) x ≠ (func h) y): G.edge x y = false := sorry

theorem lemma1 (G: Graph) (x y z: G.node) (h: balanced G): (G.edge x y) ∧ (G.edge x z) -> G.edge y z := sorry

theorem lemma2 (G: Graph) (x y z: G.node) (h: balanced G): (¬ G.edge x y) ∧ (¬ G.edge x z) -> G.edge y z := sorry


theorem BalancedImpliesBipartiteComplete (G: Graph): balanced G → bipartite_complete G := by
  intro h
  rw [bipartite_complete]
  have x0: G.node := sorry
  have f: G.node → Bool := fun x => G.edge x x0
  exists f
  intro x y
  apply Iff.intro
  intro h1
  match f x with
  | true => {
    have h2: f y = true := sorry
    rw [h2]
  }
  | false => {
    have h2: f y = false := sorry
    rw [h2]
  }
  intro h1
  match f x with
  | true => {
    have h2: f y = true := sorry
    sorry
  }
  | false => sorry

theorem BipartiteCompleteImpliesBalanced (G: Graph): bipartite_complete G → balanced G := by
  intro h
  rw [balanced]
  intro x y z
  rw [locally_balanced]
  by_cases h1: (func h) x
  by_cases h2: (func h) y
  by_cases h3: (func h) z
  apply Or.inl
  rw [three_complete]
  apply And.intro
  have h4: (func h) x = (func h) y := by rw [h1, h2]
  apply func_fact2 h4
  apply And.intro
  have h4: (func h) y = (func h) z := by rw [h2, h3]
  apply func_fact2 h4
  have h4: (func h) x = (func h) z := by rw [h1, h3]
  apply func_fact2 h4
  apply Or.inr
  rw [two_connected]
  simp
  apply Or.inl
  apply And.intro
  have h4: (func h) x = (func h) y := by rw [h1, h2]
  apply func_fact2 h4
  apply And.intro
  have h4: (func h) y ≠ (func h) z := sorry
  apply func_fact3 h4
  have h4: (func h) x ≠ (func h) z := sorry
  apply func_fact3 h4
  apply Or.inr
  rw [two_connected]
  simp
  apply Or.inr
  by_cases h3: func h z
  apply Or.inr
  sorry
  apply Or.inl
  sorry
  by_cases h2: (func h) y
  by_cases h3: (func h) z
  apply Or.inr
  rw [two_connected]
  apply Or.inr
  simp
  apply Or.inl
  apply And.intro
  have h4: (func h) x ≠ (func h) y := sorry
  apply func_fact3 h4
  apply And.intro
  have h4: (func h) y = (func h) z := by rw [h2, h3]
  apply func_fact2 h4
  have h4: (func h) x ≠ (func h) z := sorry
  apply func_fact3 h4
  apply Or.inr
  rw [two_connected]
  simp
  apply Or.inr
  apply Or.inr
  apply And.intro
  have h4: (func h) x ≠ (func h) y := sorry
  apply func_fact3 h4
  apply And.intro
  have h4: (func h) y ≠ (func h) z := sorry
  apply func_fact3 h4
  have h4: (func h) x = (func h) z := sorry
  apply func_fact2 h4
  by_cases h3: func h z
  apply Or.inr
  rw [two_connected]
  simp
  apply Or.inl
  apply And.intro
  have h4: (func h) x = (func h) y := sorry
  apply func_fact2 h4
  apply And.intro
  have h4: (func h) y ≠ (func h) z := sorry
  apply func_fact3 h4
  have h4: (func h) x ≠ (func h) z := sorry
  apply func_fact3 h4
  apply Or.inl
  rw [three_complete]
  apply And.intro
  have h4: (func h) x = (func h) y := sorry
  apply func_fact2 h4
  apply And.intro
  have h4: (func h) y = (func h) z := sorry
  apply func_fact2 h4
  have h4: (func h) x = (func h) z := sorry
  apply func_fact2 h4

theorem BalanceTheorem (G: Graph): balanced G ↔ bipartite_complete G := by
  apply Iff.intro
  exact BalancedImpliesBipartiteComplete G
  exact BipartiteCompleteImpliesBalanced G
