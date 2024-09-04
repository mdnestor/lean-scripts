
-- categories of nets https://arxiv.org/pdf/2101.04238

import Mathlib.Data.Multiset.Basic
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

class PreNet where
  specie: Type
  trans: Type
  source: transition → List specie
  target: transition → List specie

class PreNet.map (P1 P2: PreNet) where
  smap: P1.specie → P2.specie
  tmap: P1.trans → P2.trans
  h1: (List.map smap) ∘ P1.source = P2.source ∘ tmap
  h2: (List.map smap) ∘ P1.target = P2.target ∘ tmap

def PreNet.id (P: PreNet): PreNet.map P P := {
  smap := fun x => x
  tmap := fun x => x
  h1 := sorry
  h2 := sorry
}

def PreNet.comp {P1 P2 P3: PreNet} (f1: PreNet.map P1 P2) (f2: PreNet.map P2 P3): PreNet.map P1 P3 := {
  smap := f2.smap ∘ f1.smap
  tmap := f2.tmap ∘ f1.tmap
  h1 := sorry
  h2 := sorry
}

instance: Category PreNet where
  Hom := PreNet.map
  id := PreNet.id
  comp := PreNet.comp

class PetriNet where
  specie: Type
  trans: Type
  source: trans → Multiset specie
  target: trans → Multiset specie

class PetriNet.map (P1 P2: PetriNet) where
  smap: P1.specie → P2.specie
  tmap: P1.trans → P2.trans
  h1: (Multiset.map smap) ∘ P1.source = P2.source ∘ tmap
  h2: (Multiset.map smap) ∘ P1.target = P2.target ∘ tmap

def PreNet.toPetriNet (P: PreNet): PetriNet := {
  specie := P.specie
  trans := P.trans
  source := Multiset.ofList ∘ P.source
  target := Multiset.ofList ∘ P.target
}

def PetriNet.id (P: PetriNet): PetriNet.map P P := {
  smap := fun x => x
  tmap := fun x => x
  h1 := sorry
  h2 := sorry
}

def PetriNet.comp {P1 P2 P3: PetriNet} (f1: PetriNet.map P1 P2) (f2: PetriNet.map P2 P3): PetriNet.map P1 P3 := {
  smap := f2.smap ∘ f1.smap
  tmap := f2.tmap ∘ f1.tmap
  h1 := sorry
  h2 := sorry
}

instance: Category PetriNet where
  Hom := PetriNet.map
  id := PetriNet.id
  comp := PetriNet.comp
