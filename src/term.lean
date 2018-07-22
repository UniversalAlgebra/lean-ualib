import basic

import data.seq
import order.bounded_lattice

open seq (map) (reduce) (all)
open lattice



-- The next few structures are direct translations of Andrej Bauer's Coq code
-- at https://gist.github.com/andrejbauer/3cc438ab38646516e5e9278fdb22022c

structure OpSignature :=
(operation : Type)
(arity : operation → Type)

structure OpAlgebra (S : OpSignature) :=
(carrier : Type)
(op : ∀ o : S.operation, ((S.arity o) → carrier) → carrier)

structure Hom {S : OpSignature} (A : OpAlgebra S) (B : OpAlgebra S) :=
(map : A.carrier → B.carrier) -- the underlying map
(op_commute : ∀ (o : S.operation) (args : S.arity o → A.carrier),
map (A.op o args) = B.op o (λ x, map (args x)))

inductive termtree (S : OpSignature) (X : Type) : Type
| generator : X → termtree
| node : ∀ (o : S.operation), (S.arity o → termtree) → termtree

#check termtree

def Free (S : OpSignature) (X : Type) : OpAlgebra S :=
OpAlgebra.mk (termtree S X) termtree.node

#print Free

section free_is_free

variables (S : OpSignature) (X : Type) (A : OpAlgebra S) (h : X → A.carrier)

-- That's all I have working so far...

/- def induced_map : (termtree S X) → A.carrier
| (generator x) := h x
| (node o arg) := op A o (λ i, induced_map (arg i))
 -/

