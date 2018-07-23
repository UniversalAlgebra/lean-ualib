import basic

import data.seq
import order.bounded_lattice

open seq (map) (reduce) (all)
open lattice



-- The next few structures are direct translations of Andrej Bauer's Coq code
-- at https://gist.github.com/andrejbauer/3cc438ab38646516e5e9278fdb22022c
--section free_term_algebra
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

inductive term {S : OpSignature} (X : Type) : Type
| gen : X → term
| node : ∀ (o : S.operation), (S.arity o → term) → term

#check term

def Free (S : OpSignature) (X : Type) : OpAlgebra S :=
OpAlgebra.mk 
  (@term S X) -- carrier 
  (@term.node S X)   -- operations

#print Free

section free_is_free
variables (S : OpSignature) (A : OpAlgebra S) 
variables (X : Type) (h : X → A.carrier) 

def induced_map : (@term S X) → A.carrier
| (term.gen x) := h x
| (term.node o args) :=  
  (A.op o) (λ (i : S.arity o), induced_map (args i))

-- Theorem (Existence): There is a homomorphism from Free S X into every 
--                      algebra of the given signature.
theorem induced_hom : Hom (Free S X) A :=
Hom.mk                      -- construct the homomorphism
  (induced_map S A X h)          -- the hom map
  (assume (o: S.operation)       -- proof that the map preserves structure
    (args : S.arity o → (Free S X).carrier), rfl) 

-- Theorem (Uniqueness): The homomorphism in the previous theorem is unique.
theorem from_free_unique (f g : Hom (Free S X) A) :
  (∀ (x : X), f.map (term.gen x) = g.map (term.gen x)) → 
      ∀ (t : @term S X), f.map t = g.map t := 
      assume h: (∀ (x : X), (f.map (term.gen x) = g.map (term.gen x))),
      assume (t : @term S X), show (f.map t = g.map t), from sorry
      --t.rec_on 
      --(assume x, show f.map (term.gen x) = g.map (term.gen x), from h x)
      --(assume n, show f.map n = g.map n, sorry)
      
  

end free_is_free
--end free_term_algebra