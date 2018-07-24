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

inductive term {S : OpSignature} (X : Type) : Type
| gen : X → term
| node : ∀ (o : S.operation), (S.arity o → term) → term

#check term

def Free (S : OpSignature) (X : Type) : OpAlgebra S := 
⟨@term S X, @term.node S X⟩ -- ⟨ carrier , operations ⟩ 

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
⟨induced_map S A X h,          -- the function
  (assume (o: S.operation)     -- proof that the function preserves structure
  (args : S.arity o → (Free S X).carrier), rfl)⟩  

-- Theorem (Uniqueness): The homomorphism in the previous theorem is unique.
theorem from_free_unique (f g : Hom (Free S X) A) :
(∀ (x : X), f.map (term.gen x) = g.map (term.gen x)) → 
  ∀ (t : @term S X), f.map t = g.map t := 
assume h1: (∀ (x : X), (f.map (term.gen x) = g.map (term.gen x))),
assume (t : @term S X), 
show (f.map t = g.map t), from
begin 
  induction t,
  case term.gen : {simp [h1]},
  case term.node : o args ih { 
    show f.map (term.node o args) = g.map (term.node o args), from 
    calc f.map (term.node o args) = term.node o (f.map ∘ args)  : by rw [f.op_commute]
                              ... = term.node o (g.map ∘ args)  : by rw [ih]
                              ... = f.map (term.node o args) : by rw [g.op_commute]
  }
end



end free_is_free
