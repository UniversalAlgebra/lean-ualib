import basic

import data.seq
import order.bounded_lattice

open seq (map) (reduce) (all)
open lattice

/- section

universes u v
 
 --parameters (X : Sort u) (S : signature.{v})

inductive term : ℕ → Sort (max 1 u v)
| nullary (f : S.F) : S.ρ f = 0 → term 0
| word : X → term 0
| lift {m n} : m < n → term m → term n
| apply (f) {n} : seq (term n) (S.ρ f) → term (n + 1)

 
theorem reduce_max {α} [semilattice_sup_bot α] {n} (a : seq α n) : all a (≤ reduce (⊔) ⊥ a) :=
begin
  intro i,
  induction n with m ih,
  exact fin.elim0 i,
  admit
end

def term_algebra : algebra_on S (psigma term) :=
λ (f : S.F) t,
let n := reduce (⊔) ⊥ (map psigma.fst t) in

⟨n + 1, begin
let t' : seq (term n) (S.ρ f) := sorry,
exact term.apply f t',
end⟩
 -/



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

-- I don't have the rest working yet  
/- def induced_map : (termtree S X) → A.carrier
| (generator x) := h x
| (node o arg) := op A o (λ i, induced_map (arg i))
 -/

