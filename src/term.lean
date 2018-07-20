import basic

import data.seq
import order.bounded_lattice

open seq (map) (reduce) (all)
open lattice

section

universes u v
parameters (X : Sort u) (S : signature.{v})

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

end
