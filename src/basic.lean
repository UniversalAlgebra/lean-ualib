import init.function

import data.seq
import data.function

open seq (map) (all)
open function (op) (restrict)

-- Definition/s 1.1

structure signature :=
mk :: (F : Sort*) (ρ : F → ℕ)

section
parameter (S : signature)

-- define the operations of the algebra
def algebra_on (α) :=
Π (f : S.F), op α (S.ρ f)  

def algebra :=  -- defines the universe and the operations ???
psigma algebra_on

instance alg_univ : has_coe_to_sort algebra :=
⟨_, psigma.fst⟩

-- ^^^^ These coersions are cool! vvvvv

instance alg_interp : has_coe_to_fun algebra :=  -- Should we call this instance `alg_ops` ?
⟨_, psigma.snd⟩

end

section
parameter {S : signature}

-- Definition/s 1.2

def is_subalgebra {α} (A : algebra_on S α) {β : set α} (B : algebra_on S β) :=
∀ f b, ↑(B f b) = restrict (A f) β b  -- this is nice

def homomorphic {A B : algebra S} (h : A → B) := -- Should we call this homomorphism ???
∀ f a, h (A f a) = B f (map h a)

end
