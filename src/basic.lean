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

def algebra_on (α) :=
Π f, op α (S.ρ f)

def algebra :=
psigma algebra_on

instance alg_univ : has_coe_to_sort algebra :=
⟨_, psigma.fst⟩

instance alg_interp : has_coe_to_fun algebra :=
⟨_, psigma.snd⟩

end

section
parameter {S : signature}

-- Definition/s 1.2

def is_subalgebra {α} (A : algebra_on S α) {β : set α} (B : algebra_on S β) :=
∀ f b, ↑(B f b) = restrict (A f) β b

def homomorphic {A B : algebra S} (h : A → B) :=
∀ f a, h (A f a) = B f (map h a)

end
