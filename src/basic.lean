import init.function

import data.seq
import data.function

open seq (map) (all)
open function (op) (restrict)

open psigma (fst) (snd)

-- Definition/s 1.1

def signature :=
psigma (λ F, F → ℕ)

instance sig_funsym : has_coe_to_sort signature :=
⟨_, fst⟩

instance sig_arity : has_coe_to_fun signature :=
⟨_, snd⟩

section
parameter (S : signature)

def algebra_on (α) :=
Π f, op α (S f)

def algebra :=
psigma algebra_on

instance alg_univ : has_coe_to_sort algebra :=
⟨_, fst⟩

instance alg_interp : has_coe_to_fun algebra :=
⟨_, snd⟩

end

section
parameter {S : signature}

-- Definition/s 1.2

def is_subalgebra {α} (A : algebra_on S α) {β : set α} (B : algebra_on S β) :=
∀ f b, ↑(B f b) = restrict (A f) β b

def homomorphic {A B : algebra S} (h : A → B) :=
∀ f a, h (A f a) = B f (map h a)

-- Definition 1.8

def is_subuniverse {α} (β : set α) (A : algebra_on S α) :=
∀ f b, restrict (A f) β b ∈ β

end
