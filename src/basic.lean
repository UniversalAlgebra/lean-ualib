import data.set2

structure signature :=
mk :: (F : Type) (ρ : F → Type)


section
parameter (S : signature)

-- Defines the interpretation of an algebra on the carrier α
def algebra_on (α) :=
Π f, (S.ρ f → α) → α

-- An algebra pairs a carrier with an interpretation
def algebra := 
psigma algebra_on

instance alg_univ : has_coe_to_sort algebra :=
⟨_, psigma.fst⟩


instance alg_ops : has_coe_to_fun algebra := 
⟨_, psigma.snd⟩


end

section
parameter {S : signature}

def is_subalgebra {α} (A : algebra_on S α) {β : set α} (B : algebra_on S β) :=
∀ f b, ↑(B f b) = A f ↑b

def homomorphic {A B : algebra S} (h : A → B) :=
∀ f a, h (A f a) = B f (h ∘ a)

end
