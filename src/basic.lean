import data.set

def op (β α) := (β → α) → α

def π {β α} (i) : op β α :=
λ x, x i

-- Signature
-- F : a set of operation symbols
-- ρ : returns the arity of a given operation symbol
structure signature :=
mk :: (F : Type*) (ρ : F → Type*)

section
parameter (S : signature)

--def F := S.F
-- def ρ := S.ρ 

-- Defines the interpretation of an algebra on the carrier α
def algebra_on (α : Type*) := Π f, op (S.ρ f) α   

-- This is called `algebra_on` since an algebra is fully
-- specified by its (Cayley) operation tables. An inhabitant 
-- of `algebra_on` assigns to each op symbol f : F, of 
-- arity `α = S.ρ f`, an interpretation of f, that is, 
-- a function of type (α → υ) → υ.

-- An algebra pairs a carrier with an interpretation of the op symbols
def algebra :=
psigma algebra_on

instance alg_univ : has_coe_to_sort algebra :=
⟨_, psigma.fst⟩

instance alg_ops : has_coe_to_fun algebra :=
⟨_, psigma.snd⟩

end

section
parameters {S : signature} {α : Type*} {β : Type*} {A : algebra S} {B : algebra S} 

def is_subalgebra {α} (A : algebra_on S α) {β : set α} (B : algebra_on S β) :=
∀ f b, ↑(B f b) = A f ↑b

def homomorphic (h : A → B) := ∀ f a, h (A f a) = B f (h ∘ a)

-- more explicitly, 
-- def homomorphic {A B : algebra S} (h : A → B) := 
-- ∀ (f : S.F) (a : (S.ρ f) → A.fst) , h (A f a) = B f (h ∘ a)

def rel_on_A := A → A → Prop

def rel_on_tuples_of_A := (β → α) → (β → α) → Prop

-- A relation is compatible with A iff it is preserved by the ops of A
def compatible (r: A → A → Prop) : Prop := 
  ∀ (f : S.F) (a : S.ρ f → A.fst) (b : S.ρ f → A.fst), 
  ∀ i, r (a i) (b i) → r (A f a) (A f b)

-- A congruence relation on A is a compatible equivalence relation
def congruence (r: A → A → Prop) : Prop := equivalence r ∧ compatible r

def kernel (f : A → B) : A → A → Prop := λ a a', f a = f a'


lemma cong_iff_hom_ker (r :  A → A → Prop) :
congruence r ↔ ∃ h : A → B, homomorphic h ∧ ((kernel h) = r) := sorry

def image (f : A → B) : set B := λ b, ∃ a, f a = b

def ker (f : α → β) : α → α → Prop := λ a a', f a = f a'


end
