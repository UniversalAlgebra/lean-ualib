import basic

section
parameters (S : signature) (X : Type*)

inductive term
| var     : X → term
| app (f) : (S.ρ f → term) → term

def free : algebra S :=
⟨term, term.app⟩

end

section
parameters {S : signature} (A : algebra S) (X : Type*)

open term

def free_ := free S X
def var_  := @var S X

-- Free algebra is really free: existence & uniqueness of homomorphism

section
parameter (h : X → A)

def imap : free_ → A
| (var .(S) x) := h x
-- WARNING: need to fully expand composition so Lean doesn't throw a tantrum
| (app f a)    := A f (λ x, imap $ a x)

lemma imap_is_hom : homomorphic imap :=
λ f a, show imap (app f a) = A f (imap ∘ a), from rfl

end

lemma hom_unique : ∀ {α β : free_ → A},
  homomorphic α → homomorphic β → α ∘ var_ = β ∘ var_ → α = β :=
begin
  assume (α β : free_ → A)
         (hα : homomorphic α)
         (hβ : homomorphic β)
         (h : α ∘ var_ = β ∘ var_),
  
  funext t, show α t = β t,
  
  induction t with t f a ih,

  show α (var_ t) = β (var_ t),
  { apply congr_fun h t },

  show α (app f a) = β (app f a),
  { have ih' : α ∘ a = β ∘ a, from funext ih,
    calc α (app f a) = A f (α ∘ a) : hα f a
                 ... = A f (β ∘ a) : congr_arg (A f) ih'
                 ... = β (app f a) : (hβ f a).symm }
end

end