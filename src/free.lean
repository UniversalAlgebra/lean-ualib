import basic

section

parameters (S : signature) (X : Sort*)

inductive term
| word : X → term
| apply (f) : (S.ρ f → term) → term

open term

def free : algebra S :=
⟨term, apply⟩

parameters (A : algebra S) (h : X → A)

-- Free algebra is really free: existence & uniqueness

def imap : free → A
| (word .(S) x) := h x
| (apply f a)   := A f (imap ∘ a)

lemma imap_is_hom : homomorphic imap :=
λ f a, by rw [show free f a = apply f a, from rfl,
              show imap (apply f a) = A f (imap ∘ a), from rfl]

lemma hom_unique : ∀ {α β : free → A},
  homomorphic α → homomorphic β → α ∘ word = β ∘ word → α = β :=
λ _ _ hα hβ h, funext $ λ t, begin
  induction t with _ _ _ ih,
  { apply congr_fun h },
  { erw [hα, hβ, function.comp, funext ih] }
end

end