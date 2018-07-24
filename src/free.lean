import basic

import data.seq
import order.bounded_lattice

open seq (map) (reduce) (all)
open lattice


section


inductive term  {S : signature} (X : Type) : Type
| var : X → term
| app : ∀ (f : S.F), (S.ρ f → term) → term

open term


def free {S : signature} (X : Type) : algebra S :=
⟨@term S X, @term.app S X⟩

#print free

variable (S : signature) --(X : Type 0)
variables (A : algebra S) (Y: Type) (g : Y → A.1)

-- Free algebra is really free: existence & uniqueness
def imap : (@free S Y) → A.1
| (term.var x) := g x
| (term.app f a) := (A f) (imap ∘ a)
--(λ (i : S.ρ f), imap (a i))

lemma imap_is_hom : homomorphic imap :=
λ f a, by rw [show @free S Y f a = app f a, from rfl,
              show imap (app f a) = A f (imap ∘ a), from rfl]

lemma hom_unique : ∀ {α β : free → A},
  homomorphic α → homomorphic β → α ∘ var = β ∘ var → α = β :=
λ _ _ hα hβ h, funext $ λ t, begin
  induction t with _ _ _ ih,
  { apply congr_fun h },
  { erw [hα, hβ, function.comp, funext ih] }
end

end











