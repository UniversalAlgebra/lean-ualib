import basic
import data.set

open set (subset.antisymm)

section
parameters {α : Type*} {S : signature} (A : algebra_on S α)

def Sub : set (set α) :=
λ β, ∀ f (a : S.ρ f → α), (∀ x, a x ∈ β) → A f a ∈ β

def Sg (X : set α) : set α :=
⋂₀ {U ∈ Sub | X ⊆ U}

parameter (X : set α)

-- One way to make this SEGFAULT lol
inductive Y : set α
| var (x : α) : x ∈ X → Y x
| app (f : S.F) (a : S.ρ f → α) : (∀ i, Y (a i)) → Y (A f a)

theorem sg_inductive : Sg X = Y :=
have h : Y ∈ Sub, from sorry,
have l : Sg X ⊆ Y, from sorry,
have r : Y ⊆ Sg X, from sorry,
subset.antisymm l r

end
