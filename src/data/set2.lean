instance set_type {α} : has_coe_to_sort (set α) :=
⟨_, subtype⟩

namespace set

def sIntersection {α} (s : set (set α)) : set α := λ t, ∀ a ∈ s, t ∈ a
prefix `⋂₀`:110 := sIntersection

inductive iUnion {α I} : (I → set α) → set α
| intro (s : I → set α) (i x) : x ∈ s i → iUnion s x

prefix `⋃ᵢ`:110 := iUnion

def eq {α} {s₁ s₂ : set α} : s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ = s₂ :=
λ g h, funext (λ x, propext (iff.intro (@g x) (@h x)))

def image_in {α β} (f : α → β) (s : set β) :=
∀ x, f x ∈ s

end set