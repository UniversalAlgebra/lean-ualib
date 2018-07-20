import basic
import data.function
import data.seq
import data.set2

open function (restrict)
open seq (all)
open set (iUnion)

section
parameters {α : Type*} {S : signature} (A : algebra_on S α)

def Sub : set (set α) :=
λ β, ∀ f a, all a (∈ β) → A f a ∈ β

def Sg (X : set α) : set α :=
⋂₀ {U ∈ Sub | X ⊆ U}

parameter (X : set α)

def X' : ℕ → set α
| 0 := X
| (n + 1) := X' n ∪ {y | ∀ f a, all a (∈ X' n) ∧ y = A f a}

def Y := ⋃ᵢ X'

-- Bugs out, should probably report
/-inductive X' : ℕ → set α
| zero (x : α) : x ∈ X → X' 0 x
| inl {n : ℕ} (x : α) : x ∈ X' n → X' (n + 1) x
| inr {n : ℕ} (f : S.F) (a : seq α n) : all a (∈ X' n) → X' (n + 1) (A f a)-/

theorem sg_inductive : Sg X = Y :=
have h : Y ∈ Sub, from sorry,
have l : Sg X ⊆ Y, from begin intros y h', end,
have r : Y ⊆ Sg X, from sorry,
set.eq l r

end
