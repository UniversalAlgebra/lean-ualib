import .basic
import data.function
import data.seq
import data.set2

open function (restrict)
open seq (all)
open set (iUnion)

section
parameter {S : signature}

def is_subuniverse {α} (A : algebra_on S α) (β : set α) :=
∀ f a, all a (∈ β) → A f a ∈ β

def Sub {α} (A : algebra_on S α) : set (set α) :=
is_subuniverse A

def Sg {α} (A : algebra_on S α) (X : set α) :=
⋂₀ {U ∈ Sub A | X ⊆ U}

parameters {α : Type*} (X : set α) (A : algebra_on S α)

def X' : ℕ → set α
| 0 := X
| (n + 1) := X' n ∪ {y | ∀ f a, all a (∈ X' n) ∧ y = A f a}

def Y := ⋃ᵢ X'

-- Bugs out, should probably report
/-inductive X' : ℕ → set α
| zero (x : α) : x ∈ X → X' 0 x
| inl {n : ℕ} (x : α) : x ∈ X' n → X' (n + 1) x
| inr {n : ℕ} (f : S.F) (a : seq α n) : all a (∈ X' n) → X' (n + 1) (A f a)-/

theorem sg_inductive : Sg A X = Y :=
have Y ∈ Sub A, from
(begin
   intros f a h,
   let h' : ∃ n, all a (∈ X' n) := sorry,
   cases h' with n h',
   apply set.iUnion.intro X' n,
   
   end),
have X ⊆ Y, from set.iUnion.intro X' 0,
have l : Sg A X ⊆ Y, from sorry,
have r : Y ⊆ Sg A X, from sorry,
set.eq l r

end
