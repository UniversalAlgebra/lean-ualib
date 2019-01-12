/-lean-ualib: relation.lean
  Author: William DeMeo <williamdemeo@gmail.com>
  Date: 2018 November 30

  References: 
  [1] Avigad, et al. Logic and Proof.

  Copyright (c) 2018 William DeMeo
  See LICENSE file: https://github.com/UniversalAlgebra/lean-ualib/blob/master/LICENSE
-/

namespace ualib_relation
  variable {A : Type}

  def reflexive (R : A → A → Prop) : Prop := ∀ {x}, R x x
  def symmetric (R : A → A → Prop) : Prop := ∀ {x y}, R x y → R y x
  def antisymmetric (R : A → A → Prop) : Prop := ∀ {x y}, R x y → R y x → x = y
  def transitive (R : A → A → Prop) : Prop := ∀ {x y z}, R x y → R y z → R x z

  -- Usage:
  variable R : A → A → Prop
  example (h : reflexive R) (x : A) : R x x := h
  example (h : symmetric R) (x y : A) (h1 : R x y) : R y x := h h1
  example (h : antisymmetric R) (x y : A) (h1 : R x y) (h2 : R y x) : x = y := h h1 h2
  example (h : transitive R) (x y z : A) (h1 : R x y) (h2 : R y z) : R x z := h h1 h2
  
  example (h₁ : irreflexive R) (h₂ : transitive R) : ∀ x y, R x y → ¬ R y x :=
  assume x y (h₃ : R x y), assume h₄ : R y x, 
  have h₅ : R x x, from h₂ h₃ h₄,
  have h₆ : ¬ R x x, from h₁ x, show false, from h₆ h₅

end ualib_relation


namespace ualib_equivalence
  section
    def refl {α : Type} (r : α → α → Prop) : Prop := ∀ {a}, r a a
    def trans {α : Type} (r : α → α → Prop) : Prop := ∀ {a b c}, r a b → r b c → r a c
    def preorder {α : Type} (r : α → α → Prop) : Prop := refl r ∧ trans r
    def antisymm {α : Type} (r : α → α → Prop) : Prop := ∀ {a b}, r a b → r b a → a = b
    def symm {α : Type} (r : α → α → Prop) : Prop := ∀ {a b}, r a b → r b a
    def equiv {α : Type} (r : α → α → Prop) : Prop := preorder r ∧ symm r

    parameters {A : Type}
    parameter R : A → A → Prop

    local infix ≈ := R

    def transymm (R: A → A → Prop) : Prop := ∀ {a b c}, a ≈ b ∧ c ≈ b → a ≈ c

    example (h₁ : refl R) (h₂ : transymm R) :
    (∀ a b, a ≈ b → b ≈ a) ∧ (∀ a b c, a ≈ b ∧ b ≈ c → a ≈ c) :=
    have h₃ : ∀ a b, a ≈ b → b ≈ a, from 
      assume a b (h: a ≈ b), 
      have b ≈ b ∧ a ≈ b, from and.intro h₁ h,
      show b ≈ a, from h₂ ‹b ≈ b ∧ a ≈ b›,
    have h₄ : ∀ a b c, a ≈ b ∧ b ≈ c → a ≈ c, from 
      assume a b c (h: a ≈ b ∧ b ≈ c),
      have c ≈ b, from h₂ (and.intro h₁ h.right),
      have a ≈ b ∧ c ≈ b, from and.intro h.left ‹ c ≈ b ›, 
      show a ≈ c, from h₂ this,
    and.intro h₃ h₄ 
  end
end ualib_equivalence










-- Examples (from the Logic and Proof book?)

section 
  parameters {A : Type} (R : A → A → Prop)

  local infix ≤ := R

  example (h₁ : irreflexive R) (h₂ : transitive R) : ∀ x y, x ≤ y → ¬ y ≤ x :=
  assume x y (h₃ : x ≤ y), assume h₄ : y ≤ x,
  have h₅ : x ≤ x, from h₂ h₃ h₄,
  have h₆ : ¬ x ≤ x, from h₁ x, show false, from h₆ h₅ 

  parameters (reflR : reflexive R) (transR : transitive R) 
  parameter (antisymmR : ∀ {a b : A}, R a b → R b a → a = b)
  
  definition R' (a b : A) : Prop := a ≤ b ∧ a ≠ b

  local infix < := R'

  theorem irreflR (a : A) : ¬ a < a := assume h : a < a,
  have h₁ : a ≠ a, from and.right h,
  have h₂ : a = a, from rfl, show false, from h₁ h₂ 

  theorem transR {a b c : A} (h₁ : a < b) (h₂ : b < c) : a < c :=
  have a ≤ b, from and.left h₁, have a ≠ b, from and.right h₁,
  have b ≤ c, from and.left h₂, have b ≠ c, from and.right h₂,
  have a ≤ c, from transR ‹a ≤ b› ‹b ≤ c›,
  have a ≠ c, from assume : a = c,
    have c ≤ b, from eq.subst ‹a = c› ‹a ≤ b›,
    have b = c, from antisymmR ‹b ≤ c› ‹c ≤ b›,
    show false, from ‹b ≠ c› ‹b = c›,
  show a < c, from and.intro ‹a ≤ c› ‹a ≠ c›

end

section
  parameter A : Type
  parameter R : A → A → Prop

  variable h1 : transitive R
  variable h2 : reflexive R

  def S (x y : A) := R x y ∧ R y x

  example : reflexive S := assume x, have R x x, from h2 x,
  show S x x, from and.intro this this

  example : symmetric S := assume x y, assume h : S x y,
  have h1 : R x y, from h.left, have h2 : R y x, from h.right,
  show S y x, from ⟨h.right, h.left⟩ 
        
end


section 
  open nat
  variables n m : ℕ

  #check 0 ≤ n
  #check n < n + 1

  example : 0 ≤ n := zero_le n
  example : n < n + 1 := lt_succ_self n

  example (h : n + 1 ≤ m) : n < m + 1 :=
  have h1 : n < n + 1, from lt_succ_self n,
  have h2 : n < m, from lt_of_lt_of_le h1 h,
  have h3 : m < m + 1, from lt_succ_self m,
  show n < m + 1, from lt.trans h2 h3
  variables (A : Type) [partial_order A]
  variables a b c : A

  #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
  #check (lt_trans : a < b → b < c → a < c)
  #check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
  #check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
  #check (le_of_lt : a < b → a ≤ b)


  #check (nat.zero_le : ∀ n : ℕ, 0 ≤ n)
  #check (nat.lt_succ_self : ∀ n : ℕ, n < n + 1)
  #check (nat.le_succ : ∀ n : ℕ, n ≤ n + 1)
end

