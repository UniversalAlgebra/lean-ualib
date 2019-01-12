/-quotient.lean -- Quotient Structures and Homomorphic Images

  Author: William DeMeo <williamdemeo@gmail.com>
  Date: 30 Nov 2018

  References
  [1] Avigad, et al, "Theorem Proving in Lean," 2018 
      url: https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf
  [2] Bergman, Clifford, "Universal algebra," CRC Press, 2012

  Copyright (c) 2018 William DeMeo  
  See LICENSE file at https://github.com/UniversalAlgebra/lean-ualib/blob/master/LICENSE
-/

import basic 
import data.fintype
universes u v

  /-Reference: Chapter 11 of Theorem Proving in Lean [1].
    Let α be any type, and let r be an equivalence relation on α. It is 
    Then the *quotient* α / r is the type of equivalence classes of α modulo r. 

    Let f : α → β be any (unary) function and let r : α → α → Prop be a binary relation on α.  
    The Lean standard library takes "f respects r" to mean the following:

    ∀ x y : α, r x y → f x = f y.
    
    But, for us, it seems the consequent f x = f y is unnecessarily strong.  
    Instead, we would prefer to take "f respects r" to mean only that 
    `r x y` implies `r (f x) (f y)`. 
    
    In any case, when f respects r (in the appropriate sense), then f should "lift" to 
    a function on the classes, f' : α / r → α / r, defined on each equivalence 
    class ⟦x⟧ by f' ⟦x⟧ = ⟦f x⟧.
    
    Because of the distinction between our notion of "respects" and that of the std lib, 
    we develop our own quotient.
  -/

namespace ualib_quotient
  
  section unary
  parameters {α : Type*} {ρ : Type*} 

  -- The equivalence class of r containing a will be denoted by a/r.
  local notation a`/`r := quot.mk r a

  lemma equiv_elem (r : α → α → Prop) (f : (ρ → α) → α) : 
  ∀ (a b : ρ → α), r (f a) (f b)  → (f a)/r = (f b)/r := assume (a: ρ → α) (b: ρ → α), 
  assume h : r (f a) (f b), show (f a)/r = (f b)/r, from quot.sound h
  
  -- (πᵤ f) a == (f a)/r.
  local notation a`/`r := quot.mk r a
  def πᵤ (f : α → α) (r : α → α → Prop) : α → quot r := λ a, (f a) / r
  
  def compatible_unary (f : α → α) (r : α → α → Prop) := ∀ a b, r a b → r (f a) (f b)
   
  lemma proj_of_compatible_unary_respects 
  (f : α → α) (r : α → α → Prop) (h : compatible_unary f r) :
  ∀ a b, r a b → (f a)/r = (f b)/r :=  -- N.B. (f a)/r = (f b)/r means (πᵤ f r) a = (πᵤ f r) b
  assume a b (h₀ : r a b), 
  have h₃ : r (f a) (f b), from h a b h₀, 
  show (f a)/r = (f b)/r, from quot.sound h₃

  def lift_proj (f : α → α) (r : α → α → Prop) (h : compatible_unary f r) : quot r → quot r := 
  quot.lift (πᵤ  f r) (proj_of_compatible_unary_respects f r h) 
  
  end unary

--We want to construct a quotient algebra A/r such that if A has operation f : (ρ → α) → α, 
--then A/r should have operation f' : (ρ → α/r) → α/r  
  section higher_arity

    parameters {α : Type*} {β : Type*}  {γ : Type*} 
    parameter {S : signature}  -- {A : algebra_on α } -- {B : algebra S} 
    parameter r : α → α → Prop
    parameter P : (γ → α) → (γ → α) → Prop
    parameters (A : algebra_on S α) (f : S.F) 
--    parameter (Q : op (S.ρ f) α → op (S.ρ f) α → Prop)  
    parameter (Q : (S.ρ f → α) → (S.ρ f → α) → Prop)  

    -- notation
    def F := S.F
    def ρ := S.ρ 

    -- The equivalence class of r containing a will be denoted by a/r.
    local notation a`/`r := quot.mk r a

    def liftR {γ : Type u} (r : α → α → Prop) : (γ → α) → (γ → α) → Prop := 
    λ (a b : γ → α) , ∀ i, r (a i) (b i)

    local notation `⟦`r`⟧` := liftR r
    local notation `[`a`]` := quot.mk Q a
--    local notation `[`:max a`]` := quot.mk r a
    
    parameter ν : quot Q → Type*
    
    -- If a, b : γ → α, and r is a binary relation on α, then: ⟦r⟧ a b ↔ ∀ i, r (a i) (b i).
    
    def compatible_fun_rel (f : (γ → α) → α) (r : α → α → Prop) : Prop := 
    ∀ (a b : γ → α), ⟦r⟧ a b → r (f a) (f b)

    def compatible_fun_rel' (f : (γ → α) → α) (r : α → α → Prop): Prop := 
    ∀ (a b : γ → α), ⟦r⟧  a b → (f a)/r = (f b)/r

    def compatible_op_rel (A : algebra_on S α) (f : F) (r : α → α → Prop) : Prop := 
    ∀ (a b : ρ f → α), ⟦r⟧ a b → (A f a)/r = (A f b)/r
    -- ∀ (a b : S.ρ f → α), (∀ i, r (a i) (b i)) → (A f a)/r = (A f b)/r
  
    def ker (f : (γ → α) → α) : (γ → α) → (γ → α) → Prop :=  λ a b, f a = f b

    lemma proj_of_compatible_respects 
    (f : (γ → α) → α) (r : α → α → Prop) (h : compatible_fun_rel f r) :
    ∀ (a b : γ → α), ⟦r⟧  a b  →  (f a)/r = (f b)/r :=
    assume a b (h₀ : ⟦r⟧ a b), 
    have h₃ : r (f a) (f b), from h a b h₀, 
    show (f a)/r = (f b)/r, from quot.sound h₃

    def π (f : (γ → α) → α) (r : α → α → Prop) : (γ → α) → quot r := 
    λ (a : γ → α) , (f a) / r

    -- attribute [reducible, elab_as_eliminator]
    def lift_general (f : (γ → α) → α ) (r : α → α → Prop) (h : compatible_fun_rel f r) : 
    quot ⟦r⟧ → quot r := 
    quot.lift (π f r) (proj_of_compatible_respects f r h) 

    def kernel {A : algebra_on S α} {B : algebra_on S β} (f : α → β) : 
    α → α → Prop := λ a a', f a = f a'

    -- A relation is compatible with A iff it is preserved by the ops of A
    def compatible_alg_rel (A : algebra_on S α) (r: α → α → Prop) : Prop := 
    ∀ f : F, compatible_op_rel A f r

    def rel_on_tuples_of_A_of_length {α : Type*} (β :Type*) := (β → α) → (β → α) → Prop

    -- A congruence is a compatible equivalence relation
    def congruence (A : algebra_on S α) (r: α → α → Prop) : Prop := 
    equivalence r ∧ compatible_alg_rel A r

    attribute [reducible, elab_as_eliminator]
    def lift_op (A : algebra_on S α) (f : F) (r : α → α → Prop) (h : congruence A r) :
    quot ⟦r⟧  → quot r := 
    quot.lift (λ a, (A f a)/ r) (h.right f) 

    -- The type of an operation f on the quotient A/r should be 
    -- (ρ f → A/r) → A/r

    -- def lift_alg_op (A : algebra_on S α) (f : F) (r : α → α → Prop) 
    -- (h: ∀ (a b : ρ f → α), ⟦r⟧ a b → (A f a)/r = (A f b)/r) :
    -- (ρ f → quot r) → quot r := λ (a : ρ f → quot r), (A f a)/r

    --#check quot.mk Q (A f)
    
    def lift_elem (a : ρ f → α) : ρ f → quot r := λ i, (a i)/r



    --def indep (A : algebra_on S α) (f : S.F) (a : S.ρ f → α) : sigma ν := ⟨[a], (A f a)⟩   
    def indep (a : S.ρ f → α) : sigma ν := ⟨[a], (A f a)⟩   

    -- def lift_alg_op (aa : ρ f → quot r) : quot r := 
    --    quot.mk r (A f a)

    
--#check lift_alg_op

    -- def lift' (f : (γ → α) → α) (r : α → α → Prop) : (γ → quot r) → quot r 
    -- | λ a, quot.mk r a := f a
    
    -- (h: ∀ (a b : ρ f → α), ⟦r⟧ a b → (A f a)/r = (A f b)/r) :
    -- (ρ f → quot r) → quot r := λ (a : ρ f → quot r), match a
    -- | quot.mk ⟦ r ⟧ a := (A f a)/r

    def semi_lift_op (A : algebra_on S α) (f : F) (r : α → α → Prop) :
    (ρ f → α ) → quot r := λ a, (A f a)/ r

    #check lift_op

    lemma congruence_sound_quot (A : algebra_on S α) 
    (f : S.F) (r : α → α → Prop) (h : congruence A r) :
    ∀ (a b : ρ f → α), ⟦r⟧ a b  →  (A f a)/r = (A f b)/r :=
    assume a b (h₀ : ⟦r⟧ a b),
    show (A f a)/r = (A f b)/r, from (h.right f a b h₀)

    lemma congruence_sound (A : algebra_on S α) 
    (r : α → α → Prop) (h : congruence A r) :
    ∀ (f : S.F), ∀ (a b : ρ f → α), ⟦r⟧ a b  →  (A f a)/r = (A f b)/r :=
    assume f a b (h₀ : ⟦r⟧ a b),
    show (A f a)/r = (A f b)/r, from (h.right f a b h₀)

    def quot_alg (A : algebra_on S α) (r: α → α → Prop) (h : congruence A r) : algebra_on S (quot r) := 
    λ f : F , (lift_op A f r h) -- (congruence_sound_quot A f r h) 

    #check quot_alg
    variables r : α → α → Prop
    #check quot r
    #check quot ⟦ r ⟧ 
--  def quot_alg {A : algebra S} (f : S.F) (r: A.fst → A.fst → Prop) : ((S.ρ f) → (quot r)) → (quot r) := 
  -- λ aa, ∀ i, 
  -- (quot.mk r a), A f a
  
  -- lemma lift_beta {α : Sort u} {r : α → α → Prop} {β : Sort v} 
  -- (f : α → β) --(c : ∀ a b, r a b → f a = f b) 
  -- (a : α) : lift f c (quot.mk r a) = f a := rfl

  -- If K is the kernel of a hom h, then we have
  -- h (A f a) = B f (h ∘ a), and if ∀ i, (kernel h) (a i) (b i), 
  -- then ∀ i, h (a i) = h (b i), which implies h ∘ a = h ∘ b, which implies
  -- h (A f a) = B f (h ∘ a) = B f (h ∘ b) = h (A f b)

  
  --def quotient_algebra {A : algebra S} (r : A.fst → A.fst → Prop) (h₁ : congruence r)
  --: algebra S := ⟨ quot r, Π (f : S.F), quot.lift f 


  -- lemma cong_iff_hom_ker (r :  A → A → Prop) :
  -- congruence r ↔ ∃ B : algebra S, ∃ h : A → B, 
  --                homomorphic h ∧ ((kernel h) = r) := 
  -- iff.intro
  -- (assume h₁ : congruence r, 
  -- show ∃ (B : algebra S) (h : A → B), homomorphic h ∧ (kernel h) = r, from sorry)
  -- (sorry)

  -- def image (f : A → B) : set B := λ b, ∃ a, f a = b

  -- def ker (f : α → β) : α → α → Prop := λ a a', f a = f a'

    end higher_arity

end ualib_quotient



  /-Notes from Ch. 11. Theorem Proving in Lean.
  
    In its most basic form, the quotient construction does not require 
    r be an equivalence relation. The following are built into Lean 
    as constants: 
  -/
  
  #check @quot  --form the type quot r given a type α by any binary relation r on α. 
  --constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u
  
  #check @quot.mk   -- map α to quot α; if r : α → α → Prop and a : α, then 
                    -- quot.mk r a ∈ quot r. 
  --constant quot.mk : Π {α : Sort u} (r : α → α → Prop), α → quot r
  
  #check @quot.ind  --says that each element of quot.mk r a is of the form quot.mk r a.  
  --axiom quot.ind : ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
  --(∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q

  #check @quot.lift --given a function f : α → β, if h is a proof that f respects r, 
                    -- then quot.lift f h 
                    -- is the corresponding function on quot r.  -/
  --constant quot.lift : Π {α : Sort u} {r : α → α → Prop} {β : Sort u}
  --(f : α → β), (∀ a b, r a b → f a = f b) → quot r → β

  -- What makes quot into a bonafide quotient is the following additional axiom:
  #check @quot.sound  
  -- axiom quot.sound: ∀ {α: Type u} {r: α → α → Prop} {a b: α}, r a b → quot.mk r a = quot.mk r b
  
  -- If a thm or def uses quot.sound, it will show up in #print axioms.
  --The quotient is most commonly used when r is an equivalence relation. 
  --Given r as above, define r' as follows: ∀ a b, r' a b ↔ quot.mk r a = quot.mk r b, 
  --Then it's clear that r' is an equivalence relation. Indeed, r' is the *kernel* of 
  --the function a ↦ quot.mk r.  The axiom quot.sound says that r a b implies r' a b. 
  --Using quot.lift and quot.ind, we can show that r' is the smallest equivalence 
  --containing r. If r was already an equivalence, then ∀ a b, r a b ↔ r' a b.

  --To support this common use case, the std lib defines the notion of a *setoid*, which is 
  --simply a type with an associated equivalence relation:

  #print setoid    --class setoid (α : Type u) := (r : α → α → Prop) (iseqv : equivalence r)
