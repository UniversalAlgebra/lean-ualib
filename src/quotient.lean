/-quotient.lean -- Quotient Structures and Homomorphic Images

  Author: William DeMeo <williamdemeo@gmail.com>
  Date: 30 Nov 2018

  References
  [1] Bergman, Clifford, "Universal algebra," CRC Press, 2012
  [2] Avigad, et al, "Theorem Proving in Lean," 2018 
      url: https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf
  
  

  Copyright (c) 2018 William DeMeo  
  See LICENSE file at https://github.com/UniversalAlgebra/lean-ualib/blob/master/LICENSE
-/

universe u

namespace ualib_quotient

  /-Reference: Chapter 11 of Theorem Proving in Lean [1].
    Let `α` be any type, and let `r` be an equivalence relation on `α`. It is mathematically 
    common to form the "quotient" `α / r`, that is, the type of elements of `α` "modulo" `r`. 
    Set theoretically, one can view `α / r` as the set of equivalence classes of `α` modulo `r`. 
    If `f : α → β` is any function that respects the equivalence relation in the sense that for 
    every `x y : α`, `r x y` implies `f x = f y`, then `f` "lifts" to a function `f' : α / r → β` 
    defined on each equivalence class `⟦x⟧` by `f' ⟦x⟧ = f x`. Lean's standard library extends 
    the Calculus of Constructions with additional constants that perform exactly these 
    constructions, and installs this last equation as a definitional reduction rule.  -/

  /-In its most basic form, the quotient construction does not require `r` be an equivalence 
    relation. The following are built into Lean as constants: -/
  
  #check @quot  --form the type `quot r` given a type `α` by any binary relation `r` on `α`. 
  --constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u
  
  #check @quot.mk   -- map `α` to `quot α`; if `r : α → α → Prop` and `a : α`, then 
                    -- `quot.mk r a ∈ quot r`. 
  --constant quot.mk : Π {α : Sort u} (r : α → α → Prop), α → quot r
  
  #check @quot.ind  --says that each element of `quot.mk r a` is of the form `quot.mk r a`.  
  --axiom quot.ind : ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
  --(∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q

  #check @quot.lift --given a function `f : α → β`, if `h` is a proof that `f` respects `r`, 
                    -- then `quot.lift f h` 
                    -- is the corresponding function on `quot r`.  -/
  --constant quot.lift : Π {α : Sort u} {r : α → α → Prop} {β : Sort u}
  --(f : α → β), (∀ a b, r a b → f a = f b) → quot r → β
      
  --EXAMPLES:
  variables (α β : Type) (r : α → α → Prop) (a : α) -- N.B. we need not assume r is an equiv rel.
  #check (quot r : Type)         -- the quotient type
  #check (quot.mk r a : quot r)  -- the r-class containing a

  variables (f : α → β) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂)
  #check (quot.lift f h : quot r → β) -- the corresponding function on quot r

  /-For each `a` in `α`, `quot.lift f h` maps the r-class `quot.mk r a` of `a` to `f a`, 
    and `h` shows that this function is well defined. In fact, the computation principle 
    is declared as a reduction rule:                                       -/
  theorem thm : quot.lift f h (quot.mk r a) = f a := rfl

  #print axioms thm  -- no axioms required since quot.lift & quot.mk are part of logical framework.

  -- What makes `quot` into a bonafide quotient is the following additional axiom:
  #check @quot.sound  -- axiom quot.sound: ∀ {α: Type u} {r: α → α → Prop} {a b: α}, r a b → quot.mk r a = quot.mk r b
  
  -- If a thm or def uses `quot.sound`, it will show up in `#print axioms`.

  --The quotient is most commonly used when `r` is an equivalence relation. 
  --Given `r` as above, define `r'` as follows: `∀ a b, r' a b ↔ quot.mk r a = quot.mk r b`, 
  --Then it's clear that `r'` is an equivalence relation. Indeed, `r'` is the *kernel* of 
  --the function `a ↦ quot.mk r`.  The axiom `quot.sound` says that `r a b` implies `r' a b`. 
  --Using `quot.lift` and `quot.ind`, we can show that `r'` is the smallest equivalence 
  --containing `r`. If `r` was already an equivalence, then `∀ a b, r a b ↔ r' a b`.

  --To support this common use case, the std lib defines the notion of a *setoid*, which is 
  --simply a type with an associated equivalence relation:

  #print setoid    --class setoid (α : Type u) := (r : α → α → Prop) (iseqv : equivalence r)

  --infix `≈` := setoid.r
  variable [s : setoid α]
  include s

  --theorem refl (a : α) : a ≈ a := (@setoid.iseqv α s).left a
  theorem refl (a : α) : a ≈ a := (@setoid.iseqv α s).left a
  theorem symm {a b : α} : a ≈ b → b ≈ a := λ h, (@setoid.iseqv α s).right.left h
  theorem trans {a b c: α}: a ≈ b → b ≈ c → a ≈ c:= λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂


/- def liftR {α : Type u_5} (r : α → α → Prop) {τ : Type u_2} : (τ → α) → (τ → α) → Prop := λ s t : τ → α, 
∀ i, r (s i) (t i)
def compatible₂ (r: A → A → Prop) : Prop := 
  ∀ f a b, liftR r a b → r (A f a) (A f b)

def quot_algebra_on (r : rel_on_A) (rcong : congruence r) 
-- : algebra_on S (quot r) 
:= Π f, op (S.ρ f) (quot r)

def quot_algebra  (r : rel_on_A) (rcong : congruence r) :=
psigma (quot_algebra_on r rcong)
 -/






end ualib_quotient
