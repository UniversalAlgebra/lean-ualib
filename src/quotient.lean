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

import basic 
import data.fintype
universes u v

  /-Reference: Chapter 11 of Theorem Proving in Lean [1].
    Let $\alpha$ be any type, and let $r$ be an equivalence relation on $\alpha$. It is 
    common to form the "quotient" $\alpha / r$, that is, the type of elements of $\alpha$ "modulo" $r$. 
    One can view $\alpha / r$ as the set of equivalence classes of $\alpha$ modulo $r$. 


    Let ``f : α → β`` be any (unary) function and let ``r : α → α → Prop`` be a binary relation
    on ``α``.  The Lean standard library takes a notion of "f respects r" that is different from ours.
    
    In the Lean std lib, ``f`` *respects* ``r`` iff 
    ``∀ x y : α, r x y → f x = f y``.
    
    But the consequent ``f x = f y`` is unnecessarily strong.  
    Instead, we require only that `r x y` implies `r (f x) (f y)`. 
    
    In any case, when ``f`` respects ``r`` (in this appropriate sense), then 
    ``f`` should "lift" to a function ``f' : α / r → α / r`` defined on each equivalence 
    class ``⟦x⟧`` by ``f' ⟦x⟧ = ⟦f x⟧``.
    
    Because of the distinction between our notion of "respects" and that of the std lib, 
    we will roll our own quotient.
  -/

namespace ualib_quotient
  --EXAMPLES:
  -- We have the quotient for unary functions ``f : α → α`` ↦ ``f' : α/r → α/r``  working fine.
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
  ∀ a b, r a b → (f a)/r = (f b)/r :=  
  assume a b (h₀ : r a b), 
  have h₃ : r (f a) (f b), from h a b h₀, 
  show (f a)/r = (f b)/r, from quot.sound h₃

  def lift_proj (f : α → α) (r : α → α → Prop) (h : compatible_unary f r) : quot r → quot r := 
  quot.lift (πᵤ  f r) (proj_of_compatible_unary_respects f r h) 
  
  end unary

  -- Unfortunately, we haven't got the quotient for higher-ary functions 
  -- ``f : (ρ → α) → α`` ↦ ``f' : (ρ → α/r) → α/r``  working just yet.
  -- Also, it's probably only possible to get this working when ``ρ : fintype``.

  section higher_arity
    parameters {α : Type*} {ρ : Type*} 

    -- The equivalence class of r containing a will be denoted by a/r.
    local notation a`/`r := quot.mk r a

    def liftR (r : α → α → Prop) : (ρ → α) → (ρ → α) → Prop := 
    λ a b, ∀ i, r (a i) (b i)
    -- liftR a b  takes tuples a, b and returns true iff each pair (a i, b i) of i-th coordinates is r-related.
    variable r : α → α → Prop

    local notation `⟦`r`⟧` := liftR r
    -- If a and b are tuples from ρ → α, and R is a binary relation on α, then 
    -- ⟦R⟧ a b   ↔   ∀ i, R (a i) (b i)
  
    def compatible (f : (ρ → α) → α) (r : α → α → Prop) := 
    ∀ (a b : ρ → α), ⟦r⟧ a b → r (f a) (f b)
  
    def compatible' (f : (ρ → α) → α) (r : α → α → Prop) := 
    ∀ (a b : ρ → α), ⟦r⟧ a b → (f a)/r = (f b)/r
   
    def ker {α : Type*} {ρ : Type*} (f : (ρ → α) → α) : (ρ → α) → (ρ → α) → Prop :=  
    λ a b, f a = f b

    lemma proj_of_compatible_respects
    (f : (ρ → α) → α) (r : α → α → Prop) (h : compatible f r) :
    ∀ (a b : ρ → α), ⟦r⟧  a b  →  (f a)/r = (f b)/r :=
    assume a b (h₀ : ⟦r⟧ a b), 
    have h₃ : r (f a) (f b), from h a b h₀, 
    show (f a)/r = (f b)/r, from quot.sound h₃

    def π (f : (ρ → α) → α) (r : α → α → Prop) : (ρ → α) → quot r := 
    λ (a : ρ → α) , (f a) / r

  
    -- Recall, if f : (ρ → α) → α, then  π f : (ρ → α) → quot r := λ a, (f a) / r
    -- attribute [reducible, elab_as_eliminator]
    -- def lift_gen (f : (ρ → α) → α ) (r : α → α → Prop) (h : compatible f r) : 
    -- quot r → quot r := 
    -- quot.lift ((π f) r) (proj_of_compatible_respects f r h) 
    --(quot.mk (λ (a b : ρ → α), ⟦ r ⟧ a b) i) 
    -- λ (i : ρ → α), (quot.lift ((π f) r) (proj_of_compatible_respects f r h) )(quot.mk (λ (a b : ρ → α), ⟦ r ⟧ a b) i) 
  
  end higher_arity

end ualib_quotient 


namespace other_attempts
    private definition rr {α : Type*} {ρ : Type*} 
    (r : α → α → Prop) : 
    (ρ → α) → (ρ → α) → Prop := 
    λ (a b : ρ → α) , ∀ (i : ρ), r (a i) (b i)

    infix ` ⟦r⟧ `:50 := rr

    private theorem rr.refl {α : Type*} {ρ : Type*} 
    (r : α → α → Prop) (r_is_equiv : equivalence r):
    ∀ (a : ρ → α), rr r a a := assume a, 
    show ∀ (i : ρ), r (a i) (a i), from 
    assume (i : ρ), r_is_equiv.left (a i)
    
    private theorem rr.symm {α : Type*} {ρ : Type*} 
    (r : α → α → Prop) (r_is_equiv : equivalence r):
    ∀ (a b : ρ → α), rr r a b → rr r b a := assume a b (h₀ : rr r a b), show  
    rr r b a, from assume i, 
    have h₁ : r (a i) (b i), from h₀ i,
    r_is_equiv.right.left h₁ 

    private theorem rr.trans  {α : Type*} {ρ : Type*} 
    (r : α → α → Prop) (r_is_equiv : equivalence r):
    ∀ (a b c : ρ → α), rr r a b → rr r b c → rr r a c := 
    assume a b c (h₀ : rr r a b) (h₁ : rr r b c), show  rr r a c, from 
    assume i, 
    have h₂ : r (a i) (b i), from h₀ i,
    have h₃ : r (b i) (c i), from h₁ i,
    r_is_equiv.right.right h₂ h₃ 
    
    private theorem rr_is_equiv {α : Type*} {ρ : Type*} 
    (r : α → α → Prop) (r_is_equiv: equivalence r) :
    equivalence (@rr α ρ r) := and.intro (rr.refl r r_is_equiv) 
    (and.intro (rr.symm r r_is_equiv) (rr.trans r r_is_equiv) )

    --parameters {α : Type*} {ρ : Type*} (r : α → α → Prop)

    instance rr.setoid (α : Type*) (ρ : Type*) 
    (r : α → α → Prop) (r_is_equiv: equivalence r) : 
    setoid (ρ → α) :=
    setoid.mk (@rr α ρ r) (@rr_is_equiv α ρ r r_is_equiv)

    definition quot_struct (α : Type*) (ρ : Type*) 
    (r : α → α → Prop) (r_is_equiv: equivalence r) : Type* :=
    quotient (rr.setoid α ρ r r_is_equiv)

    namespace quot_struct
      open quot_struct
      definition mk {α : Type*} {ρ : Type*}
      (r: α → α → Prop) (r_is_equiv : equivalence r)
      (a : ρ → α) : (ρ → α) → Prop :=
      λ (b : ρ → α), ∀ i, r (a i) (b i)  -- (quot_struct α ρ r r_is_equiv) a
    end quot_struct

    section
      parameters {α : Type*} {ρ : Type*} 
      variables (r : α → α → Prop) (r_is_equiv: equivalence r)
    -- This doesn't work:
    --  theorem soundness (a b : ρ → α)
    --  (R : quot_struct α ρ r r_is_equiv) 
    --  (a b :ρ → α) (h : R) : ∀ (i : ρ), a i = b i 
    end

end other_attempts


section ualib_quotient_algebra

  parameters {S : signature} {A : algebra S} {B : algebra S} (h : A → B)
  variables (hh : homomorphic h)
  
  def kernel {A : algebra S} {B : algebra S} (f : A → B) : 
  A → A → Prop := λ a a', f a = f a'

  def kerh := kernel h

  -- A relation is compatible with A iff it is preserved by the ops of A
  def compatible (r: A → A → Prop) : Prop := 
  ∀ (f : S.F) (a : S.ρ f → A.fst) (b : S.ρ f → A.fst), 
  ∀ i, r (a i) (b i) → r (A f a) (A f b)

  def rel_on_A := A.fst → A.fst → Prop

  def rel_on_tuples_of_A_of_length (β :Type*) := (β → A.fst) → (β → A.fst) → Prop

  -- A congruence relation on A is a compatible equivalence relation
  def congruence (r: A.fst → A.fst → Prop) : Prop := equivalence r ∧ compatible r

  
    variables (α : Type*) (β : Type*) (r : α → α → Prop) (f : α → α) 
    variables (h' : ∀ a₁ a₂, r a₁ a₂ → r (f a₁) (f a₂))
    
    -- #check (quot.lift f h' : quot r → β) -- the corresponding function on quot r

  -- def lift {A : algebra S} (f : S.F) (r: A.fst → A.fst → Prop) : ((S.ρ f) → (quot r)) → (quot r) := 
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


  lemma cong_iff_hom_ker (r :  A → A → Prop) :
  congruence r ↔ ∃ B : algebra S, ∃ h : A → B, 
                 homomorphic h ∧ ((kernel h) = r) := 
  iff.intro
  (assume h₁ : congruence r, 
  show ∃ (B : algebra S) (h : A → B), homomorphic h ∧ (kernel h) = r, from sorry)
  (sorry)

  def image (f : A → B) : set B := λ b, ∃ a, f a = b

  def ker (f : α → β) : α → α → Prop := λ a a', f a = f a'

end ualib_quotient_algebra



  /-Notes from Ch. 11. Theorem Proving in Lean.
  
    In its most basic form, the quotient construction does not require 
    ``r`` be an equivalence relation. The following are built into Lean 
    as constants: 
  -/
  
  #check @quot  --form the type ``quot r`` given a type ``α`` by any binary relation ``r`` on ``α``. 
  --constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u
  
  #check @quot.mk   -- map ``α`` to ``quot α``; if ``r : α → α → Prop`` and ``a : α``, then 
                    -- ``quot.mk r a ∈ quot r``. 
  --constant quot.mk : Π {α : Sort u} (r : α → α → Prop), α → quot r
  
  #check @quot.ind  --says that each element of ``quot.mk r a`` is of the form ``quot.mk r a``.  
  --axiom quot.ind : ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
  --(∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q

  #check @quot.lift --given a function ``f : α → β``, if ``h`` is a proof that ``f`` respects ``r``, 
                    -- then ``quot.lift f h`` 
                    -- is the corresponding function on ``quot r``.  -/
  --constant quot.lift : Π {α : Sort u} {r : α → α → Prop} {β : Sort u}
  --(f : α → β), (∀ a b, r a b → f a = f b) → quot r → β

  -- What makes ``quot`` into a bonafide quotient is the following additional axiom:
  #check @quot.sound  
  -- axiom quot.sound: ``∀ {α: Type u} {r: α → α → Prop} {a b: α}, r a b → quot.mk r a = quot.mk r b``
  
  -- If a thm or def uses ``quot.sound``, it will show up in ``#print axioms``.
  --The quotient is most commonly used when ``r`` is an equivalence relation. 
  --Given ``r`` as above, define ``r'`` as follows: ``∀ a b, r' a b ↔ quot.mk r a = quot.mk r b``, 
  --Then it's clear that ``r'`` is an equivalence relation. Indeed, ``r'`` is the *kernel* of 
  --the function ``a ↦ quot.mk r``.  The axiom ``quot.sound`` says that ``r a b`` implies ``r' a b``. 
  --Using ``quot.lift`` and ``quot.ind``, we can show that ``r'`` is the smallest equivalence 
  --containing ``r``. If ``r`` was already an equivalence, then ``∀ a b, r a b ↔ r' a b``.

  --To support this common use case, the std lib defines the notion of a *setoid*, which is 
  --simply a type with an associated equivalence relation:

  #print setoid    --class setoid (α : Type u) := (r : α → α → Prop) (iseqv : equivalence r)
