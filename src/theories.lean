/-theories.lean -- Basic model theory

  Author: William DeMeo <williamdemeo@gmail.com>
  Date: 26 Nov 2018

  References
  [1] Bergman, Clifford, "Universal algebra," CRC Press, 2012
  [2] Avigad, et al, "Theorem Proving in Lean," 2018 
      url: https://leanprover.github.io/theorem_proving_in_lean/theorem_proving_in_lean.pdf
  
  

  Copyright (c) 2018 William DeMeo  
  See the LICENSE file at \url{https://github.com/UniversalAlgebra/lean-ualib/blob/master/LICENSE}
-/

universe u

--namespace ualib_quotient
--Reference: Chapter 11 of Theorem Proving in Lean [1].

  /-Let `α` be any type, and let `r` be an equivalence relation on `α`. It is mathematically 
    common to form the "quotient" `α / r`, that is, the type of elements of `α` "modulo" `r`. 
    Set theoretically, one can view `α / r` as the set of equivalence classes of `α` modulo `r`. 
    If `f : α → β` is any function that respects the equivalence relation in the sense that for 
    every `x y : α`, `r x y` implies `f x = f y`, then `f` "lifts" to a function `f' : α / r → β` 
    defined on each equivalence class `⟦x⟧` by `f' ⟦x⟧ = f x`. Lean's standard library extends 
    the Calculus of Constructions with additional constants that perform exactly these constructions, 
    and installs this last equation as a definitional reduction rule.
  -/

  /-In its most basic form, the quotient construction does not require `r` be an equivalence 
    relation. The following constants are built into Lean:
  -/

  constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u
    
  --constant quot.mk : Π {α : Sort u} (r : α → α → Prop), α → quot r

  --axiom quot.ind : ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
  --(∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q

  --constant quot.lift : Π {α : Sort u} {r : α → α → Prop} {β : Sort u} (f : α → β),
  --(∀ a b, r a b → f a = f b) → quot r → β

  /-1.forms the type `quot r` given a type `α` by any binary relation `r` on `α`. 
    2.`quot.mk` maps `α` to `quot α`; if `r : α → α → Prop` & `a : α`, then `quot.mk r a ∈ quot r`. 
    3.`quot.ind` says that each element of `quot.mk r a` is of this form.  
    4.given a function `f : α → β`, if `h` is a proof that `f` respects `r`, then `quot.lift f h` 
      is the corresponding function on `quot r`. 
  -/

  variables α β : Type
  variable  r : α → α → Prop
  variable  a : α

  -- the quotient type
  #check (quot r : Type)

  -- the class of a
  #check (quot.mk r a : quot r)

  variable  f : α → β
  variable   h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂

  -- the corresponding function on quot r
  #check (quot.lift f h : quot r → β)

  /-The idea of 4 is that for each `a` in `α`, the function `quot.lift f h` maps `quot.mk r a` 
    (the `r`-class containing `a`) to `f a`, wherein `h` shows that this function is well defined. 
    In fact, the computation principle is declared as a reduction rule, as the following makes clear.
  -/

  -- the computation principle
  theorem thm : quot.lift f h (quot.mk r a) = f a := rfl

  #print axioms thm   -- no axioms (are required for thm)

-- since  `quot`, `quot.mk`, `quot.ind`, and `quot.lift` are not viewed as additional axioms;
-- instead, they are, like inductively defined types and the associated constructors and recursors, 
-- viewed as part of the logical framework.

-- What makes `quot` into a bona fide quotient is the following additional axiom:


namespace hidden
  axiom quot.sound :
  ∀ {α : Type u} {r : α → α → Prop} {a b : α},
  r a b → quot.mk r a = quot.mk r b

end hidden

--This axiom asserts that any two elements of `α` that are related by `r` become identified 
-- in the quotient. If a theorem or definition makes use of `quot.sound`, it will show up 
-- in the `#print axioms` command.

-- Of course, the quotient construction is most commonly used in situations when ``r`` is an equivalence relation. Given ``r`` as above, if we define `r'` according to the rule `r' a b` iff `quot.mk r a = quot.mk r b`, then it's clear that `r'` is an equivalence relation. Indeed, `r'` is the *kernel* of the function ``a ↦ quot.mk r``.  The axiom ``quot.sound`` says that ``r a b`` implies ``r' a b``. Using ``quot.lift`` and ``quot.ind``, we can show that ``r'`` is the smallest equivalence relation containing ``r``, in the sense that if ``r''`` is any equivalence relation containing ``r``, then ``r' a b`` implies ``r'' a b``. In particular, if ``r`` was an equivalence relation to start with, then for all ``a`` and ``b`` we have ``r a b`` iff ``r' a b``.

-- To support this common use case, the std lib defines the notion of a *setoid*, which is 
-- simply a type with an associated equivalence relation:

namespace hidden

    -- BEGIN
    class setoid (α : Type u) :=
    (r : α → α → Prop) (iseqv : equivalence r)

    namespace setoid
      infix `≈` := setoid.r

      variable {α : Type u}
      variable [s : setoid α]
      include s

      theorem refl (a : α) : a ≈ a :=
      (@setoid.iseqv α s).left a

      theorem symm {a b : α} : a ≈ b → b ≈ a :=
      λ h, (@setoid.iseqv α s).right.left h

      theorem trans {a b c : α} : a ≈ b → b ≈ c → a ≈ c :=
      λ h₁ h₂, (@setoid.iseqv α s).right.right h₁ h₂
    end setoid
    -- END

    end hidden

universes u v

constant quot : Π {α : Sort u}, (α → α → Prop) → Sort u

constant quot.mk :
  Π {α : Sort u} (r : α → α → Prop), α → quot r

axiom quot.ind :
  ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
    (∀ a, β (quot.mk r a)) → ∀ (q : quot r), β q

constant quot.lift :
  Π {α : Sort u} {r : α → α → Prop} {β : Sort u} (f : α → β),
    (∀ a b, r a b → f a = f b) → quot r → β


end ualib_quotient
