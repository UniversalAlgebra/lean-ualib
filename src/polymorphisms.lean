/-polymorphisms.lean
  Author: William DeMeo <williamdemeo@gmail.com>
  Date: 30 Nov 2018

  Copyright (c) 2018 William DeMeo  
  See LICENSE file: https://github.com/UniversalAlgebra/lean-ualib/blob/master/LICENSE
-/


namespace ualib_polymorphisms

  section
    parameters {α : Type*} {β : Type*}

    -- all unary polymorphisms of r
    def unary_polymorphisms (r : α → α → Prop) : (α → α) → Prop := λ f : α → α, 
    ∀ (a: α) (a':α), (r a a') → r (f a) (f a')

    -- all polymorphisms of one relation r
    def polymorphisms (r : α → α → Prop) : ((β → α) → α) → Prop := λ f : (β → α) → α, 
    ∀ (a a' : β → α), (∀ (i : β), r (a i) (a' i)) → r (f a) (f a')

    -- polymorphisms of a set R of relations 
    def polymoprhisms (R : (α → α → Prop) → Prop) : ((β → α) → α) → Prop := 
    λ (f : (β → α) → α), ∀ r, R r → (polymorphisms r) f

  end
end ualib_polymorphisms