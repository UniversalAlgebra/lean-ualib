/-
Copyright (c) 2018 William DeMeo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: William DeMeo <williamdemeo@gmail.com>

lean-ualib basic.lean -- Universal Algebra Foundations
-/

-- we start with some examples of classical algebraic structures
namespace examples
  universes u
  variables {α : Type u}

  class magma (α : Type u) extends has_mul α
  -- avoid the name groupoid here because that means something 
  -- different in category theory; we could have called these "binars"

  -- by convention, we use an additive model if the operation is commutative
  class comm_magma (α : Type u) extends has_add α :=
  ( add_comm : ∀ a b : α, a + b = b + a )

  class semigroup (α : Type u) extends magma α :=
  ( mul_assoc : ∀ a b c : α, a * b * c = a * (b * c) )

  class comm_semigroup (α : Type u) extends comm_magma α := 
  ( add_assoc : ∀ a b c : α, a + b + c = a + (b + c) )

  class monoid (α : Type u) extends semigroup α, has_one α := 
  ( one_mul : ∀ a : α, 1 * a = a ∧ a * 1 = a ) 

  class comm_monoid (α : Type u) extends comm_semigroup α, has_zero α := 
  ( zero_add : ∀ a : α, 0 + a = a ∧ a + 0 = a ) 

  class group (α : Type u) extends monoid α, has_inv α 

  class comm_group (α : Type u) extends comm_monoid α, has_inv α 

  -- Use monoid here because we assume rings have a multiplicative identity
  class ring (α : Type u) extends comm_group α, monoid α := 
  ( distr_add_mul : ∀  a b c : α, a * (b + c) = a * b + a * c )

  -- Use semigroup here to model rings without a multiplicative identity; i.e. "rngs"
  class rng (α : Type u) extends comm_group α, semigroup α :=
  ( distr_add_mul : ∀  a b c : α, a * (b + c) = a * b + a * c )

 
end examples


