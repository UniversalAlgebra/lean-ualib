-- we start with some examples of classical algebraic structures
namespace examples
  universes u
  variables {α : Type u}

  class magma (α : Type u) extends has_mul α
  -- avoid the name groupoid here because that means something 
  -- different in category theory; we could have called these "binars"

  -- by convention, we use an additive model if the operation is commutative
  class commutative_magma (α : Type u) extends has_add α :=
  (add_comm : ∀ a b : α, a + b = b + a)

  class semigroup (α : Type u) extends magma α :=
  (mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))

  class commutative_semigroup (α : Type u) extends commutative_magma α := 
  (add_assoc : ∀ a b c : α, a + b + c = a + (b + c))

  class monoid (α : Type u) extends semigroup α, has_one α := 
  (one_mul : ∀ a : α, 1 * a = a) (mul_one : ∀ a : α, a * 1 = a) 

  class commutative_monoid (α : Type u) extends commutative_semigroup α, has_zero α := 
  (zero_add : ∀ a : α, 0 + a = a) (add_zero : ∀ a : α, a + 0 = a) 

  class group (α : Type u) extends monoid α, has_inv α 

  class commutative_group (α : Type u) extends commutative_monoid α, has_inv α 

  -- Use monoid here because we assume rings have a multiplicative identity
  class ring (α : Type u) extends commutative_group α, monoid α := 
  (distr_add_mul_left : ∀  a b c : α, a * (b + c) = a * b + a * c)
  (distr_add_mul_right : ∀  a b c : α, (b + c) * a = b * a + c * a)

  -- Use semigroup here to model rings without a multiplicative identity; i.e. "rngs"
  class rng (α : Type u) extends commutative_group α, semigroup α :=
  (distr_add_mul_left : ∀  a b c : α, a * (b + c) = a * b + a * c)
  (distr_add_mul_right : ∀  a b c : α, (b + c) * a = b * a + c * a)

  -- model meet or join with plus
  class semilattice (α : Type u) extends commutative_semigroup α :=
  (add_idempotent : ∀ x :α,  x + x = x)

  -- we model ∨ (or "join" or "sup") as + of semilattice; 
  -- we model ∧ (or "meet" or "inf") as a * of a semigroup and make it commutative.
  class lattice (α : Type u) extends semilattice α, semigroup α :=  
  (mul_idempotent : ∀ x : α,  x * x = x)
  (add_absorb_left: ∀ x y: α, x * (x + y) = x) (add_absorb_right: ∀ x y: α, (x + y) * x = x)  
  (mul_absorb_left: ∀ x y: α, x + (x * y) = x) (mul_absorb_right: ∀ x y: α, (x * y) + x = x)  

  class bounded_lattice (a : Type u) extends lattice α, has_one α, has_zero α :=
  (one_mul : ∀ x : α, one * x = x)  (mul_one : ∀ x : α, x * one = x)
  (add_one : ∀ x : α, one + x = one)  (one_add : ∀ x : α, x + one = one)
  (zero_mul : ∀ x : α, zero * x = zero) (mul_zero : ∀ x : α, x * zero = zero)
  (zero_add : ∀ x : α, zero + x = x) (add_zero : ∀ x : α, x + zero = x)

  class distributative_lattice (α : Type u) extends lattice α :=  
  (add_dis : ∀ x y z : α,  x + (y * z) = (x + y) * (x + z))
  (dis_add : ∀ x y z : α,  (y * z) + x = (y + x) * (z + x))
  (mul_dis : ∀ x y z : α,  x * (y + z) = (x * y) + (x * z))
  (dis_mul : ∀ x y z : α,  (y + z) * x = (y * x) + (z * x))


end examples


