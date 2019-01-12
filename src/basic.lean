import data.set

definition op (β α) := (β → α) → α

definition π {β α} (i) : op β α :=
λ f, f i

variables (α : Type*) (β : Type*) (i : β) (f : β → α) 
#check π i f
-- Signature
-- F : a set of operation symbols
-- ρ : returns the arity of a given operation symbol

structure signature := mk :: (F : Type*) (ρ : F → Type*)

section
  parameter (S : signature)
  local notation `F` := S.F
  local notation `ρ` := S.ρ 

  -- Defines the interpretation of an algebra on the carrier α
  definition algebra_on (α : Type*) := Π (f : F), op (ρ f) α   

  -- This is called `algebra_on` since an algebra is fully
  -- specified by its (Cayley) operation tables. An inhabitant 
  -- of `algebra_on` assigns to each op symbol f : F, of 
  -- arity `β = S.ρ f`, an interpretation of f, that is, 
  -- a function of type (β → α) → α.

  -- An algebra pairs a carrier with an interpretation of the op symbols
  definition algebra := sigma algebra_on

  -- sigma is the "dependent pair" type: ⟨α, β α⟩ which is appropriate here since
  -- an algebra consists of a universe (of type α), and operations on that universe,
  -- the type of the operations depends on the universe type.

  instance alg_carrier : has_coe_to_sort algebra := ⟨_, sigma.fst⟩

  instance alg_operations : has_coe_to_fun algebra := ⟨_, sigma.snd⟩
end

section

  def is_subalgebra {S : signature} {α : Type*} {β : Type*}
  (A : algebra_on S α) {β : set α} (B : algebra_on S β) :=
  ∀ f b, ↑(B f b) = A f ↑b

  def homomorphic {S : signature}
  {A : algebra S} {B : algebra S} 
  (h : A → B) := ∀ (f : S.F) (a : S.ρ f → A.fst), h (A f a) = B f (h ∘ a)

  -- more explicitly, 
  -- def homomorphic {A B : algebra S} (h : A → B) := 
  -- ∀ (f : S.F) (a : (S.ρ f) → A.fst) , h (A f a) = B f (h ∘ a)
end

/- section
  open alg
  parameters (S : signature) (α : Type*) (β : Type*) (A : @algebra_on S α)
  def F := S.F
  def ρ := S.ρ 
  
/-   def is_subalgebra (β : set α) (B : algebra_on β) :=
  ∀ (f : F) (b : ρ f → β), ↑(B f b) = A f ↑b
 -/
--def homomorphic (h : A → B) := ∀ f a, h (A f a) = B f (h ∘ a)

-- more explicitly, 
def homomorphic {A B : algebra S} (h : A → B) := 
∀ (f : S.F) (a : (S.ρ f) → A.fst) , h (A f a) = B f (h ∘ a)

end

 -/
-- Misc. Notes
-- -----------
-- An algebra pairs a carrier with an interpretation of the op symbols.
-- def algebra := sigma algebra_on
-- 
-- sigma is the dependent product (i.e., dependent pair) type.
--
-- sigman := Π α, ⟨α, β (α)⟩ 
--
-- This is appropriate here since an algebra consists of a universe (of type α),
-- along with operations on that universe, and the type of each operation is
-- dependent on the type, α, of the universe.
--
-- We use coersions so that, if A is an algebra, Lean will correctly interpret 
-- the symbol A to mean either the algebra itself or the carrier of the algebra.