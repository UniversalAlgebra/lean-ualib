import basic

-- The next few structures are direct translations of Andrej Bauer's Coq code
-- at https://gist.github.com/andrejbauer/3cc438ab38646516e5e9278fdb22022c


section
structure OpSignature :=
(op_symbol : Type*)
(arity : op_symbol → Type*)

structure OpAlgebra (S : OpSignature) :=
(carrier : Type*)
(op : ∀ f : S.op_symbol, ((S.arity f) → carrier) → carrier)

structure Hom {S : OpSignature} (A : OpAlgebra S) (B : OpAlgebra S) :=
(map : A.carrier → B.carrier) -- the underlying map
(op_commute : ∀ (f : S.op_symbol) (args : S.arity f → A.carrier),
map (A.op f args) = B.op f (λ x, map (args x)))


section terms
  parameters (S : OpSignature) (X : Type*)

  inductive term
  | gen    : X → term
  | node (f)  : --∀ (f : S.op_symbol), 
  (S.arity f → term) → term

  #check term

  def free : OpAlgebra S := 
  ⟨term, term.node⟩ -- ⟨ carrier , operations ⟩ 

end terms

section outer

  parameters {S : OpSignature} (A : OpAlgebra S) (X : Type*) 

  open term
  def term_ := @term S X  
  def free_ := free S X  
  def gen_ := @gen S X

  section inner
  parameter (h : X → A.carrier) 

  def induced_map : free_.1 → A.1
  | (gen .(S) x) := h x
  | (node f a) :=  A.op f (λ (i : S.arity f), induced_map (a i))

  -- Theorem (Existence): There is a homomorphism from Free S X into every 
  --                      algebra of the given signature.
  theorem induced_hom : Hom (free_) A :=
  ⟨induced_map S A X h,          -- the function
  (assume (o: S.op_symbol)     -- proof that the function preserves structure
  (args : S.arity o → free_.carrier), rfl)⟩  

  end inner

-- Theorem (Uniqueness): The homomorphism in the previous theorem is unique.
theorem from_free_unique (f g : Hom (free_) A) :
(∀ (x : X), f.map (gen_ x) = g.map (gen_ x)) → 
  ∀ (t : term_), f.map t = g.map t := 
assume h1: (∀ (x : X), (f.map (gen_ x) = g.map (gen_ x))),
assume (t : @term S X), 
show (f.map t = g.map t), from
begin 
  induction t,
  case term.gen : {simp [h1]},
  case term.node : o args ih { 
    show f.map (term.node o args) = g.map (term.node o args), from 
    calc f.map (term.node o args) = term.node o (f.map ∘ args)  : by rw [f.op_commute]
                              ... = term.node o (g.map ∘ args)  : by rw [ih]
                              ... = f.map (term.node o args) : by rw [g.op_commute]
  }
end

end outer

end