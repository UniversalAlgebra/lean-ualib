/-birkhoof.lean -- Birkhoff's HSP Theorem in Lean

  Notes:Recall, 
        -`Prop` is syntactic sugar for `Sort 0`, the bottom of the type hierarchy.
          Like the other type universes, it is closed under the arrow constructor 
          (if `p q : Prop`, then `p → q : Prop`)
        -`Type u` is syntactic sugar for `Sort (u+1)`
          (`Prop = Type -1` and `Sort 1 = Type 0`)
-/
-- import basic
import basic
import subuniverse 
import data.set

section

  universe s -- where operation (s)ymbols live
  universe u -- where structure (u)niverses (i.e. carriers) live
  universe a -- where (a)rities live

  parameter υ : Sort u  -- A carrier type
  parameter τ : Sort u  -- Another carrier type

  -- Operation on the carrier υ (of arity α) 
--  def op (υ : Sort u) (α : Sort a) := (α → υ) → υ  

  -- Restricted Operation on the carrier υ (of arity α) 
  def op_restricted {υ : Sort u} (r : υ → Prop) (α : Sort a) := (α → (υ → Prop)) → (υ → Prop) 

   -- i-th projection
   --def π {υ : Sort u} (α : Sort a) (i) : op υ α := λ x, x i

  -- Signature
  -- F : a set of operation symbols
  -- ρ : returns the arity of a given operation symbol
--  structure signature := 
--  mk :: (F : Sort s) (ρ : F → Sort a)
  
  -- The type of interpretations of operation symbols.
--  def algebra_on (υ : Sort u) (S : signature) := Π (f : S.F) , op υ (S.ρ f)
  -- It's called `algebra_on` since an algebra is fully specified by its
  -- (Cayley) operation tables. An inhabitant of `algebra_on` assigns to 
  -- each op symbol f : F, of arity `α = S.ρ f`, an interpretation of f, 
  -- that is, a function of type (α → υ) → υ.
  
--  def homomorphic {υ : Sort u} {τ : Sort u} {S : signature} 
--  (A : algebra_on υ S) (B : algebra_on τ S) (h : υ → τ) : Prop := 
--  ∀ (f : S.F) (tuple : (S.ρ f) → υ), h (A f tuple) = (B f) (h ∘ tuple)

--parameters {α : Type*} {S : signature} (A : algebra S) (B : algebra S) {I ζ : Type} {R : I → set α} 
--section
parameters {α : Type*} {β : Type*} {S : signature} (A : algebra_on S α) 
parameters (B : algebra_on S β) {I ζ : Type} {R : I → set α} 
open set
open subuniverse
  -- parameter {S : signature} 
  -- parameters {A : algebra_on S} {B : algebra_on τ S}
  
  -- def Sub (β : set α) : Prop :=
  -- ∀ f (a : S.ρ f → α), (∀ x, a x ∈ β) → A f a ∈ β

  -- def is_subuniverse {υ : Sort u} {S : signature} (A : algebra_on υ S) : (υ → Prop) → Prop :=
/-   def is_subuniverse (B : υ → Prop) : Prop :=
  ∀ f (tuple : S.ρ f → υ), (∀ x, B (tuple x)) → (A f tuple) ∈ B
 -/  -- Note: z ∈ B is syntactic sugar for B z, so the line B (a x) → B (A f a) 
  -- is understood to mean: (a x) ∈ B → (A f a) ∈ B.

  -- Elementary Facts ------------------------------------------

  /- Lemma (cf. Ex. 1.16.6 of MR2839398)
     Let $f$ and $g$ be homomorphisms from $\alg{A}$ to $\alg{B}$.
     Let $E(f,g) = \{ a \in A : f(a) = g(a) \}$ (the \defin{equalizer} of $f$ and $g$). 
     1. $E(f,g)$ is a subuniverse of $\alg{A}$.
     2. If $X \subseteq A$ and $X$ generates $\alg{A}$ and $\restr{f}{X} = \restr{g}{X}$, then $f = g$. 
     3. If $\mathbf A$, $\mathbf B$ are finite algebras and $X$ generates $\mathbf A$, then 
        $|Hom(\mathbf A, \mathbf B)| \leq |B|^{|X|}$.
  -/
  -- equalizer for generic functions
  def equalizer (h : α → β) (g : α → β) : set α := λ (x : α), h x = g x 


  def hom (h : α → β) :=
  ∀ f a, h (A f a) = B f (h ∘ a)

  def equalizer_of_homs (h : α → β) (g : α → β) 
  (hh : hom h) (hg : hom g) : set α := 
  λ a, h a = g a 

variables (h : α → β) (g : α → β)  (hh : hom h)  (hg : hom g) 
#check equalizer
#check @Sub

  -- 1. The equalizer $E(f,g)$ is a subuniverse of $\mathbf A$.
  lemma sub_equalizer (h : α → β) (g : α → β) (hh : hom h)  (hg : hom g) : 
  Sub A (equalizer_of_homs h g hh hg) := 
  assume f a (h₁: ∀ x, a x ∈ equalizer_of_homs h g hh hg),
  show A f a ∈ (equalizer_of_homs h g hh hg),  from 
    have h₂ : h ∘ a = g ∘ a, from funext h₁, 
    show h (A f a) = g (A f a), from 
      calc h (A f a) = (B f) (h ∘ a): hh f a
                 ... = (B f) (g ∘ a): congr_arg (B f) h₂ 
                 ... = g (A f a) : eq.symm (hg f a)
  


  -- 2. If X ⊆ A, if Sg(X) = \mathbf A, and if f x = g x for all x ∈ X, then f = g. 



















/- inductive term
| var     : X → term
| app (f) : (S.ρ f → term) → term

def free : algebra S :=
⟨term, term.app⟩
 -/
-- One way to make this SEGFAULT lol
/- inductive subuniverse (X : υ) (S: signature) : Type
| var : subuniverse 
| app (f : S.F) (a : S.ρ f → υ) : (∀ i, subuniverse (a i)) → Y (A f a)

theorem sg_inductive : Sg X = Y :=
have h : Y ∈ Sub, from sorry,
have l : Sg X ⊆ Y, from sorry,
have r : Y ⊆ Sg X, from sorry,
subset.antisymm l r
def is_subuniverse' {υ : Sort u} {S : signature} (A : algebra_on υ S) : (υ → Prop) → Prop :=
  λ B, ∀ f, ∀ (tuple : S.ρ f → υ), (∀ x, B (tuple x)) → B (A f tuple)
  

def generates (X : υ → Prop) : Prop := ∀ (SX : υ → Prop), --if B contains X and is a subalgebra of A, then B = A
∀ x, (X x → (SX x)) →  is_subuniverse A SX → is_subuniverse SX (λ z, true)

lemma homs_determined_on_gens (h : υ → τ) (g : υ → τ)
(hh : @homomorphic S A B h) (hg : @homomorphic S A B g) (X : υ → Prop) : 
(is_generating X A) → (∀ x, h x = g x) → h = g := sorry
 -/ /- 
  Suppose the subset $X \subseteq A$ generates $\alg{A}$ and suppose
  $\restr{f}{X} = \restr{g}{X}$.
  Fix an arbitrary element $a\in A$.  We show $f(a) = g(a)$.
  Since $X$ generates $\alg{A}$, there exists a (say, $n$-ary) term $t$ and 
  a tuple $(x_1, \dots, x_n) \in X^n$ such that 
  $a = t^{\alg{A}}(x_1, \dots, x_n)$. Therefore, 
  \begin{align*}
    f(a) = f(t^{\alg{A}}(x_1, \dots, x_n)) &= t^{\alg{B}}(f(x_1), \dots, f(x_n))\\
                                    &= t^{\alg{B}}(g(x_1), \dots, g(x_n))
                                     = g(t^{\alg{A}}(x_1, \dots, x_n)) = g(a).
  \end{align*}
  In other words, a homomorphism is uniquely determined by its restriction to 
  a generating set.
  -/

/-  
  
   There are exactly $|B|^{|X|}$ functions from $X$ to $B$ so, 
  assuming $X$ generates $\alg{A}$, we have
  $|\!\Hom{\alg{A},\alg{B}}| \leq |B|^{|X|}$.
  -/

end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            