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
  -- (defined in basic.lean)  def op (υ : Sort u) (α : Sort a) := (α → υ) → υ  

  -- Restricted Operation on the carrier υ (of arity α) 
  def op_restricted {υ : Sort u} (r : υ → Prop) (α : Sort a) := (α → (υ → Prop)) → (υ → Prop) 

  -- (defined in basic.lean) structure signature := mk :: (F : Sort s) (ρ : F → Sort a)

  parameters {α : Type*} {β : Type*} {S : signature} (A : algebra_on S α) 
  parameters (B : algebra_on S β) {I ζ : Type} {R : I → set α} 
  open set
  open subuniverse

  -- Elementary Facts ------------------------------------------

  /- Lemma (cf. Ex. 1.16.6 of Bergman~\cite{MR2839398})
     Let $f$ and $g$ be homomorphisms from $\mathbf A$ to $\mathbf B$.
     Let $E(f,g) = \{ a \in A : f(a) = g(a) \}$ (the **equalizer** of $f$ and $g$). 
     1. $E(f,g)$ is a subuniverse of $\mathbf A$.
     2. If $X \subseteq A$, if $X$ generates $\mathbf A$, and if $\restr{f}{X} = \restr{g}{X}$, 
        then $f = g$. 
     3. If $\mathbf A$, $\mathbf B$ are finite algebras and $X$ generates $\mathbf A$, then 
        $|Hom(\mathbf A, \mathbf B)| \leq |B|^{|X|}$. -/

  -- equalizer for generic functions
  def equalizer (h : α → β) (g : α → β) : set α := λ (x : α), h x = g x 

  -- indicates whether h is a homomorphism  
  def hom (h : α → β) : Prop := ∀ f a, h (A f a) = B f (h ∘ a)

  def equalizer_of_homs (h : α → β) (g : α → β) 
  (hh : hom h) (hg : hom g) : set α := λ a, h a = g a 

  variables (h : α → β) (g : α → β)  (hh : hom h)  (hg : hom g) 

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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            