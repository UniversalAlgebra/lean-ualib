/-birkhoof.lean -- Birkhoff's HSP Theorem in Lean

  Notes:Recall, 
        -`Prop` is syntactic sugar for `Sort 0`, the bottom of the type hierarchy.
          Like the other type universes, it is closed under the arrow constructor 
          (if `p q : Prop`, then `p → q : Prop`)
        -`Type u` is syntactic sugar for `Sort (u+1)`
          (`Prop = Type -1` and `Sort 1 = Type 0`)
-/

universe s -- where operation (s)ymbols live
universe u -- where structure (u)niverses (i.e. carriers) live
universe a -- where (a)rities live

section 

  parameter υ : Sort u  -- A carrier type
  parameter τ : Sort u  -- Another carrier type

  -- Operation on the carrier υ (of arity α) 
  def op (υ : Sort u) (α : Sort a) := (α → υ) → υ  

  -- Restricted Operation on the carrier υ (of arity α) 
  def op_restricted {υ : Sort u} (r : υ → Prop) (α : Sort a) := (α → (υ → Prop)) → (υ → Prop) 

  -- i-th projection
  def π {υ : Sort u} (α : Sort a) (i) : op υ α := λ x, x i

  -- Signature
  -- F : a set of operation symbols
  -- ρ : returns the arity of a given operation symbol
  structure signature := 
  mk :: (F : Sort s) (ρ : F → Sort a)
  
  -- The type of interpretations of operation symbols.
  def algebra_on (υ : Sort u) (S : signature) := 
  Π (f : S.F) , op υ (S.ρ f)
  -- It's called `algebra_on` since an algebra is fully specified by its
  -- Cayley (operation) tables. An inhabitant of `algebra_on` assigns to 
  -- each op symbol f : F, of arity `α = S.ρ f`, a function of type (α → υ) → υ.
  
  def homomorphic {υ : Sort u} {τ : Sort u} {S : signature} (A : algebra_on υ S) (B : algebra_on τ S) 
  (h : υ → τ) : Prop := 
  ∀ (f : S.F) (tuple : (S.ρ f) → υ), h (A f tuple) = (B f) (h ∘ tuple)

  def is_subuniverse {υ : Sort u} {S : signature} (A : algebra_on υ S) : (υ → Prop) → Prop :=
  λ B, ∀ f, ∀ (tuple : S.ρ f → υ), (∀ x, B (tuple x)) → B (A f tuple)
  -- Note: B z is true iff z ∈ B, so the line B (a x) → B (A f a) 
  -- means: (a x) ∈ B  → (A f a) ∈ B.

  -- Elementary Facts ------------------------------------------

  /- Lemma (cf. Ex. 1.16.6 of MR2839398)
     Let $f$ and $g$ be homomorphisms from $\alg{A}$ to $\alg{B}$.
     Let $E(f,g) = \{ a \in A : f(a) = g(a) \}$ (the \defin{equalizer} of $f$ and $g$). 
     1. $E(f,g)$ is a subuniverse of $\alg{A}$.
     2. If $X \subseteq A$ and $X$ generates $\alg{A}$ and $\restr{f}{X} = \restr{g}{X}$, then $f = g$. 
     3. If $\alg{A}, \alg{B}$ are finite and $X$ generates $\alg{A}$, then $|\!\Hom{\alg{A},\alg{B}}| \leq |B|^{|X|}$.
  -/

  parameter {S : signature} 
  parameters {A : algebra_on υ S} {B : algebra_on τ S}
  
  -- equalizer for generic functions
  def equalizer (h : υ → τ) (g : υ → τ) : υ → Prop := λ (x : υ), h x = g x 

  -- equalizer for homomorphisms
  def equalizer_of_homs (h : υ → τ) (g : υ → τ) 
  (hh : homomorphic A B h) (hg : homomorphic A B g) : υ → Prop := 
  λ (ai : υ), h ai = g ai 

  -- 1. The equalizer $E(f,g)$ is a subuniverse of $\alg{A}$.
  lemma equalizer_is_subuniverse
  (h : υ → τ) (g : υ → τ) (hh : homomorphic A B h)  (hg : homomorphic A B g) : 
  is_subuniverse A (equalizer h g) := 
    assume (f : S.F) (tuple : S.ρ f → υ),
    assume (h₁ : ∀ i, (equalizer h g) (tuple i)),
    have h₂ : h ∘ tuple = g ∘ tuple, from funext h₁, 
      calc h (A f tuple) = (B f) (h ∘ tuple): hh f tuple
                     ... = (B f) (g ∘ tuple): congr_arg (B f) h₂ 
                     ... = g (A f tuple) : by rw (hg f tuple)

  lemma equalizer_of_homs_is_subuniverse (h : υ → τ) (g : υ → τ) 
  (hh : homomorphic A B h) (hg : homomorphic A B g) : 
  is_subuniverse A (equalizer_of_homs h g hh hg) := 
    assume (f : S.F) (tuple : S.ρ f → υ),
    assume (h₁ : ∀ i, (equalizer_of_homs h g hh hg) (tuple i)),
    have h ∘ tuple = g ∘ tuple, from funext h₁, 
    calc h (A f tuple) = (B f) (h ∘ tuple): hh f tuple
                   ... = (B f) (g ∘ tuple): congr_arg (B f) this 
                   ... = g (A f tuple) : by rw (hg f tuple)

/- Here's a "paper-and-pencil" proof of equalizer_is_subuniverse:

  Let $\rho$ be the similarity type of $\alg{A}$ and $\alg{B}$, and 
  $f$ a (say, $n$-ary) operation symbol in $\rho$. Then, 
  for every tuple $(a_1, \dots, a_n) \in E(h,g)^n$,
  \begin{align*}
    h(f^{\alg{A}}(a_1, \dots, a_n)) &= f^{\alg{B}}(h(a_1), \dots, h(a_n))\\
                                    &= f^{\alg{B}}(g(a_1), \dots, g(a_n))
                                     = g(f^{\alg{A}}(a_1, \dots, a_n)).
  \end{align*}
  Therefore, $E(f,g)$ is closed under $p$.  Since $p$ was arbitrary, 
  $E(f,g)$ is closed under all operations in $\rho$ and is thus a 
  subuniverse of $\alg{A}$.
-/


--     2. If $X \subseteq A$ and $X$ generates $\alg{A}$ and $\restr{f}{X} = \restr{g}{X}$, then $f = g$. 


def generates (X : υ → Prop) : Prop := ∀ (SX : υ → Prop), --if B contains X and is a subalgebra of A, then B = A
∀ x, (X x → (SX x)) →  is_subuniverse A SX → is_subuniverse SX (λ z, true)

lemma homs_determined_on_gens (h : υ → τ) (g : υ → τ)
(hh : @homomorphic S A B h) (hg : @homomorphic S A B g) (X : υ → Prop) : 
(is_generating X A) → (∀ x, h x = g x) → h = g := sorry
 /- 
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
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            