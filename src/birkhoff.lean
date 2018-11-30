/-birkhoof.lean -- Birkhoff's HSP Theorem in Lean

  Author: William DeMeo <williamdemeo@gmail.com>
  Date: 26 Nov 2018

  References
  [1] Bergman, Clifford, "Universal algebra," CRC Press, 2012

  Copyright (c) 2018 William DeMeo  
  
  See the LICENSE file in 
  \url{https://github.com/UniversalAlgebra/lean-ualib/blob/master/LICENSE}
-/

import basic
import subuniverse 
import data.set
import data.quot
--import data.setoid 

universe s -- where operation (s)ymbols live
universe u -- where structure (u)niverses (i.e. carriers) live
universe u' -- where structure (u)niverses (i.e. carriers) live
universe u'' -- where structure (u)niverses (i.e. carriers) live
universe a -- where (a)rities live

section

  parameter υ : Sort u  -- A carrier type
  parameter τ : Sort u  -- Another carrier type

  -- (defined in basic.lean)  def op (υ : Sort u) (α : Sort a) := (α → υ) → υ  
  -- (defined in basic.lean) structure signature := mk :: (F : Sort s) (ρ : F → Sort a)

  parameters {S : signature}
  open set
  open subuniverse
  -- Elementary Facts ------------------------------------------

  /- Lemma (cf. Ex. 1.16.6 of [1])
     Let $f$ and $g$ be homomorphisms from $\mathbf A$ to $\mathbf B$.
     Let $E(f,g) = \{ a \in A : f(a) = g(a) \}$ (the **equalizer** of $f$ and $g$). 
     1. $E(f,g)$ is a subuniverse of $\mathbf A$.
     2. If $X \subseteq A$, if $X$ generates $\mathbf A$, and if the restrictions of f and g
        to $X$ agree---i.e., $f |_X = g |_X$---then $f = g$. 
     3. If $\mathbf A$, $\mathbf B$ are finite algebras and $X$ generates $\mathbf A$, then 
        $|Hom(\mathbf A, \mathbf B)| \leq |B|^{|X|}$. -/

  -- equalizer for generic functions
 --(A : algebra_on S α) (B : algebra_on S β) (C : algebra_on S γ) -- {I ζ : Type} {R : I → set α} 
  def equalizer {α : Type u} {β : Type u'}
  (h : α → β) (g : α → β) : set α := λ (x : α), h x = g x 

  -- indicates whether h is a homomorphism  
  def hom {A : algebra S} {B : algebra S} (h : A → B) 
  : Prop := ∀ f a, h (A f a) = B f (h ∘ a)


  -- composition of homomorphisms is a homomorphism
  lemma hom_comp_hom_of_hom {A : algebra S} {B : algebra S} {C : algebra S}
  (h : A → B)  {h₁ : hom h} (g : B → C) {h₂ : hom g} : 
  hom (g ∘ h) := assume f a, show (g ∘ h)(A f a) = C f (g ∘ h ∘ a), from 
  have h₃ : (g ∘ h)(A f a) = g (h (A f a)), from  rfl,
  calc (g ∘ h)(A f a) = g ((B f) (h ∘ a)) : (h₁ f a) ▸ h₃ 
                  ... = (C f) (g ∘ h ∘ a) : h₂ f (h ∘ a)

  -- the set on which two homs agree
  def equalizer_of_homs {A : algebra S} {B : algebra S}
  (h : A → B) (g : A → B) {hh : hom h} {hg : hom g} : set A := λ a, h a = g a 


  -- 1. The equalizer $E(f,g)$ is a subuniverse of $\mathbf A$.
  lemma sub_equalizer_of_homs {A : algebra S} {B : algebra S}
  (h : A → B) (g : A → B) (hh : hom h)  (hg : hom g) : 
  Sub A (equalizer h g) := 
    assume f a (h₁: ∀ x, a x ∈ equalizer h g),
    show A f a ∈ (equalizer h g),  from 
      have h₂ : h ∘ a = g ∘ a, from funext h₁, 
      show h (A f a) = g (A f a), from 
        calc h (A f a) = (B f) (h ∘ a): hh f a
                   ... = (B f) (g ∘ a): congr_arg (B f) h₂ 
                   ... = g (A f a) : eq.symm (hg f a)


  -- 2. If $X ⊆ A$, if $Sg(X) = \mathbf A$, and if $f x = g x$ for all $x ∈ X$, then $f = g$. 

  lemma mem_of_eq {α : Type u} (s t : set α) : s = t →  ∀ x, x ∈ s → x ∈ t := 
  begin intros h x h', rw ←h, assumption end

  lemma hom_determined_on_gens {A : algebra S} {B : algebra S}
  (h : A → B) (g : A → B) (hh : hom h) (hg : hom g) (X : set A) : 
  X ⊆ equalizer h g → Sg A X ⊆ equalizer h g := 
  -- Idea of the proof: we have
  --     1. X ⊆ equalizer h g,
  --     2. Sub (equalizer h g), i.e., equalizer h g is a subalgebra
  --     3. and Sg X is the smallest subalgebra containing X
  -- Therefore, Sg X ⊆ equalizer h g, which means h = g on Sg X.
  assume h₁ : X ⊆ equalizer h g, show Sg A X ⊆ equalizer h g, from 
  assume a (h₂ : a ∈ Sg A X), show a ∈ equalizer h g, from 
  have h₃ : Sub A (equalizer h g), from (sub_equalizer_of_homs h g hh hg),
      (sInter_mem A a) h₂ h₃ h₁


  -- Here's another proof of the last result using the recursor of Y.
  lemma hom_determined_on_gens_rec {A : algebra S} {B : algebra S} 
  (h : A → B) (g : A → B)  (hh : hom h) (hg : hom g) (X : set A) : 
  (∀ x, x ∈ X → h x = g x) → (∀ a, a ∈ Sg A X → h a = g a) := 
  assume (h₁ : ∀ x, x ∈ X → h x = g x), 
  assume a (h₂ : a ∈ Sg A X), show h a = g a, from 
    have h₃ : a ∈ Y A X, from mem_of_eq (Sg A X) (Y A X) (sg_inductive A X) a h₂,
    Y.rec 
      --base step: assume a = x ∈ X
      h₁ 
      --inductive step: assume a = A f b for some b with ∀ i, b i ∈ Sg X
      ( assume f b (h₄ : ∀ i, b i ∈ Y A X)  (h₅ : ∀ i, h (b i) = g (b i)),
        show h (A f b) = g (A f b), from 
        have h₆ : h ∘ b = g ∘ b, from funext h₅, 
        calc h (A f b) = (B f) (h ∘ b) : hh f b
                   ... = (B f) (g ∘ b) : congr_arg (B f) h₆    
                   ... = g (A f b)     : eq.symm (hg f b)) h₃ 


  -- def surjective {α : Type u} {β : Type u'} (f : α → β ) : Prop := ∀ y, ∃ x, f x = y
  -- def injective {α : Type u} {β : Type u'} (f : α → β) : Prop := ∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂
  -- def bijective {α : Type u} {β : Type u'} (f : α → β) : Prop := injective f ∧ surjective f

  open classical function
  local attribute [instance] prop_decidable

  noncomputable def inverse' {α : Type u} {β : Type u'} (f : α → β) (default : α)  : β → α :=
  λ b, if h : ∃ a, f a = b then some h else default

  -- The right inverse of a surjective function.
  noncomputable def right_inv {α : Type u} {β : Type u'} (f : α → β)
  (h₁ : surjective f) : β → α := λ b, some (h₁ b)

  -- A surjective function has a right inverse.
  lemma right_inv_is_right_inverse {α : Type u} {β : Type u'} (f : α → β) 
  (h₁ : surjective f) : ∀ b, b = f ((right_inv f h₁) b) := 
  assume b, have h₂ : (right_inv f h₁) b = some (h₁ b), from rfl,
  have h₃ : f (some (h₁ b)) = b, from some_spec (h₁ b),
  eq.subst (eq.symm h₂) (eq.symm h₃)

  -- Right inverse of epi is hom.
  lemma right_inv_of_epi_is_hom {A : algebra S} {B : algebra S} (g : A → B) 
  (h₁ : surjective g) (h₂ : hom g) : hom (right_inv g h₁) := 
  let g_inv := (right_inv g h₁) in 
  show hom g_inv, from 
  assume f b, show g_inv (B f b) = A f (g_inv ∘ b), from  sorry
  -- B f b = B f (g ∘ g_inv ∘ b) = g (A f (g_inv ∘ b))
  -- g (g_inv (B f b)) = B f b 
  -- This seems to show only that the pair
  -- (g_inv (B f b), A f (g_inv ∘ b)) belongs to the kernel of g.
  
  def ker {α : Type u} {β : Type u'} (f : α → β) : α → α → Prop := λ a b, f a = f b

  /-Lemma (Ex. 1.26.8.a. [1])
    If $f : A → B$ is epi
       $g : A → C$ is hom
       $ker f ⊆ ker g$
    Then $∃ h : B → C$ with $g = h ∘ f$ and $h$ is a homomorphism.
  -/
  lemma hom_facotor_down {A : algebra S} {B : algebra S} {C : algebra S} 
  -- assumptions:
  (f : A → B) (hf : hom f) (hs : surjective f)    -- f is epi
  (g : A → C) (hg : hom g)                        -- g is hom
  (kk : ∀ a b, ker f a b → ker g a b) :           -- ker f ⊆ ker g
  -- conclusion:
  ∃ h : B → C, (g = h ∘ f) ∧ (hom h) := 
  -- proof:
  let h := g ∘ (right_inv f hs)  in 
    have h₁ : hom h, from sorry,
    have h₃ : g = h ∘ f, from sorry, 
    exists.intro h (and.intro h₃ h₁) 
  /-
       A---f----> B
       |        /
       g       h
       |     /
       |   /
       V L
       C
  -/
 
  /-Lemma (Ex. 1.26.8.b) [1])
    If $f : A → B$ is hom
       $g : A → C$ is epi
       $ker g ⊆ ker f$
    Then $∃ h : B → C$ with $f = h ∘ g$ and $h$ is a homomorphism.
  -/
  lemma hom_facotor_up {A : algebra S} {B : algebra S} {C : algebra S} 
  -- assumptions:
  (f : A → B) (hf : hom f)                        -- f is hom
  (g : A → C) (hg : hom g) (hs : surjective g)    -- g is epi
  (kk : ∀ a b, ker g a b → ker f a b) :           -- ker g ⊆ ker f
  -- conclusion:
  ∃ h : C → B,  (f = h ∘ g) ∧ (hom h) 
  := 
  -- proof:
  let h := f ∘ (right_inv g hs)  in 
    have h₁ : hom h, from sorry,
    have h₃ : f = h ∘ g, from sorry, 
    exists.intro h (and.intro h₃ h₁) 
  
  /-
       A----f----> B
       |         7
       g       /
       |     h
       |   /
       V /
       C
 -/
 
end                                                                                                                                                                                                                                            



namespace H -- homomorphisms
section 
  parameter S : signature
  variables {α : Type*} {β : Type*} {A : algebra S} {B : algebra S}
  open subuniverse 
  --  def preorder (R : α → α → Prop) : Prop := reflexive R ∧ transitive R
  --  def partial_order (R : α → α → Prop) : Prop := preorder R ∧ anti_symmetric R

  -- kernel of a set map
  def ker (f : α → β) : α → α → Prop := 
  λ a a', f a = f a'

  -- kernel of an algebra map  (shouldn't need two separate defs for ker and kernel)
  def kernel (f : A → B) : A → A → Prop := 
  λ a a', f a = f a'

  lemma ker_is_equivalence (h : α → β) : equivalence (ker h) :=
  have hr : reflexive (ker h), from assume x, rfl,
  have hs : symmetric (ker h), from 
    assume x y (hxy : h x = h y), eq.symm hxy,
  have ht : transitive (ker h), from 
    assume x y z (h₁ : h x = h y) (h₂ : h y = h z), eq.trans h₁ h₂,
  ⟨hr, hs, ht⟩ 

  #check ker_is_equivalence 

  lemma kernel_is_equivalence 
  (h : A → B) (hh : homomorphic h) : equivalence (kernel h) :=
  have hr : reflexive (kernel h), from assume x, rfl,
  have hs : symmetric (kernel h), from 
    assume x y (hxy : h x = h y), eq.symm hxy,
  have ht : transitive (kernel h), from 
    assume x y z (h₁ : h x = h y) (h₂ : h y = h z), eq.trans h₁ h₂,
  ⟨hr, hs, ht⟩ 

  #check kernel_is_equivalence 

  open quot
  def kernel.setoid (h : A → B) (hh : homomorphic h) : setoid A := 
  setoid.mk (kernel h) (kernel_is_equivalence h hh)

  -- A homomorphic image (i.e., a quotient modulo kernel of a hom).
  def quotient_by_hom_kernel (h: A → B) (hh: homomorphic h) := 
  quot (kernel.setoid h hh).r

  def hom_image (h: A → B) (hh: homomorphic h) : set B := λ b, ∃ a, h a = b

  open classical function
  local attribute [instance] prop_decidable

  -- A homomorphic image is a subalgebra.
  lemma hom_image_is_sub (h : A → B) (hh : homomorphic h) : 
  Sub B (hom_image h hh) := 
  assume (f : S.F) (b : S.ρ f → B.fst) (h₁ : ∀ i, b i ∈ (hom_image h hh)), 
  show (hom_image h hh) (B f b),  -- must show ∃ x ∈ A, h x = B f b
  from  
    have h₂ : ∀ i, ∃ x, h x = b i, from h₁, 
    have h₃ : ∀ i, h (some (h₂ i)) = b i, from assume i, some_spec (h₂ i),
    have h₆ : (λ i, h (some (h₂ i)))= b, from funext h₃, 
    have h₄ : h (A f (λ i, some (h₂ i))) = B f b, by rw [hh, congr_arg (B f) h₆],
    exists.intro (A f (λ i, some (h₂ i))) h₄ 
  -- This is pretty ugly.  There's probably a better way.


end


end H

namespace S -- subalgebras
section
end
end S

namespace P -- products
section
end
end P



















/- Miscellaneous Notes  

Recall, 
  - `Prop` is syntactic sugar for `Sort 0`, the bottom of the type hierarchy.
    Like the other type universes, it is closed under the arrow constructor 
    (if `p q : Prop`, then `p → q : Prop`)
  -`Type u` is syntactic sugar for `Sort (u+1)`
    (`Prop = Type -1` and `Sort 1 = Type 0`)


-/
/-
Refereces:
[1] @book {MR2839398,
    AUTHOR = {Bergman, Clifford},
     TITLE = {Universal algebra},
    SERIES = {Pure and Applied Mathematics (Boca Raton)},
    VOLUME = {301},
      NOTE = {Fundamentals and selected topics},
 PUBLISHER = {CRC Press, Boca Raton, FL},
      YEAR = {2012},
     PAGES = {xii+308},
      ISBN = {978-1-4398-5129-6},
   MRCLASS = {08-02 (06-02 08A40 08B05 08B10 08B26)},
  MRNUMBER = {2839398 (2012k:08001)},
MRREVIEWER = {Konrad P. Pi{\'o}ro},
}
-/