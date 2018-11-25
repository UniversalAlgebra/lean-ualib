import basic
import data.set


section
parameters {α : Type*} {S : signature} (A : algebra_on S α) {I ζ : Type} {R : I → set α} 
open set

def Sub (β : set α) : Prop :=
∀ f (a : S.ρ f → α), (∀ x, a x ∈ β) → A f a ∈ β

-- N.B. A f a ∈ β   is notation for   β (A f a)


def Sg (X : set α) : set α :=
⋂₀ {U | Sub U ∧ X ⊆ U}


def index_of_sub_above_X (X : set α) (C : I → set α) : I → Prop := λ i, Sub (C i) ∧ X ⊆ (C i) 


theorem Inter.intro {x : α} (C : I → set α) (h : ∀ i, x ∈ C i) : x ∈ ⋂ i, C i :=
by simp; assumption


theorem Inter.elim {x : α} (C : I → set α) (h : x ∈ ⋂ i, C i) (i : I) : x ∈ C i := 
by simp at h; apply h


lemma sub_of_sub_inter_sub (C : I → set α) : 
(∀ i, Sub (C i)) → Sub ⋂i, C i :=
  assume h : ∀ i, Sub (C i), show  Sub (⋂i, C i), from 
    assume f a (h1 : (∀ x, a x ∈ ⋂i, C i)), show A f a ∈ (⋂i, C i), from 
      have h4 : ∀ j, A f a ∈ C j, from 
        assume j : I, show A f a ∈ C j, from 
          have h3 : ∀ x, a x ∈ (C j), from assume x, Inter.elim C (h1 x) j,
      (h j) f a h3,
    Inter.intro C h4


lemma subset_X_of_SgX (X : set α) : X ⊆ Sg X := 
assume x (h1 : x ∈ X), show x ∈ ⋂₀ {U | Sub U ∧ X ⊆ U}, from 
  assume V (h2 : V ∈ {U | Sub U ∧ X ⊆ U}),  show x ∈ V, from 
    have h3: Sub V ∧ X ⊆ V, from h2, 
    h3.right h1


lemma sInter_mem {X : set α} (x : α) : 
x ∈ Sg X  →  ∀ {R : set α }, Sub R → X ⊆ R → x ∈ R := 
  (assume (h1 : x ∈ Sg X) (R : set α)  (h2 : Sub R) (h3 : X ⊆ R), 
    show x ∈ R, from h1 R (and.intro h2 h3))


lemma SubSgX (X : set α) : Sub (Sg X) := 
assume f a (h : ∀ i, a i ∈ Sg X), show A f a ∈ Sg X, from 
  assume U (h1 : Sub U ∧ X ⊆ U), show A f a ∈ U, from 
    have h3 : Sg X ⊆ U, from 
      assume r (h4 : r ∈ Sg X), show r ∈ U, from sInter_mem r h4 h1.left h1.right,
    have h5 : ∀ i, a i ∈ U, from assume i, h3 (h i),
    (h1.left f a h5)


lemma sInter_mem_of_mem {X : set α} (x : α) : 
x ∈ Sg X  ↔  ∀ {R : set α }, Sub R → X ⊆ R → x ∈ R := 
iff.intro
  (assume (h1 : x ∈ Sg X) (R : set α)  (h2 : Sub R) (h3 : X ⊆ R), 
    show x ∈ R, from h1 R (and.intro h2 h3))
  (assume (h1 : ∀ {R : set α}, Sub R → X ⊆ R → x ∈ R), 
    show x∈ Sg X, from h1 (SubSgX X) (subset_X_of_SgX X))


parameter (X : set α)

-- One way to make this SEGFAULT lol    <-- Siva, what do you mean? 
--                                          I don't get a segv here.
inductive Y : set α
| var (x : α) : x ∈ X → Y x
| app (f : S.F) (a : S.ρ f → α) : (∀ i, Y (a i)) → Y (A f a)


lemma SubY : (Sub Y) := 
assume f a (h: ∀ i, Y (a i)), show Y (A f a), from 
Y.app f a h 

lemma MinSubY (U : set α) : Sub U → X ⊆ U → Y ⊆ U :=
assume (h1 : Sub U) (h2 : X ⊆ U) a (h3 : Y a), show U a, from 
Y.rec
  (assume x (h4 : x ∈ X) (h5 : x ∈ Y), h2 h4)
  (assume f a (h6 : ∀ i, Y (a i)) (h7 : ∀ i, Y (a i) → U (a i)) (h8 : Y (A f a)), 
    have h9 : ∀ i, U (a i), from assume i, (h7 i) (h6 i), 
    show U (A f a), from h1 f a h9) h3 h3


theorem sg_inductive : Sg X = Y :=
  have h' : X ⊆ Y, from 
    assume x (h3 : x ∈ X), show x  ∈ Y, from Y.var x h3,

  have h : Sub Y, from 
    assume f a (h1 : ∀ x, Y (a x)), show Y (A f a), from Y.app f a h1,

  have l : Sg X ⊆ Y, from 
    assume u (h3 : u ∈ Sg X), show u ∈ Y, from (sInter_mem u) h3 h h',

  have r : Y ⊆ Sg X, from 
    assume a (h0: Y a), show (Sg X) a, from
      Y.rec 
        (assume x (h1 : x ∈ X), show x ∈ Sg X, from subset_X_of_SgX X h1)
        (assume f a (h2 : ∀ i, Y (a i)) (h3 : ∀ i, (Sg X) (a i)),
          show (Sg X) (A f a), from 
            have h4 : (A f a) ∈ Y, from Y.app f a h2,
            have h5 : ∀ T ∈ {U | Sub U ∧ X ⊆ U}, (A f a) ∈ T, from 
              assume T (h6 : Sub T ∧ X ⊆ T), 
              have h7 : Y ⊆ T, from (MinSubY T) h6.left h6.right, 
              h7 h4,
            h5
        ) h0,
  subset.antisymm l r
end



-- Miscellaneous Notes

-- ⋂₀ is notation for sInter (S : set (set α)) : set α := Inf S,
-- and Inf S is defined as follows:
-- Inf          := λs, {a | ∀ t ∈ s, a ∈ t },
-- So, if S : set (set α) (i.e., a collection of sets of type α),
-- then Inf S is the intersection of the sets in S.
