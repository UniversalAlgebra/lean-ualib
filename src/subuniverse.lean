import basic
import data.set


section
parameters {α : Type*} {S : signature} (A : algebra_on S α)
open set

def Sub (β : set α) : Prop :=
∀ f (a : S.ρ f → α), (∀ x, a x ∈ β) → A f a ∈ β

-- N.B. A f a ∈ β   is notation for   β (A f a)


def Sg (X : set α) : set α :=
⋂₀ {U | Sub U ∧ X ⊆ U}

lemma sInter_imp {X : set α} (x : α) : x ∈ Sg X → (∀ {U : set α }, 
  Sub U → X ⊆ U → x∈ U) := 
  assume (h1 : x ∈ Sg X) U (h2 : Sub U) (h3 : X ⊆ U), show x ∈ U, from 
  have h4 : U ∈ {U | Sub U ∧ X ⊆ U}, from and.intro h2 h3,
  have h5 : x ∈ ⋂₀ {U | Sub U ∧ X ⊆ U}, from h1,
  have h6 : ∀ Y ∈ {U | Sub U ∧ X ⊆ U}, x∈ Y, from h1, h6 U h4

lemma mem_gens (X : set α) : X ⊆ Sg X := 
assume x (h1 : x ∈ X), show x ∈ ⋂₀ {U | Sub U ∧ X ⊆ U}, from 
  assume V (h2 : V ∈ {U | Sub U ∧ X ⊆ U}),  show x ∈ V, from 
    have h3: Sub V ∧ X ⊆ V, from h2, 
    h3.right h1

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
  have h2 : X ⊆ Y, from 
    assume x (h3 : x ∈ X), show x  ∈ Y, from Y.var x h3,

  have h : Sub Y, from 
    assume f a (h1 : ∀ x, Y (a x)), show Y (A f a), from Y.app f a h1,

  have l : Sg X ⊆ Y, from 
    assume u (h3 : u ∈ Sg X), show u ∈ Y, from sInter_imp u h3 h h2,

  have r : Y ⊆ Sg X, from 
    assume a (h4: Y a), show (Sg X) a, from
      Y.rec 
        (assume x (h5 : x ∈ X), show x ∈ Sg X, from mem_gens X h5)
        (assume f a (h6 : ∀ i, Y (a i)) (h7 : ∀ i, (Sg X) (a i)),
        show (Sg X) (A f a), from 
          have h8 : (A f a) ∈ Y, from Y.app f a h6,
          have h9 : ∀ V ∈ {U | Sub U ∧ X ⊆ U}, (A f a) ∈ V, from 
            assume V (h10 : Sub V ∧ X ⊆ V), 
            have h11 : Y ⊆ V, from (MinSubY V) h10.left h10.right, 
              h11 h8,
            h9
        ) h4,
  subset.antisymm l r
end



-- Miscellaneous Notes

-- ⋂₀ is notation for sInter (S : set (set α)) : set α := Inf S,
-- and Inf S is defined as follows:
-- Inf          := λs, {a | ∀ t ∈ s, a ∈ t },
-- So, if S : set (set α) (i.e., a collection of sets of type α),
-- then Inf S is the intersection of the sets in S.
