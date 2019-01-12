import basic

section
  parameters {S : signature} (X :Type*)
  local notation `F` := S.F
  local notation `ρ` := S.ρ 

  inductive term
  | var         : X → term
  | app (f : F) : (ρ f → term) → term

  def Term : algebra S := ⟨term, term.app⟩
end

section
  open term
  parameters {S : signature} (X :Type*) {A : algebra S} -- 
  definition F := S.F
  definition ρ := S.ρ 
  definition 𝕋 := @Term S
  definition 𝕏 := @var S X

  -- To prove that the free algebra is free, we show that
  -- the lift of an arbitrary function h : X → A is a homomorphism
  -- and that it is the unique homomorphism extending h.

  -- Definition of the lift of a function.
  definition lift_of (h : X → A) : 𝕋(X) → A
  | (var x) := h x
  | (app f a) := (A f) (λ x, lift_of (a x))

  -- The lift of a function is a homomorphism.
  lemma lift_is_hom (h : X → A) : homomorphic (lift_of h) :=
  λ f a, show lift_of h (app f a) = A f (lift_of h ∘ a), from rfl

  -- The lift of a function is unique among homomorphic lifts.
  lemma lift_is_unique : ∀ {h h' : 𝕋(X) → A},
  homomorphic h → homomorphic h' → h ∘ 𝕏 = h' ∘ 𝕏 → h = h' :=
  assume (h h' : 𝕋(X) → A) (h₁ : homomorphic h)
    (h₂ : homomorphic h')(h₃ : h ∘ 𝕏 = h' ∘ 𝕏),
    show h = h', from 
      have h₀ : ∀ t : 𝕋(X), h t = h' t, from 
        assume t : 𝕋(X), 
        begin
          induction t with t f a ih₁ ,
          show h (𝕏 t) = h' (𝕏 t),
          { apply congr_fun h₃ t },

          show h (app f a) = h' (app f a),
          { have ih₂  : h ∘ a = h' ∘ a, from funext ih₁,
            calc h (app f a) = A f (h ∘ a) : h₁ f a
                         ... = A f (h' ∘ a) : congr_arg (A f) ih₂ 
                         ... = h' (app f a) : (h₂ f a).symm }
        end,
      funext h₀ 





  -- begin
  --   assume (h h' : 𝔽(X) → A)
  --          (h₁ : homomorphic h)
  --          (h₂ : homomorphic h')
  --          (h₃ : h ∘ 𝕏 = h' ∘ 𝕏),
  
  --   funext t, show h t = h' t,
  
  --   induction t with t f a ih₁ ,

  --   show h (𝕏 t) = h' (𝕏 t),
  --   { apply congr_fun h₃ t },

  --   show h (app f a) = h' (app f a),
  --   { have ih₂  : h ∘ a = h' ∘ a, from funext ih₁,
  --     calc h (app f a) = A f (h ∘ a) : h₁ f a
  --                ... = A f (h' ∘ a) : congr_arg (A f) ih₂ 
  --                ... = h' (app f a) : (h₂ f a).symm }
  -- end


end