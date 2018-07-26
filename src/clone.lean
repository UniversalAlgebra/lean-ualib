import basic

section
parameters (α : Type*) (F : Type*)

structure is_clone (C : set (op F α)) :=
(proj_closed : ∀ k, (λ (x : F → α), x k) ∈ C)
(comp_closed : ∀ f (g : F → op F α), f ∈ C → (∀ i, g i ∈ C) → (λ x, f (λ i, g i x)) ∈ C)

parameter (X : set (op F α))

-- The smallest clone containing X
inductive clo : set (op F α)
| proj (k) : clo (π k)
-- there are like two different ways to make this SEGFAULT lmao
| comp {f} {g : F → op F α} :
    f ∈ X → (∀ i, clo (g i)) → clo (λ x, f (λ i, g i x))

theorem clo_contains : X ⊆ clo :=
begin
  intros _ h,
  apply clo.comp h,
  apply clo.proj
end

theorem clo_is_clone : is_clone clo :=
{ proj := clo.proj,
  comp := begin
    intros _ _ fc gc,
    induction fc with _ f _ _ _ ih,
    { apply gc },
    { apply @clo.comp f,
      assumption,
      apply ih }
  end }

theorem clo_is_smallest (Y : set (op F α)) :
  is_clone Y → X ⊆ Y → clo ⊆ Y :=
begin
  intros hY hX f hf,
  induction hf,
  { apply hY.proj_closed },
  { apply hY.comp_closed,
    apply hX,
    repeat { assumption } }
end

end

section
parameters {S : signature} (A : algebra S)

-- TODO: relate clone of term operations to term algebra

end