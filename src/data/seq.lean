-- /Sequences/ of length n with elements in α
def seq (α n) :=
fin n → α

namespace seq

/- Apply a function pointwise to a sequence -/
def map {α β} (f : α → β) {n} (a : seq α n) : seq β n :=
λ i, f (a i)

/- Quantify over every element of a sequence -/
def all {α n} (a : seq α n) (P : α → Prop) :=
∀ i, P (a i)

end seq
