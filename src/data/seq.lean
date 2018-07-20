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

def tail {α n} (a : seq α (n + 1)) : seq α n :=
λ i, a (fin.succ i)

def reduce {α β} (f : β → α → β) (b : β) : Π {n}, seq α n → β
| 0 _       := b
| (n + 1) a := f (reduce (tail a)) (a 0)

end seq
