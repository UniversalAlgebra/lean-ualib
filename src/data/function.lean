import data.seq

open seq (map)

instance set_type {α} : has_coe_to_sort (set α) :=
⟨_, subtype⟩

namespace function

def op (α n) :=
seq α n → α

def restrict {α β n} (f : seq α n → β) (γ : set α) (x : seq γ n) : β :=
f (map coe x)

inductive range_seq {α} {β : Type*} (f : α → β) {n} : set (seq β n)
| intro (a) : range_seq (map f a)

end function
