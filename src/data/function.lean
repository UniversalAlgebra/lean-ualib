import data.seq

open seq (map)

instance set_type {α} : has_coe_to_sort (set α) :=
⟨_, subtype⟩

namespace function

def op (α n) :=
seq α n → α

def restrict {α β n} (f : seq α n → β) (γ : set α) (x : seq γ n) : β :=
f (map coe x)

end function
