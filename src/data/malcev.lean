class has_ternary_op (α : Type*) := (ternary_op : α → α → α → α) 

class has_malcev_op (α : Type*) extends has_ternary_op α := 
(malcev_op_left : ∀ x y : α, ternary_op x y y = x) 
(malcev_op_right : ∀ x y : α, ternary_op y y x = x) 
