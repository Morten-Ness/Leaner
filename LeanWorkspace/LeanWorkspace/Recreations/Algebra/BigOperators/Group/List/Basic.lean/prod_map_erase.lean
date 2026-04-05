import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_map_erase [DecidableEq α] (f : α → M) {a} :
    ∀ {l : List α}, a ∈ l → f a * ((l.erase a).map f).prod = (l.map f).prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    · simp only [map, erase_cons_tail (not_beq_of_ne ne.symm), prod_cons, prod_map_erase _ h,
        mul_left_comm (f a) (f b)]

