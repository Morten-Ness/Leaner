import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_of_eqOn_one (hf : s.EqOn f 1) : ∏ᶠ i ∈ s, f i = 1 := by
  rw [← finprod_mem_one s]
  exact finprod_mem_congr rfl hf

