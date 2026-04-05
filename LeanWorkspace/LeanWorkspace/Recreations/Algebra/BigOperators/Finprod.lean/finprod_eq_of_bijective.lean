import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_eq_of_bijective {f : α → M} {g : β → M} (e : α → β) (he₀ : Function.Bijective e)
    (he₁ : ∀ x, f x = g (e x)) : ∏ᶠ i, f i = ∏ᶠ j, g j := by
  rw [← finprod_mem_univ f, ← finprod_mem_univ g]
  exact finprod_mem_eq_of_bijOn _ he₀.bijOn_univ fun x _ => he₁ x

