import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_map_equiv (e : ι ≃ κ) : (s.map e).prod (f ∘ e.symm) = s.prod f := by simp

