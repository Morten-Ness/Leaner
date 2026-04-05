import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_comp_equiv {f : κ → M} (e : ι ≃ κ) : s.prod (f ∘ e) = (s.map e).prod f := by simp

