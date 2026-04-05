import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ → M) :
    ∏ x ∈ s.map e, f x = ∏ x ∈ s, f (e x) := by
  rw [Finset.prod, Finset.map_val, Multiset.map_map]; rfl

