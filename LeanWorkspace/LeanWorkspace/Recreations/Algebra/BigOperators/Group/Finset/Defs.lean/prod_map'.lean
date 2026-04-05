import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_map' (s : Finset ι) (e : ι ↪ κ) :
    Finset.prod (s.map e) = fun (f : κ → M) => ∏ x ∈ s, f (e x) := by
  funext f
  simp

