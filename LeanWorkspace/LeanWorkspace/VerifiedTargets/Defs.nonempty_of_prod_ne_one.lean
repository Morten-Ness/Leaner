import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem nonempty_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : s.Nonempty := s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ Finset.prod_empty) id

