import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem _root_.Equiv.Perm.prod_comp' (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → ι → M)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x ∈ s, f (σ x) x) = ∏ x ∈ s, f x (σ.symm x) := by
  convert σ.prod_comp s (fun x => f x (σ.symm x)) hs
  rw [Equiv.symm_apply_apply]

