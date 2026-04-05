import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem _root_.Equiv.Perm.prod_comp (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → M)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x ∈ s, f (σ x)) = ∏ x ∈ s, f x := by
  convert (Finset.prod_map s σ.toEmbedding f).symm
  exact (map_perm hs).symm

