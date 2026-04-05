import Mathlib

variable {ι : Type*} [Preorder ι] (G : ι → Type*)

variable [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

theorem quotientMk_of (i x) : Ideal.Quotient.mk _ (.of ⟨i, x⟩) = of G f i x := rfl

