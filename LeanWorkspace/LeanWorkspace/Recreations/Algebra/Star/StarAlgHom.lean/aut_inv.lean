import Mathlib

variable {S R : Type*} [Mul R] [Add R] [Star R] [SMul S R]

theorem aut_inv (f : R ≃⋆ₐ[S] R) : f⁻¹ = f.symm := rfl

