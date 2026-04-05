import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem adjoin_ext {s : Set A} ⦃φ₁ φ₂ : Algebra.adjoin R s →ₐ[R] B⦄
    (h : ∀ x hx, φ₁ ⟨x, Algebra.subset_adjoin hx⟩ = φ₂ ⟨x, Algebra.subset_adjoin hx⟩) : φ₁ = φ₂ := ext fun ⟨x, hx⟩ ↦ Algebra.adjoin_induction h (fun _ ↦ φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ ↦ by convert congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ _ _ h₁ h₂ ↦ by convert congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl) hx

