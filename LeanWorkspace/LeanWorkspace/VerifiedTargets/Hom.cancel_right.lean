import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem cancel_right {g₁ g₂ : B →ₐ[R] C} {f : A →ₐ[R] B} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := ⟨fun h => AlgHom.ext <| hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩

