import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem cancel_right {g₁ g₂ : B →ₐ[R] C} {f : A →ₐ[R] B} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := by
  constructor
  · intro h
    ext b
    rcases hf b with ⟨a, rfl⟩
    exact DFunLike.congr_fun h a
  · intro h
    rw [h]
