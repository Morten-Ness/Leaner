import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem cancel_left {g₁ g₂ : A →ₐ[R] B} {f : B →ₐ[R] C} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ := ⟨fun h => AlgHom.ext <| fun _ ↦ hf.eq_iff.mp <| AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

