import Mathlib

variable (ι : Type*)

variable {R : Type*}

variable (A : ι → Type*)

variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

theorem algHom_comp {B C : Type*} [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]
    (g : ∀ i, C →ₐ[R] A i) (h : B →ₐ[R] C) :
    (Pi.algHom R A g).comp h = Pi.algHom R A (fun i ↦ (g i).comp h) := rfl

