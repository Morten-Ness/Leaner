import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem mapAlgHom_comp (Polynomial.C : Type*) [Semiring Polynomial.C] [Algebra R Polynomial.C] (f : B →ₐ[R] Polynomial.C) (g : A →ₐ[R] B) :
    (Polynomial.mapAlgHom f).comp (Polynomial.mapAlgHom g) = Polynomial.mapAlgHom (f.comp g) := by
  ext <;> simp

