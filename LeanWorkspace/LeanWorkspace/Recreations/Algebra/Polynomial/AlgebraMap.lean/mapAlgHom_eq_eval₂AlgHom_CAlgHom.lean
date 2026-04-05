import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem mapAlgHom_eq_eval₂AlgHom_CAlgHom (f : A →ₐ[R] B) : Polynomial.mapAlgHom f = Polynomial.eval₂AlgHom
    (Polynomial.CAlgHom.comp f) Polynomial.X (fun a => (commute_X (Polynomial.C (f a))).symm) := by
  rfl

