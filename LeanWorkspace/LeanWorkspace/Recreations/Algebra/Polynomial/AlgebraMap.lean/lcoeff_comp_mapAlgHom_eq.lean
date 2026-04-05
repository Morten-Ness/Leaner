import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem lcoeff_comp_mapAlgHom_eq (f : A →ₐ[R] B) (n : ℕ) :
    (lcoeff B n).restrictScalars R ∘ₗ (Polynomial.mapAlgHom f).toLinearMap =
      f.toLinearMap ∘ₗ (lcoeff A n).restrictScalars R := by
  ext f; simp

