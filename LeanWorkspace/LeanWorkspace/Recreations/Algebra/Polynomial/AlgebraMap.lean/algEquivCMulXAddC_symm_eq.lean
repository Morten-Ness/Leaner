import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem algEquivCMulXAddC_symm_eq {R : Type*} [CommRing R] (a b : R) [Invertible a] :
    (Polynomial.algEquivCMulXAddC a b).symm = Polynomial.algEquivCMulXAddC (⅟a) (-⅟a * b) := by
  ext p : 1
  simp only [algEquivCMulXAddC_symm_apply, neg_mul, algEquivCMulXAddC_apply, map_neg, map_mul]
  congr
  simp [mul_add, sub_eq_add_neg]

