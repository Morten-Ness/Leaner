import Mathlib

section

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem algebraMap_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A) := funext Algebra.algebraMap_eq_smul_one

end

section

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem algebraMap_eq_smul_one (r : R) : algebraMap R A r = r • (1 : A) := calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_one _).symm
    _ = r • (1 : A) := (Algebra.smul_def r 1).symm

end

section

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem algebra_ext {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] (P Q : Algebra R A)
    (h : ∀ r : R, (haveI := P; algebraMap R A r) = haveI := Q; algebraMap R A r) :
    P = Q := by
  replace h : P.algebraMap = Q.algebraMap := DFunLike.ext _ _ h
  have h' : (haveI := P; (· • ·) : R → A → A) = (haveI := Q; (· • ·) : R → A → A) := by
    funext r a
    rw [P.smul_def', Q.smul_def', h]
  rcases P with @⟨⟨P⟩⟩
  congr

end

section

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem left_comm (x : A) (r : R) (y : A) :
    x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  rw [← mul_assoc, ← Algebra.commutes, mul_assoc]

end

section

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem right_comm (x : A) (r : R) (y : A) :
    x * algebraMap R A r * y = x * y * algebraMap R A r := by
  rw [mul_assoc, Algebra.commutes, ← mul_assoc]

end
