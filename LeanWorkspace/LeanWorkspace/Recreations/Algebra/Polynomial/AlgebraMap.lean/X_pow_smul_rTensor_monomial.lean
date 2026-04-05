import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem X_pow_smul_rTensor_monomial [CommSemiring S] [Algebra R S] {N : Type*}
    [AddCommMonoid N] [Module R N] (k : ℕ) (sn : S ⊗[R] N) :
    Polynomial.X (R := S) ^ k • (LinearMap.rTensor N ((monomial 0).restrictScalars R)) sn =
      (LinearMap.rTensor N ((monomial k).restrictScalars R)) sn := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul s n =>
    simp only [rTensor_tmul, coe_restrictScalars, monomial_zero_left]
    rw [smul_tmul', smul_eq_mul, mul_comm, C_mul_X_pow_eq_monomial]

