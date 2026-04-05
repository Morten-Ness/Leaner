import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [SMul R M] [SMul R S] [SMul S M] [IsScalarTower R S M]

theorem mul_iff_right [Mul R] [IsScalarTower R R M] (ha : IsSMulRegular M a) :
    IsSMulRegular M (a * b) ↔ IsSMulRegular M b := ⟨IsSMulRegular.of_mul, IsSMulRegular.mul ha⟩

