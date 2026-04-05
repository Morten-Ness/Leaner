import Mathlib

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [Semiring T]

variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

variable (b : Basis m R S) (c : Basis n S T)

theorem smulTower_leftMulMatrix (x) (ik jk) :
    Algebra.leftMulMatrix (b.smulTower c) x ik jk =
      Algebra.leftMulMatrix b (Algebra.leftMulMatrix c x ik.2 jk.2) ik.1 jk.1 := by
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, mul_comm, Module.Basis.smulTower_apply,
    Module.Basis.smulTower_repr, Finsupp.smul_apply, smul_eq_mul, map_smul, mul_smul_comm,
    coe_lmul_eq_mul, LinearMap.mul_apply']

