import Mathlib

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

theorem smul_leftMulMatrix {G} [Group G] [DistribMulAction G S]
    [SMulCommClass G R S] [SMulCommClass G S S] (g : G) (x) :
    Algebra.leftMulMatrix (g • b) x = Algebra.leftMulMatrix b x := by
  ext
  simp_rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, coe_lmul_eq_mul, LinearMap.mul_apply',
    Module.Basis.repr_smul, Module.Basis.smul_apply, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_symm_apply, mul_smul_comm, inv_smul_smul]

