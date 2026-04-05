import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_smul [DistribSMul α R] (r : α) (A : Matrix n n R) :
    Matrix.trace (r • A) = r • Matrix.trace A := Finset.smul_sum.symm

