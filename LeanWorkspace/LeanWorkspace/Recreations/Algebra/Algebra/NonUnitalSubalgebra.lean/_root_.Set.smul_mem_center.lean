import Mathlib

variable {R A : Type*}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem _root_.Set.smul_mem_center (r : R) {a : A} (ha : a ∈ Set.center A) :
    r • a ∈ Set.center A where
  comm b := by rw [commute_iff_eq, mul_smul_comm, smul_mul_assoc, ha.comm]
  left_assoc b c := by rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, ha.left_assoc]
  right_assoc b c := by
    rw [mul_smul_comm, mul_smul_comm, mul_smul_comm, ha.right_assoc]

