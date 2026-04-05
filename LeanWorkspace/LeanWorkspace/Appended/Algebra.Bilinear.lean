import Mathlib

section

variable {R A B : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem _root_.Algebra.lmul_injective : Function.Injective (Algebra.lmul R A) := fun a₁ a₂ h ↦ by simpa using DFunLike.congr_fun h 1

end

section

variable {R A B : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A]

theorem _root_.Algebra.lmul_isUnit_iff {x : A} :
    IsUnit (Algebra.lmul R A x) ↔ IsUnit x := by
  rw [Module.End.isUnit_iff, Iff.comm]
  exact IsUnit.isUnit_iff_mulLeft_bijective

end

section

variable {R A B : Type*}

variable [CommSemiring R] [NonUnitalSemiring A] [NonUnitalSemiring B] [Module R B] [Module R A]

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable [SMulCommClass R B B] [IsScalarTower R B B]

theorem commute_mulLeft_right (a b : A) : Commute (mulLeft R a) (mulRight R b) := by
  ext c
  exact (mul_assoc a c b).symm

end

section

variable {R A B : Type*}

variable (R A) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable {M : Type*} [AddCommMonoid M] [Module R M]

theorem lift_lsmul_mul_eq_lsmul_lift_lsmul {r : R} :
    lift (lsmul R M ∘ₗ LinearMap.mul R R r) = lsmul R M r ∘ₗ lift (lsmul R M) := by
  apply TensorProduct.ext'
  intro x a
  simp [← mul_smul, mul_comm]

end

section

variable {R A B : Type*}

variable [CommSemiring R] [NonUnitalCommSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

theorem mul'_comp_comm : LinearMap.mul' R A ∘ₗ TensorProduct.comm R A A = LinearMap.mul' R A := by
  simp [LinearMap.mul', lift_comp_comm_eq]

end

section

variable {R A B : Type*}

variable [Semiring R] [Semiring A]

variable [Module R A] [SMulCommClass R A A]

theorem pow_mulLeft (a : A) (n : ℕ) : mulLeft R a ^ n = mulLeft R (a ^ n) := match n with
  | 0 => by rw [pow_zero, pow_zero, mulLeft_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ, mulLeft_mul, Module.End.mul_eq_comp, pow_mulLeft]

end

section

variable {R A B : Type*}

variable [Semiring R] [Semiring A]

variable [Module R A] [IsScalarTower R A A]

theorem pow_mulRight (a : A) (n : ℕ) : mulRight R a ^ n = mulRight R (a ^ n) := match n with
  | 0 => by rw [pow_zero, pow_zero, mulRight_one, Module.End.one_eq_id]
  | (n + 1) => by rw [pow_succ, pow_succ', mulRight_mul, Module.End.mul_eq_comp, pow_mulRight]

end
