import Mathlib

section

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem algebraMapSubmonoid_powers {S : Type*} [Semiring S] [Algebra R S] (r : R) :
    Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r) := by
  simp [Algebra.algebraMapSubmonoid]

end

section

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem algebraMap_eq_one_iff {r : R} : algebraMap R A r = 1 ↔ r = 1 := map_eq_one_iff _ <| FaithfulSMul.algebraMap_injective R A

end

section

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem algebraMap_eq_zero_iff {r : R} : algebraMap R A r = 0 ↔ r = 0 := map_eq_zero_iff (algebraMap R A) <| FaithfulSMul.algebraMap_injective R A

end

section

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem algebraMap_injective : Function.Injective (algebraMap R A) := (faithfulSMul_iff_algebraMap_injective R A).mp inferInstance

end

section

open scoped Algebra

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

theorem map_algebraMap_mul (f : A →ₗ[R] B) (a : A) (r : R) :
    f (algebraMap R A r * a) = algebraMap R B r * f a := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul]

end

section

open scoped Algebra

variable {R : Type*} {A : Type*} {B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

theorem map_mul_algebraMap (f : A →ₗ[R] B) (a : A) (r : R) :
    f (a * algebraMap R A r) = f a * algebraMap R B r := by
  rw [← Algebra.commutes, ← Algebra.commutes, LinearMap.map_algebraMap_mul]

end

section

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem mem_algebraMapSubmonoid_of_mem {S : Type*} [Semiring S] [Algebra R S] {M : Submonoid R}
    (x : M) : algebraMap R S x ∈ Algebra.algebraMapSubmonoid S M := Set.mem_image_of_mem (algebraMap R S) x.2

end

section

variable {R A M : Type*}

variable [CommSemiring R]

theorem mul_sub_algebraMap_pow_commutes [Ring A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, Algebra.mul_sub_algebraMap_commutes, mul_assoc, ih, ← mul_assoc]

end
