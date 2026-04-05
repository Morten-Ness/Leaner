import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem Algebra.charZero_of_charZero [CharZero R] : CharZero A := have := algebraMap_comp_natCast R A
  ⟨this ▸ (FaithfulSMul.algebraMap_injective R A).comp CharZero.cast_injective⟩

