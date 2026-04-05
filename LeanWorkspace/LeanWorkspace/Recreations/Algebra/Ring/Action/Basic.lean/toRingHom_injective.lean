import Mathlib

variable (M N : Type*) [Monoid M] [Monoid N]

variable (R : Type v) [Semiring R]

theorem toRingHom_injective [MulSemiringAction M R] [FaithfulSMul M R] :
    Function.Injective (MulSemiringAction.toRingHom M R) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => RingHom.ext_iff.1 h r

