import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [MonoidWithZero R] [Zero M] [MulActionWithZero R M]

theorem zero [sM : Subsingleton M] : IsSMulRegular M (0 : R) := IsSMulRegular.zero_iff_subsingleton.mpr sM

