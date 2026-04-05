import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [MonoidWithZero R] [Zero M] [MulActionWithZero R M]

theorem not_zero [nM : Nontrivial M] : ¬IsSMulRegular M (0 : R) := IsSMulRegular.not_zero_iff.mpr nM

