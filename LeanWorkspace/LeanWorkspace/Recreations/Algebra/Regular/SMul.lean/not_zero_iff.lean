import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [MonoidWithZero R] [Zero M] [MulActionWithZero R M]

theorem not_zero_iff : ¬IsSMulRegular M (0 : R) ↔ Nontrivial M := by
  rw [nontrivial_iff, not_iff_comm, IsSMulRegular.zero_iff_subsingleton, subsingleton_iff]
  push Not
  exact Iff.rfl

