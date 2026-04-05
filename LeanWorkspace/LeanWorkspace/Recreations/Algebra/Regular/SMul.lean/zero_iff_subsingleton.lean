import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [MonoidWithZero R] [Zero M] [MulActionWithZero R M]

theorem zero_iff_subsingleton : IsSMulRegular M (0 : R) ↔ Subsingleton M := ⟨fun h => IsSMulRegular.subsingleton h, fun H a b _ => @Subsingleton.elim _ H a b⟩

