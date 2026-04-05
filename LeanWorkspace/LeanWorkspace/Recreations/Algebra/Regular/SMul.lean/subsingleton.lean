import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [MonoidWithZero R] [Zero M] [MulActionWithZero R M]

theorem subsingleton (h : IsSMulRegular M (0 : R)) : Subsingleton M := ⟨fun a b => h (by dsimp only [Function.comp_def]; repeat' rw [MulActionWithZero.zero_smul])⟩

