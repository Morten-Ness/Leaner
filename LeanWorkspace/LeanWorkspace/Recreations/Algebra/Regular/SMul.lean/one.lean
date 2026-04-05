import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [Monoid R] [MulAction R M]

theorem one : IsSMulRegular M (1 : R) := fun a b ab => by
  dsimp only [Function.comp_def] at ab
  rw [one_smul, one_smul] at ab
  assumption

