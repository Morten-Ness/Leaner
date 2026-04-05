import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable (M) [Monoid R] [MulAction R M]

theorem IsUnit.isSMulRegular (ua : IsUnit a) : IsSMulRegular M a := by
  rcases ua with ⟨a, rfl⟩
  exact a.isSMulRegular M

