import Mathlib

variable {K : Type u} [Field K]

theorem refl (A : CSA K) : IsBrauerEquivalent A A := ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.refl⟩⟩

