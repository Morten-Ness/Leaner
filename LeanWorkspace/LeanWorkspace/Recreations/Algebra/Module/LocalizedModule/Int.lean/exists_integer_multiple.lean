import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

variable [IsLocalizedModule S f]

theorem exists_integer_multiple (x : M') : ∃ a : S, IsLocalizedModule.IsInteger f (a.val • x) := let ⟨⟨Num, denom⟩, h⟩ := IsLocalizedModule.surj S f x
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩

