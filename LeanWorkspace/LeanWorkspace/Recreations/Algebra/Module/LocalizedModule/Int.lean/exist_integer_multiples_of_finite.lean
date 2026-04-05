import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

variable [IsLocalizedModule S f]

theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (g : ι → M') :
    ∃ b : S, ∀ i, IsLocalizedModule.IsInteger f ((b : R) • g i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples S f Finset.univ g
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩

