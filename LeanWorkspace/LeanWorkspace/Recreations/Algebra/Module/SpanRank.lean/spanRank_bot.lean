import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanRank_bot : (⊥ : Ideal R).spanRank = 0 := Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

