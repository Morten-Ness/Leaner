import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

theorem isTorsionBySet_annihilator : IsTorsionBySet R M (annihilator R M) := fun _ r ↦ Module.mem_annihilator.mp r.2 _

