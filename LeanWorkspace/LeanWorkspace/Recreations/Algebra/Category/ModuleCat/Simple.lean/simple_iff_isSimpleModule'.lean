import Mathlib

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem simple_iff_isSimpleModule' (M : ModuleCat R) : Simple M ↔ IsSimpleModule R M := simple_iff_isSimpleModule

