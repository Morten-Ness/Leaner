import Mathlib

open scoped Pointwise

variable {α β : Type*}

theorem dens_inv [Fintype α] (s : Finset α) : s⁻¹.dens = s.dens := by simp [dens]

