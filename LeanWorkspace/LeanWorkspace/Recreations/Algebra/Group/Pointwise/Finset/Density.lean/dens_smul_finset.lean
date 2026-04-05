import Mathlib

open scoped Pointwise

variable {α β : Type*}

theorem dens_smul_finset [Fintype β] (a : α) (s : Finset β) : (a • s).dens = s.dens := by simp [dens]

