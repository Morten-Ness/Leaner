import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem _root_.Units.unitary_eq : unitary Rˣ = (unitary R).comap (Units.coeHom R) := by
  ext
  simp [Unitary.mem_iff, Units.ext_iff]

