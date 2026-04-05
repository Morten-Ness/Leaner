import Mathlib

variable {R : Type*} [CommRing R] [Preorder R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

theorem isHyperbolic_conj'_iff : (g.val⁻¹ * m * g.val).IsHyperbolic ↔ m.IsHyperbolic := by
  simpa using Matrix.isHyperbolic_conj_iff g⁻¹

