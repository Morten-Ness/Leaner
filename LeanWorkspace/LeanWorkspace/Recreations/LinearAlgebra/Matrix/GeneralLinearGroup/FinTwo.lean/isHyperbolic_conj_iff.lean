import Mathlib

variable {R : Type*} [CommRing R] [Preorder R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

theorem isHyperbolic_conj_iff : (g.val * m * g.val⁻¹).IsHyperbolic ↔ m.IsHyperbolic := by
  simp [Matrix.IsHyperbolic]

