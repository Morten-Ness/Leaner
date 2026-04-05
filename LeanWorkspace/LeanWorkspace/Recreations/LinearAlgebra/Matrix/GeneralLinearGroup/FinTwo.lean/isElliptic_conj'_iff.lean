import Mathlib

variable {R : Type*} [CommRing R] [Preorder R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

theorem isElliptic_conj'_iff : (g.val⁻¹ * m * g.val).IsElliptic ↔ m.IsElliptic := by
  simpa using Matrix.isElliptic_conj_iff g⁻¹

