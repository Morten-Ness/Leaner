import Mathlib

variable {R : Type*} [CommRing R] [Preorder R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

theorem isElliptic_conj_iff : (g.val * m * g.val⁻¹).IsElliptic ↔ m.IsElliptic := by
  simp [Matrix.IsElliptic]

