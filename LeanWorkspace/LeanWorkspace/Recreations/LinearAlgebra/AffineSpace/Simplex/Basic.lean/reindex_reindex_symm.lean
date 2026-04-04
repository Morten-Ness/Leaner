import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem reindex_reindex_symm {m n : ℕ} (s : Affine.Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).reindex e.symm = s := by rw [← Affine.Simplex.reindex_trans, Equiv.self_trans_symm, Affine.Simplex.reindex_refl]

