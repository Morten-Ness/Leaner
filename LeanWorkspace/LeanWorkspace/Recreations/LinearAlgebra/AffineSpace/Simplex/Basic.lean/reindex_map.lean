import Mathlib

variable (k : Type*) {V V₂ V₃ : Type*} (P P₂ P₃ : Type*)

variable [Ring k] [AddCommGroup V] [AddCommGroup V₂] [AddCommGroup V₃]

variable [Module k V] [Module k V₂] [Module k V₃]

variable [AddTorsor V P] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃]

variable {P P₂ P₃}

variable {k}

theorem reindex_map {m n : ℕ} (s : Affine.Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1))
    (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    (s.map f hf).reindex e = (s.reindex e).map f hf := rfl

