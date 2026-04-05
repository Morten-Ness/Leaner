import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem interior_map {n : ℕ} (s : Affine.Simplex k P n) {f : P →ᵃ[k] P₂} (hf : Function.Injective f) :
    (s.map f hf).interior = f '' s.interior := Affine.Simplex.setInterior_map s _ hf

