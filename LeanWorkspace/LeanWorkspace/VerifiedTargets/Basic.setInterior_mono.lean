import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem setInterior_mono {I J : Set k} (hij : I ⊆ J) {n : ℕ} (s : Affine.Simplex k P n) :
    s.setInterior I ⊆ s.setInterior J := fun _ ⟨w, hw, hw01, hww⟩ ↦ ⟨w, hw, fun i ↦ hij (hw01 i), hww⟩

