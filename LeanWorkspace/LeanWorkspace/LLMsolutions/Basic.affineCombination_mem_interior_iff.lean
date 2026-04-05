FAIL
import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem affineCombination_mem_interior_iff {n : ℕ} {s : Affine.Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.interior ↔ ∀ i, w i ∈ Set.Ioo 0 1 := by
  simp [Affine.Simplex.interior, hw]
