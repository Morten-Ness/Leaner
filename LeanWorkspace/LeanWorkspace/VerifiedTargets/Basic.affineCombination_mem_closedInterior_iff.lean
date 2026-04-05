import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem affineCombination_mem_closedInterior_iff {n : ℕ} {s : Affine.Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.closedInterior ↔ ∀ i, w i ∈ Set.Icc 0 1 := Affine.Simplex.affineCombination_mem_setInterior_iff hw

