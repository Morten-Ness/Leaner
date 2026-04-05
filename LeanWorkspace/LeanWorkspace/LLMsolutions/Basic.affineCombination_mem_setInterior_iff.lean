FAIL
import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem affineCombination_mem_setInterior_iff {I : Set k} {n : ℕ} {s : Affine.Simplex k P n}
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.setInterior I ↔ ∀ i, w i ∈ I := by
  constructor
  · intro hwmem i
    rw [Affine.Simplex.setInterior] at hwmem
    rcases hwmem with ⟨w', hw'sum, hw'I, hcomb⟩
    have hEq : w' = w := by
      exact s.eq_of_affineCombination_eq hw'sum hw hcomb
    simpa [hEq] using hw'I i
  · intro hwI
    rw [Affine.Simplex.setInterior]
    refine ⟨w, hw, hwI, rfl⟩
