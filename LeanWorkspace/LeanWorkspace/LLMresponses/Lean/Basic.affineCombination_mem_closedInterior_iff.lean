FAIL
import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem affineCombination_mem_closedInterior_iff {n : ℕ} {s : Affine.Simplex k P n} {w : Fin (n + 1) → k}
    (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.closedInterior ↔ ∀ i, w i ∈ Set.Icc 0 1 := by
  simpa [Affine.Simplex.closedInterior, Set.mem_setOf_eq, hw] using
    show (∃ w' : Fin (n + 1) → k,
        (∀ i, w' i ∈ Set.Icc 0 1) ∧
          ∑ i, w' i = 1 ∧
            Finset.univ.affineCombination k s.points w' =
              Finset.univ.affineCombination k s.points w) ↔
        ∀ i, w i ∈ Set.Icc 0 1 from
      by
        constructor
        · intro h i
          rcases h with ⟨w', hw'Icc, hw'sum, hEq⟩
          have hw' : w' = w := by
            exact s.eq_of_affineCombination_eq_of_sum_eq_one hw'sum hw hEq
          simpa [hw'] using hw'Icc i
        · intro hwIcc
          exact ⟨w, hwIcc, hw, rfl⟩
