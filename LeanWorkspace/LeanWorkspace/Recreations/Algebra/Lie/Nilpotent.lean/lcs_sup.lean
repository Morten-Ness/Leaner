import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

theorem lcs_sup {N₁ N₂ : LieSubmodule R L M} {k : ℕ} :
    (N₁ ⊔ N₂).lcs k = N₁.lcs k ⊔ N₂.lcs k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [LieSubmodule.lcs_succ, ih, LieSubmodule.lie_sup]

