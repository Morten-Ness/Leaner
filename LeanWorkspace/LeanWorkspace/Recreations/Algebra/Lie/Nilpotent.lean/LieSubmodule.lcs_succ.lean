import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

theorem lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N.lcs k⁆ := Function.iterate_succ_apply' (fun N' => ⁅⊤, N'⁆) k N

