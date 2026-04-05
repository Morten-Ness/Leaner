import Mathlib

variable {R : Type u} [CommRing R]

variable {n : Type v} [DecidableEq n] [Fintype n]

variable {N : Type w} [AddCommGroup N] [Module R N]

variable (M : Matrix n n R)

theorem isIntegral : IsIntegral R M := ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

