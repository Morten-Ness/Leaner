import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_apply (M : Matrix n n R) : M.det = ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, M (σ i) i := MultilinearMap.alternatization_apply _ M

-- This is what the old definition was. We use it to avoid having to change the old proofs below

