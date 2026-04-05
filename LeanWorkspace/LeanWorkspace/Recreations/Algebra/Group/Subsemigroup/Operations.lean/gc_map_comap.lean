import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem gc_map_comap (f : M →ₙ* N) : GaloisConnection (Subsemigroup.map f) (Subsemigroup.comap f) := fun _ _ =>
  Subsemigroup.map_le_iff_le_comap

