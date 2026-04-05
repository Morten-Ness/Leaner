import Mathlib

variable {ι κ α β R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.sum • x = (l.map fun r ↦ r • x).sum := ((smulAddHom R M).flip x).map_multiset_sum l

