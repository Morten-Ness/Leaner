import Mathlib

variable {ι κ α β R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem List.sum_smul {l : List R} {x : M} : l.sum • x = (l.map fun r ↦ r • x).sum := map_list_sum ((smulAddHom R M).flip x) l

