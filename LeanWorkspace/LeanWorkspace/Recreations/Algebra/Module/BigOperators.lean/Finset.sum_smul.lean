import Mathlib

variable {ι κ α β R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} :
    (∑ i ∈ s, f i) • x = ∑ i ∈ s, f i • x := map_sum ((smulAddHom R M).flip x) f s

