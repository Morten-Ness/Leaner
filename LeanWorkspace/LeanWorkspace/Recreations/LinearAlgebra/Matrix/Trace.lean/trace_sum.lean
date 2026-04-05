import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [AddCommMonoid R]

theorem trace_sum (s : Finset ι) (f : ι → Matrix n n R) :
    Matrix.trace (∑ i ∈ s, f i) = ∑ i ∈ s, Matrix.trace (f i) := map_sum (Matrix.traceAddMonoidHom n R) f s

