import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem sum_mul (s : Finset ι) (f : ι → R) (a : R) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := map_sum (AddMonoidHom.mulRight a) _ s

