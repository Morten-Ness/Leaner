import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem fst_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → tsze R M) :
    (∑ i ∈ s, f i).fst = ∑ i ∈ s, (f i).fst := Prod.fst_sum

