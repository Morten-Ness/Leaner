import Mathlib

variable {ι α β M N G k R : Type*}

theorem abs_sum_le_sum_abs {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (f : ι → G) (s : Finset ι) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := le_sum_of_subadditive _ abs_zero.le abs_add_le s f

