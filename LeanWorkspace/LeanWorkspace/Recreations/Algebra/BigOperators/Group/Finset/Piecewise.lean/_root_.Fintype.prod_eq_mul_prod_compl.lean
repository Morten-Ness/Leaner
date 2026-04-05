import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem _root_.Fintype.prod_eq_mul_prod_compl [DecidableEq ι] [Fintype ι] (a : ι) (f : ι → M) :
    ∏ i, f i = f a * ∏ i ∈ {a}ᶜ, f i := Finset.prod_eq_mul_prod_diff_singleton_of_mem (mem_univ a) f

