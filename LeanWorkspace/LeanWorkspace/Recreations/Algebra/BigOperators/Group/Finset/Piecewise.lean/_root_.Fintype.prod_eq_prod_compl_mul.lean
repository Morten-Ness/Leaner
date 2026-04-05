import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem _root_.Fintype.prod_eq_prod_compl_mul [DecidableEq ι] [Fintype ι] (a : ι) (f : ι → M) :
    ∏ i, f i = (∏ i ∈ {a}ᶜ, f i) * f a := Finset.prod_eq_prod_diff_singleton_mul (mem_univ a) f

