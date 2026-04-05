import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M]

theorem Finset.expect_eq_sum_div_card _root_.Fintype [Fintype ι] (f : ι → M) :
    𝔼 i, f i = (∑ i, f i) / Fintype.card ι := Finset.expect_eq_sum_div_card _ _

