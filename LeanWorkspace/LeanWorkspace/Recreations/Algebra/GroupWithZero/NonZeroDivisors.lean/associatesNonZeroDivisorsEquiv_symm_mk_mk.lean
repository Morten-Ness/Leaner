import Mathlib

open scoped nonZeroDivisors

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀}

theorem associatesNonZeroDivisorsEquiv_symm_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv.symm ⟦⟨a, ha⟩⟧ = ⟨⟦a⟧, mk_mem_nonZeroDivisors_associates.2 ha⟩ := rfl

