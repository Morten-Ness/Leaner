import Mathlib

open scoped nonZeroDivisors

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀}

theorem associatesNonZeroDivisorsEquiv_mk_mk (a : M₀) (ha) :
    associatesNonZeroDivisorsEquiv ⟨⟦a⟧, ha⟩ = ⟦⟨a, mk_mem_nonZeroDivisors_associates.1 ha⟩⟧ := rfl

