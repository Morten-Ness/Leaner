import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R]) := QuaternionAlgebra.eq_re_iff_mem_range_coe

