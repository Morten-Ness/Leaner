import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem eq_re_iff_mem_range_coe {a : ℍ[R,c₁,c₂,c₃]} :
    a = a.re ↔ a ∈ Set.range (coe : R → ℍ[R,c₁,c₂,c₃]) := ⟨fun h => ⟨a.re, h.symm⟩, fun ⟨_, h⟩ => QuaternionAlgebra.eq_re_of_eq_coe h.symm⟩

