import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P]

variable (k V) {p₁ p₂ : P}

theorem preimage_coe_affineSpan_singleton (x : P) :
    ((↑) : affineSpan k ({x} : Set P) → P) ⁻¹' {x} = Set.univ := eq_univ_of_forall fun y => (AffineSubspace.mem_affineSpan_singleton _ _).1 y.2

