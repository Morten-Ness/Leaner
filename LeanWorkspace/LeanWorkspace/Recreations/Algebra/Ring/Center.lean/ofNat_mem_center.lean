import Mathlib

variable {M : Type*}

theorem ofNat_mem_center [NonAssocSemiring M] (n : ℕ) [n.AtLeastTwo] :
    ofNat(n) ∈ Set.center M := Set.natCast_mem_center M n

