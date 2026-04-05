import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem nsmul_mem {x : R} (hx : x ∈ s) (n : ℕ) : n • x ∈ s := nsmul_mem hx n

