import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem zsmul_mem {x : R} (hx : x ∈ s) (n : ℤ) : n • x ∈ s := zsmul_mem hx n

