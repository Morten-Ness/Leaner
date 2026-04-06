FAIL
import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_sInf (S : Set (Subalgebra R A)) : (sInf S).op = sInf (.unop ⁻¹' S) := by
  ext x
  constructor
  · intro hx
    rw [Subalgebra.mem_sInf] at hx ⊢
    intro p hp
    have hp' : p.unop ∈ S := hp
    have hx' := hx p.unop hp'
    simpa using hx'
  · intro hx
    rw [Subalgebra.mem_sInf] at hx ⊢
    intro p hp
    have hp' : p.op ∈ (.unop ⁻¹' S) := hp
    have hx' := hx p.op hp'
    simpa using hx'
