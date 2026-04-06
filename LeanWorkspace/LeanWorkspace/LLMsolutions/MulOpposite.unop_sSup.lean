FAIL
import Mathlib

open MulOpposite

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sSup (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := by
  ext x
  constructor
  · intro hx
    rw [Subalgebra.mem_unop] at hx
    rw [Subalgebra.mem_sSup] at hx ⊢
    rcases hx with ⟨P, hP, hxP⟩
    exact ⟨P.unop, hP, hxP⟩
  · intro hx
    rw [Subalgebra.mem_unop]
    rw [Subalgebra.mem_sSup] at hx ⊢
    rcases hx with ⟨P, hP, hxP⟩
    exact ⟨P.op, hP, hxP⟩
