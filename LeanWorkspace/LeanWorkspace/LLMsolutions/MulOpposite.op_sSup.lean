FAIL
import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_sSup (S : Set (Subalgebra R A)) : (sSup S).op = sSup (.unop ⁻¹' S) := by
  ext x
  constructor
  · intro hx
    rw [Subalgebra.mem_sSup_of_directedOn] at hx
    · rw [Subalgebra.mem_sSup_of_directedOn]
      · rcases hx with ⟨P, hP, hxP⟩
        exact ⟨P.op, hP, hxP⟩
      · intro a ha b hb
        refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
        exact Set.mem_preimage.2 (show a.unop ⊔ b.unop ∈ S from sup_mem ha hb)
    · intro a ha b hb
      exact ⟨a ⊔ b, Set.mem_union ha hb, le_sup_left, le_sup_right⟩
  · intro hx
    rw [Subalgebra.mem_sSup_of_directedOn] at hx
    · rw [Subalgebra.mem_op]
      rw [Subalgebra.mem_sSup_of_directedOn]
      · rcases hx with ⟨P, hP, hxP⟩
        exact ⟨P.unop, hP, hxP⟩
      · intro a ha b hb
        refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
        exact Set.mem_preimage.2 (show a.unop ⊔ b.unop ∈ S from sup_mem ha hb)
    · intro a ha b hb
      refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
      exact Set.mem_preimage.2 (show a.unop ⊔ b.unop ∈ S from sup_mem ha hb)
