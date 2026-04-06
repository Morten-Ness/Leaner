FAIL
import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sInf (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := by
  ext x
  constructor
  · intro hx
    change MulOpposite.op x ∈ sInf S at hx
    rw [show sInf S = sInfₛ S by rfl] at hx
    change x ∈ sInf (.op ⁻¹' S)
    rw [show sInf (.op ⁻¹' S) = sInfₛ (.op ⁻¹' S) by rfl]
    exact fun p hp => hx hp
  · intro hx
    change x ∈ sInf (.op ⁻¹' S) at hx
    rw [show sInf (.op ⁻¹' S) = sInfₛ (.op ⁻¹' S) by rfl] at hx
    change MulOpposite.op x ∈ sInf S
    rw [show sInf S = sInfₛ S by rfl]
    exact fun p hp => hx p hp
