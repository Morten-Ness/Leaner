import Mathlib

open scoped Polynomial

variable {R K M A : Type*} {a : A}

theorem isTorsion_of_aeval_eq_zero [CommSemiring R] [NoZeroDivisors R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
    {p : R[X]} (h : Polynomial.aeval a p = 0) (h' : p ≠ 0) :
    IsTorsion R[X] (Module.AEval R M a) := by
  have hp : p ∈ nonZeroDivisors R[X] := mem_nonZeroDivisors_iff_right.mpr
    fun q hq ↦ Or.resolve_right (mul_eq_zero.mp hq) h'
  exact fun x ↦ ⟨⟨p, hp⟩, (of R M a).symm.injective <| by simp [h]⟩

