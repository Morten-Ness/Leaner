FAIL
import Mathlib

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

theorem algHom_ext'' {F : Type*}
    [FunLike F (Unitization R A) C] [AlgHomClass F R (Unitization R A) C] {φ ψ : F}
    (h : ∀ a : A, φ a = ψ a) : φ = ψ := by
  apply DFunLike.ext
  intro x
  rcases x with ⟨r, a⟩
  calc
    φ (r, a) = φ ((r, (0 : A)) + (0, a)) := by rfl
    _ = φ (r, 0) + φ (0, a) := by rw [map_add]
    _ = ψ (r, 0) + ψ (0, a) := by
      congr
      · rw [show ((r, (0 : A)) : Unitization R A) = algebraMap R (Unitization R A) r by rfl]
        exact map_algebraMap φ r
      · exact h a
    _ = ψ (r, a) := by
      rw [← map_add]
      rfl
