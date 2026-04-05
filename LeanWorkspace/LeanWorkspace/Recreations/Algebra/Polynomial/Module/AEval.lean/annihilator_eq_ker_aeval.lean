import Mathlib

open scoped Polynomial

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

theorem annihilator_eq_ker_aeval [FaithfulSMul A M] :
    annihilator R[X] (Module.AEval R M a) = RingHom.ker (Polynomial.aeval a) := by
  ext p
  simp_rw [mem_annihilator, RingHom.mem_ker]
  change (∀ m : M, Polynomial.aeval a p • m = 0) ↔ _
  exact ⟨fun h ↦ eq_of_smul_eq_smul (α := M) <| by simp [h], fun h ↦ by simp [h]⟩

