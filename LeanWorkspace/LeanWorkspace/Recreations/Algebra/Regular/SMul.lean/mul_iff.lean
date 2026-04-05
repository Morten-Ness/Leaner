import Mathlib

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

variable [CommSemigroup R] [SMul R M] [IsScalarTower R R M]

theorem mul_iff : IsSMulRegular M (a * b) ↔ IsSMulRegular M a ∧ IsSMulRegular M b := by
  rw [← IsSMulRegular.mul_and_mul_iff]
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

