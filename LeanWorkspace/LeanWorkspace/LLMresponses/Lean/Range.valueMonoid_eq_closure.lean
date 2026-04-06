FAIL
import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem valueMonoid_eq_closure : MonoidWithZeroHom.valueMonoid f = Submonoid.closure ((↑) ⁻¹' (Set.range f)) := by
  ext u
  constructor
  · rintro ⟨a, rfl⟩
    exact Submonoid.subset_closure ⟨a, rfl⟩
  · intro hu
    rw [Submonoid.mem_closure] at hu
    have hs : ((↑) ⁻¹' Set.range f) ⊆ ↑(MonoidWithZeroHom.valueMonoid f) := by
      rintro u ⟨a, rfl⟩
      exact ⟨a, rfl⟩
    exact hu (MonoidWithZeroHom.valueMonoid f) hs
