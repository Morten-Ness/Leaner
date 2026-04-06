FAIL
import Mathlib

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_surjective : Function.Surjective (MonoidWithZeroHom.snd G₀ H₀) := by
  intro f
  refine ⟨
    MonoidWithZeroHom.mk' (fun x => (1, f x)) ?_ ?_,
    rfl
  ⟩
  · intro x y
    simp [map_mul]
  · simp
