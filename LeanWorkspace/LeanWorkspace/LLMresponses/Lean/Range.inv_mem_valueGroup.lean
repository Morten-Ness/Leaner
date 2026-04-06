FAIL
import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem inv_mem_valueGroup {b : Bˣ} (hb : b.1 ∈ Set.range f) : b⁻¹ ∈ MonoidWithZeroHom.valueGroup f := by
  rw [MonoidWithZeroHom.valueGroup]
  intro t ht
  rw [Set.mem_range] at hb
  rcases hb with ⟨a, ha⟩
  rw [Set.mem_range]
  refine ⟨a, ?_⟩
  simpa [ha] using (MonoidWithZeroHomClass.map_inv₀ (f := f) a)
