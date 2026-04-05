import Mathlib

variable {α β : Type*}

theorem mem_nsmul {a : α} {s : Multiset α} {n : ℕ} : a ∈ n • s ↔ n ≠ 0 ∧ a ∈ s := by
  refine ⟨fun ha ↦ ⟨?_, Multiset.mem_of_mem_nsmul ha⟩, fun h ↦ ?_⟩
  · rintro rfl
    simp [zero_nsmul] at ha
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h.1
  rw [succ_nsmul, mem_add]
  exact Or.inr h.2

