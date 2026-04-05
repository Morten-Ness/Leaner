import Mathlib

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (e : Embedding c c')

theorem f_eq_of_r_eq_some {i : ι} {i' : ι'} (hi : e.r i' = some i) :
    e.f i = i' := by
  by_cases h : ∃ (k : ι), e.f k = i'
  · obtain ⟨k, rfl⟩ := h
    rw [r_f] at hi
    congr 1
    simpa using hi.symm
  · simp [ComplexShape.Embedding.r_eq_none e i' (by simpa using h)] at hi

