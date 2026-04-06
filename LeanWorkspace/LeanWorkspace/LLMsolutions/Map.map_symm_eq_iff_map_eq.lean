FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_symm_eq_iff_map_eq {H : Subgroup N} {e : G ≃* N} :
    H.map ↑e.symm = K ↔ K.map ↑e = H := by
  constructor
  · intro h
    rw [← h]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      change H (e (e.symm y))
      simpa
    · intro hx
      refine ⟨e x, ?_, by simp⟩
      simpa using hx
  · intro h
    rw [← h]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      change K (e.symm (e y))
      simpa
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      simpa using hx
