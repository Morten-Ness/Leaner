import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem floor_eq_self_of_mem (m : E) (h : m ∈ span ℤ (Set.range b)) : (ZSpan.floor b m : E) = m := by
  apply b.ext_elem
  simp_rw [ZSpan.repr_floor_apply b]
  intro i
  obtain ⟨z, hz⟩ := (b.mem_span_iff_repr_mem ℤ _).mp h i
  rw [← hz]
  exact congr_arg (Int.cast : ℤ → K) (Int.floor_intCast z)

