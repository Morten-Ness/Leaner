import Mathlib

variable {R : Type*} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

theorem isParabolic_iff_of_upperTriangular [IsReduced R] (hm : m 1 0 = 0) :
    m.IsParabolic ↔ m 0 0 = m 1 1 ∧ m 0 1 ≠ 0 := by
  rw [Matrix.IsParabolic]
  have aux : m.discr = 0 ↔ m 0 0 = m 1 1 := by
    suffices m.discr = (m 0 0 - m 1 1) ^ 2 by
      rw [this, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
    grind [discr_fin_two, trace_fin_two, det_fin_two]
  have (h : m 0 0 = m 1 1) : m ∈ Set.range (scalar _) ↔ m 0 1 = 0 := by
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro h'
      use m 1 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, h', hm]
  tauto

