import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable [Mul G] [SMulZeroClass G k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_single_mul_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
    (h : ¬∃ d, g' = g * d) : (SkewMonoidAlgebra.single g r * x).coeff g' = 0 := by
  classical
  rw [SkewMonoidAlgebra.coeff_mul, SkewMonoidAlgebra.sum_single_index]
  · apply Finset.sum_eq_zero
    simp_rw [ite_eq_right_iff]
    rintro g'' _hg'' rfl
    exact absurd ⟨_, rfl⟩ h
  · simp

