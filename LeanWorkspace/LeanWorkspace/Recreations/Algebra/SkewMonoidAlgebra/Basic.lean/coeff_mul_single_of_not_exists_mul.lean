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

theorem coeff_mul_single_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
    (h : ∀ x, ¬g' = x * g) : (x * SkewMonoidAlgebra.single g r).coeff g' = 0 := by
  classical
  simp only [SkewMonoidAlgebra.coeff_mul, smul_zero, mul_zero, ite_self, SkewMonoidAlgebra.sum_single_index]
  apply Finset.sum_eq_zero
  simp_rw [ite_eq_right_iff]
  rintro _ _ rfl
  exact False.elim (h _ rfl)

