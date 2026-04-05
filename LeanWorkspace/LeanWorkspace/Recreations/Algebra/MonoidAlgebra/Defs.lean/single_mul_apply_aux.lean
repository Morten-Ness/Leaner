import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

theorem single_mul_apply_aux (H : ∀ m' ∈ x.support, m * m' = m₁ ↔ m' = m₂) :
    (single m r * x) m₁ = r * x m₂ := by
  classical
  calc
    (single m r * x) m₁
    _ = x.sum fun m' r' ↦ if m * m' = m₁ then r * r' else 0 := by simp [MonoidAlgebra.mul_apply]
    _ = x.sum fun m' r' ↦ if m' = m₂ then r * r' else 0 := by
      dsimp [Finsupp.sum]; congr! 2; simp [*]
    _ = r * x m₂ := by simp +contextual [Finsupp.sum_eq_single m₂]

