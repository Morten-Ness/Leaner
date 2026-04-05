import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

theorem mul_single_apply_aux (H : ∀ m' ∈ x.support, m' * m = m₁ ↔ m' = m₂) :
    (x * single m r) m₁ = x m₂ * r := by
  classical
  calc
    (x * single m r) m₁
    _ = x.sum fun m' r' ↦ if m' * m = m₁ then r' * r else 0 := by simp [MonoidAlgebra.mul_apply]
    _ = x.sum fun m' r' ↦ if m' = m₂ then r' * r else 0 := by
      dsimp [Finsupp.sum]; congr! 2; simp [*]
    _ = x m₂ * r := by simp +contextual [Finsupp.sum_eq_single m₂]

