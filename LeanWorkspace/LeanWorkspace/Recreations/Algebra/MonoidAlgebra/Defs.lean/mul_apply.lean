import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

set_option backward.isDefEq.respectTransparency false in
theorem mul_apply [DecidableEq M] (x y : R[M]) (m : M) :
    (x * y) m = x.sum fun m₁ r₁ ↦ y.sum fun m₂ r₂ ↦ if m₁ * m₂ = m then r₁ * r₂ else 0 := by
  -- Porting note: `reducible` cannot be `local` so proof gets long.
  rw [MonoidAlgebra.mul_def, Finsupp.sum_apply]; congr; MonoidAlgebra.ext
  rw [Finsupp.sum_apply]; congr; MonoidAlgebra.ext
  apply MonoidAlgebra.single_apply

