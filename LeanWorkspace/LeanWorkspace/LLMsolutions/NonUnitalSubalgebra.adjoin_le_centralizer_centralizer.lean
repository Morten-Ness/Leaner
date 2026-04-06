FAIL
import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A]

variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_le_centralizer_centralizer (s : Set A) :
    NonUnitalAlgebra.adjoin R s ≤ NonUnitalSubalgebra.centralizer R (NonUnitalSubalgebra.centralizer R s) := by
  refine NonUnitalAlgebra.adjoin_le ?_
  intro a ha
  change a ∈ NonUnitalSubalgebra.centralizer R (↑(NonUnitalSubalgebra.centralizer R s) : Set A)
  rw [NonUnitalSubalgebra.mem_centralizer_iff]
  intro b hb
  rw [NonUnitalSubalgebra.mem_centralizer_iff] at hb
  exact hb a ha
