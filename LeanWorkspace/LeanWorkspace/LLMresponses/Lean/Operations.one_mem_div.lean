FAIL
import Mathlib

universe u v

variable {ι : Sort u}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem one_mem_div {I J : Submodule R A} : 1 ∈ I / J ↔ J ≤ I := by
  change (∀ x ∈ J, x * 1 ∈ I) ↔ J ≤ I
  simp [Submodule.le_def]
