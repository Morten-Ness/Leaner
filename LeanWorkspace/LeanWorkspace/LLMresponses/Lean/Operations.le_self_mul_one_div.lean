FAIL
import Mathlib

universe uι u v

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem le_self_mul_one_div {I : Submodule R A} (hI : I ≤ 1) : I ≤ I * (1 / I) := by
  simpa [Submodule.one_eq_span, Submodule.mul_span_singleton] using
    Submodule.mul_le.2 le_rfl (show I * (1 / I) ≤ 1 by
      exact Submodule.mul_le.2 le_rfl (by simpa [Submodule.one_div_eq_annihilator] using hI))
