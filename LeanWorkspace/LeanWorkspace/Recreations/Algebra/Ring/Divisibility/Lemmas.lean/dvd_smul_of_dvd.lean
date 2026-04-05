import Mathlib

variable {R : Type*}

theorem dvd_smul_of_dvd {M : Type*} [SMul M R] [Semigroup R] [SMulCommClass M R R] {x y : R}
    (m : M) (h : x ∣ y) : x ∣ m • y := let ⟨k, hk⟩ := h; ⟨m • k, by rw [mul_smul_comm, ← hk]⟩

