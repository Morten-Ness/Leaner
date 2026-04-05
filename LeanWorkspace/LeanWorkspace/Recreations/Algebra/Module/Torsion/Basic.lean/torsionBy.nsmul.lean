import Mathlib

variable {R M : Type*}

variable (A : Type*) [AddCommGroup A] (n : ℤ)

variable {A} {n : ℕ}

theorem torsionBy.nsmul (x : A[n]) : n • x = 0 := Nat.cast_smul_eq_nsmul ℤ n x ▸ Submodule.smul_torsionBy ..

