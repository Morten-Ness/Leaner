import Mathlib

variable {R M : Type*}

variable (A : Type*) [AddCommGroup A] (n : ℤ)

variable {A} {n : ℕ}

theorem torsionBy.nsmul_iff {x : A} :
    x ∈ A[n] ↔ n • x = 0 := Nat.cast_smul_eq_nsmul ℤ n x ▸ Submodule.mem_torsionBy_iff ..

