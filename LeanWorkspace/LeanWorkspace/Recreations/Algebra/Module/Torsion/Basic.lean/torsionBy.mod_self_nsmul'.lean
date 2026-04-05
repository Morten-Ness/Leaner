import Mathlib

variable {R M : Type*}

variable (A : Type*) [AddCommGroup A] (n : ℤ)

variable {A} {n : ℕ}

theorem torsionBy.mod_self_nsmul' (s : ℕ) {x : A} (h : x ∈ A[n]) :
    s • x = (s % n) • x := nsmul_eq_mod_nsmul s (AddSubgroup.torsionBy.nsmul_iff.mp h)

-- adding `@[implicit_reducible]` causes downstream breakage

