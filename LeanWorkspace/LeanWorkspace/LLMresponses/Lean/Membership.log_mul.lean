FAIL
import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem log_mul [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (x y : Submonoid.powers (n : M)) : Submonoid.log (x * y) = Submonoid.log x + Submonoid.log y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases hx with ⟨m, rfl⟩
  rcases hy with ⟨k, rfl⟩
  apply h
  simp [pow_add]
