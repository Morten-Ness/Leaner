FAIL
import Mathlib

variable {M : Type*}

theorem mk_injective [Monoid M] [Subsingleton Mˣ] : Function.Injective (@Associates.mk M _) := by
  intro a b h
  rw [Associates.mk_eq_mk_iff_associated] at h
  rcases h with ⟨u, hu⟩
  have : u = 1 := Subsingleton.elim _ _
  rw [this, one_mul] at hu
  exact hu
