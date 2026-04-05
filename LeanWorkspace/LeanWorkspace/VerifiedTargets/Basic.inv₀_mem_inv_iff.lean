import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v} [Semifield R] [Ring A] [Algebra R A]

theorem inv₀_mem_inv_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (↑a⁻¹ : A) ↔ r ∈ spectrum R (a : A) := by
  simp

alias ⟨of_inv₀_mem, inv₀_mem⟩ := spectrum.inv₀_mem_iff
alias ⟨of_inv₀_mem_inv, inv₀_mem_inv⟩ := inv₀_mem_inv_iff

