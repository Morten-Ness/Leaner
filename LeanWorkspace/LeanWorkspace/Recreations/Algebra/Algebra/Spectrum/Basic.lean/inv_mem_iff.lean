import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem inv_mem_iff {r : Rˣ} {a : Aˣ} : (r : R) ∈ σ (a : A) ↔ (↑r⁻¹ : R) ∈ σ (↑a⁻¹ : A) := not_iff_not.2 <| ⟨spectrum.inv_mem_resolventSet, spectrum.inv_mem_resolventSet⟩

