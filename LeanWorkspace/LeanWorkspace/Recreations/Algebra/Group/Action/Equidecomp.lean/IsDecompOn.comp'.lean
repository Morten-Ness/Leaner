import Mathlib

open scoped Classical

variable {X G : Type*} {A B C : Set X}

variable [Monoid G] [MulAction G X]

theorem IsDecompOn.comp' {g f : X → X} {B A : Set X} {T S : Finset G}
    (hg : Equidecomp.IsDecompOn g B T) (hf : Equidecomp.IsDecompOn f A S) :
    Equidecomp.IsDecompOn (g ∘ f) (A ∩ f ⁻¹' B) (T * S) := by
  intro _ ⟨aA, aB⟩
  rcases hf _ aA with ⟨γ, γ_mem, hγ⟩
  rcases hg _ aB with ⟨δ, δ_mem, hδ⟩
  use δ * γ, Finset.mul_mem_mul δ_mem γ_mem
  rwa [mul_smul, ← hγ]

