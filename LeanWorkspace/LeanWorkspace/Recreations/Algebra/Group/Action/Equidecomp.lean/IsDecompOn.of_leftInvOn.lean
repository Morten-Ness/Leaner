import Mathlib

open scoped Classical

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem IsDecompOn.of_leftInvOn {f g : X → X} {A : Set X} {S : Finset G}
    (hf : Equidecomp.IsDecompOn f A S) (h : LeftInvOn g f A) : Equidecomp.IsDecompOn g (f '' A) S⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  rcases hf a ha with ⟨γ, γ_mem, hγ⟩
  use γ⁻¹, Finset.inv_mem_inv γ_mem
  rw [hγ, inv_smul_smul, ← hγ, h ha]

