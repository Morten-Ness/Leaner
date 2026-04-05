import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem PiToModule.fromEnd_injective (hb : Submodule.span R (Set.range b) = ⊤) :
    Function.Injective (PiToModule.fromEnd R b) := by
  intro x y e
  ext m
  obtain ⟨m, rfl⟩ : m ∈ LinearMap.range (Fintype.linearCombination R b) := by
    rw [(Fintype.range_linearCombination R b).trans hb]
    exact Submodule.mem_top
  exact (LinearMap.congr_fun e m :)

