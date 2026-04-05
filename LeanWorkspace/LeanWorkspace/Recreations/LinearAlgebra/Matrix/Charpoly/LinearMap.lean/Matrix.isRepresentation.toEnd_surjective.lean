import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

variable (hb : Submodule.span R (Set.range b) = ⊤)

theorem Matrix.isRepresentation.toEnd_surjective :
    Function.Surjective (Matrix.isRepresentation.toEnd R b hb) := by
  intro f
  obtain ⟨M, e, -⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R b hb f ⊤ (by simp)
  exact ⟨M, e⟩

