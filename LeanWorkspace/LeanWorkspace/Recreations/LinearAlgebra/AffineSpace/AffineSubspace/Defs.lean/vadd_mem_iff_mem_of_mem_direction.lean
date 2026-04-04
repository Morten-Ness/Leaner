import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_iff_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction)
    {p : P} : v +ᵥ p ∈ s ↔ p ∈ s := by
  refine ⟨fun h => ?_, fun h => AffineSubspace.vadd_mem_of_mem_direction hv h⟩
  convert AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) h
  simp

