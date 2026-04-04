import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable (k V)

variable {V}

variable {k}

theorem affineIndependent_of_ne_of_mem_of_mem_of_notMem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₂ : p₁ ≠ p₂) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∉ s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  have ha : AffineIndependent k fun x : { x : Fin 3 // x ≠ 2 } => ![p₁, p₂, p₃] x := by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (2 : Fin 3))]
    convert affineIndependent_of_ne k hp₁p₂
    ext x
    fin_cases x <;> rfl
  refine ha.affineIndependent_of_notMem_span ?_
  intro h
  refine hp₃ ((AffineSubspace.le_def' _ s).1 ?_ p₃ h)
  simp_rw [affineSpan_le, Set.image_subset_iff, Set.subset_def, Set.mem_preimage]
  intro x
  fin_cases x <;> simp +decide [hp₁, hp₂]

