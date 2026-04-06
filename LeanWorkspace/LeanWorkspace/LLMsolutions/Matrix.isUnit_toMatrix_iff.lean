import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

variable {ι' : Type*}

variable [Fintype ι] (b₂ : AffineBasis ι k P)

variable [DecidableEq ι]

theorem isUnit_toMatrix_iff [Nontrivial k] (p : ι → P) :
    IsUnit (b.toMatrix p) ↔ AffineIndependent k p ∧ affineSpan k (Set.range p) = ⊤ := by
  simpa using b.isUnit_toMatrix_iff p
