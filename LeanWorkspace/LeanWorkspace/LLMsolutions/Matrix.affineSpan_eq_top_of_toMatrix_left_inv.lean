import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

variable {ι' : Type*}

theorem affineSpan_eq_top_of_toMatrix_left_inv [Finite ι] [Fintype ι'] [DecidableEq ι]
    [Nontrivial k] (p : ι' → P) {A : Matrix ι ι' k} (hA : A * b.toMatrix p = 1) :
    affineSpan k (Set.range p) = ⊤ := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact b.affineSpan_eq_top_of_toMatrix_left_inv p hA
