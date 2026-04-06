FAIL
import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem finiteDimensional [Finite ι] (b : AffineBasis ι k P) : FiniteDimensional k V := by
  classical
  let p : P := b (Classical.arbitrary ι)
  let v : ι → V := fun i => b i -ᵥ p
  have hv : LinearIndependent k v := b.vectorSpan_linearIndependent p
  let B : Basis (Set.range v) k V := Basis.ofVectorSpaceIndex hv (by
    rw [b.vectorSpan_eq_top_of_nonempty]
    exact AffineSubspace.mem_direction_iff_eq_vsub_right.mp rfl)
  exact FiniteDimensional.of_fintype_basis B
