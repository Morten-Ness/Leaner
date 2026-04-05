import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

variable {ι : Sort*}

theorem coe_iSup_of_directed [Nonempty ι] {S : ι → NonUnitalSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) := let K : NonUnitalSubalgebra R A :=
    { __ := NonUnitalSubsemiring.copy _ _ (NonUnitalSubsemiring.coe_iSup_of_directed dir).symm
      smul_mem' := fun r _x hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, (S i).smul_mem' r hi⟩ }
  have : iSup S = K := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set A)) i) (Set.iUnion_subset fun _ ↦ le_iSup S _)
  this.symm ▸ rfl

