import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable (S : NonUnitalStarSubalgebra R A)

variable {ι : Type*}

variable [StarRing R] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

variable [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

theorem coe_iSup_of_directed [Nonempty ι] {S : ι → NonUnitalStarSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) := let K : NonUnitalStarSubalgebra R A :=
    { __ := NonUnitalSubalgebra.copy _ _ (NonUnitalSubalgebra.coe_iSup_of_directed dir).symm
      star_mem' := fun hx ↦
        let ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        Set.mem_iUnion.2 ⟨i, star_mem (s := S i) hi⟩ }
  have : iSup S = K := le_antisymm (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set A)) i)
    (Set.iUnion_subset fun _ ↦ le_iSup S _)
  this.symm ▸ rfl

