import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem map_iInf {ι : Sort*} [Nonempty ι]
    [IsScalarTower R B B] [SMulCommClass R B B] (f : F)
    (hf : Function.Injective f) (S : ι → NonUnitalSubalgebra R A) :
    ((⨅ i, S i).map f : NonUnitalSubalgebra R B) = ⨅ i, (S i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ S)

