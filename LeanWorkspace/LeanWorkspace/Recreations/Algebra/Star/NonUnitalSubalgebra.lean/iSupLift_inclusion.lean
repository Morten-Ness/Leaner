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

variable [Nonempty ι] {K : ι → NonUnitalStarSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →⋆ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalStarSubalgebra R A} {hT : T = iSup K}

set_option backward.isDefEq.respectTransparency false in
theorem iSupLift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
    NonUnitalStarSubalgebra.iSupLift K dir f hf T hT (NonUnitalStarSubalgebra.inclusion h x) = f i x := by
  subst T
  dsimp [NonUnitalStarSubalgebra.iSupLift]
  apply Set.iUnionLift_inclusion
  exact h

