import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

variable {ι : Sort*}

variable [Nonempty ι] {K : ι → NonUnitalSubalgebra R A} {dir : Directed (· ≤ ·) K}
  {f : ∀ i, K i →ₙₐ[R] B} {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : NonUnitalSubalgebra R A} {hT : T = iSup K}

set_option backward.isDefEq.respectTransparency false in
theorem iSupLift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    NonUnitalSubalgebra.iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  subst hT
  dsimp [NonUnitalSubalgebra.iSupLift]
  apply Set.iUnionLift_of_mem

