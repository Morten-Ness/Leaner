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

theorem iSupLift_comp_inclusion {i : ι} (h : K i ≤ T) :
    (NonUnitalSubalgebra.iSupLift K dir f hf T hT).comp (NonUnitalSubalgebra.inclusion h) = f i := by
  ext
  simp only [NonUnitalAlgHom.comp_apply, NonUnitalSubalgebra.iSupLift_inclusion]

