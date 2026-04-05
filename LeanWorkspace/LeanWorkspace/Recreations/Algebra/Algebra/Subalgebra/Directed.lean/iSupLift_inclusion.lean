import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι → Subalgebra R A}

theorem iSupLift_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : K i) (h : K i ≤ T) :
    Subalgebra.iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  dsimp [Subalgebra.iSupLift, inclusion]
  rw [Set.iUnionLift_inclusion]
  exact SetLike.coe_subset_coe.mpr <| h.trans hT

