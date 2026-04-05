import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι → Subalgebra R A}

theorem iSupLift_mk {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    Subalgebra.iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  dsimp [Subalgebra.iSupLift, inclusion]
  rw [Set.iUnionLift_mk]

