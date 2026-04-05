import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι → Subalgebra R A}

theorem iSupLift_of_mem {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    Subalgebra.iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  dsimp [Subalgebra.iSupLift, inclusion]
  rw [Set.iUnionLift_of_mem]

