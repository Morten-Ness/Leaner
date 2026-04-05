import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem mem_iInf {ι : Sort*} {S : ι → StarSubalgebra R A} {x : A} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, StarSubalgebra.mem_sInf, Set.forall_mem_range]

