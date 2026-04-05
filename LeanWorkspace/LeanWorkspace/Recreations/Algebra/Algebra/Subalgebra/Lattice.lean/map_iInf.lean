import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A →ₐ[R] B) (hf : Function.Injective f)
    (s : ι → Subalgebra R A) : (iInf s).map f = ⨅ (i : ι), (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

