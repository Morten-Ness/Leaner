import Mathlib

section

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem isIdempotentElem_toSubmodule (S : Subalgebra R A) :
    IsIdempotentElem S.toSubmodule := by
  apply le_antisymm
  · refine (Subalgebra.mul_toSubmodule_le _ _).trans_eq ?_
    rw [sup_idem]
  · intro x hx1
    rw [← mul_one x]
    exact Submodule.mul_mem_mul hx1 (show (1 : A) ∈ S from one_mem S)

end

section

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem mul_toSubmodule {R : Type*} {A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S T : Subalgebra R A) : (Subalgebra.toSubmodule S) * (Subalgebra.toSubmodule T)
        = Subalgebra.toSubmodule (S ⊔ T) := by
  refine le_antisymm (Subalgebra.mul_toSubmodule_le _ _) ?_
  rintro x (hx : x ∈ Algebra.adjoin R (S ∪ T : Set A))
  refine
    Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun _ _ _ _ => Submodule.add_mem _)
      (fun x y _ _ hx hy => ?_) hx
  · rcases hx with hxS | hxT
    · rw [← mul_one x]
      exact Submodule.mul_mem_mul hxS (show (1 : A) ∈ T from one_mem T)
    · rw [← one_mul x]
      exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) hxT
  · rw [← one_mul (algebraMap _ _ _)]
    exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) (algebraMap_mem T _)
  have := Submodule.mul_mem_mul hx hy
  rwa [mul_assoc, mul_comm _ (Subalgebra.toSubmodule T), ← mul_assoc _ _ (Subalgebra.toSubmodule S),
    Subalgebra.isIdempotentElem_toSubmodule, mul_comm T.toSubmodule, ← mul_assoc,
    Subalgebra.isIdempotentElem_toSubmodule] at this

end
