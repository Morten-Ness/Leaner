FAIL
import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R A] [Module.Free A (Algebra.adjoin A (B : Set S))]

theorem rank_sup_eq_rank_left_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank A (Algebra.adjoin A (B : Set S)) := by
  rw [show A ⊔ B = (Algebra.adjoin A (B : Set S)).restrictScalars R by
    ext x
    change x ∈ A ⊔ B ↔ x ∈ Algebra.adjoin A (B : Set S)
    constructor
    · intro hx
      refine Subalgebra.sup_le ?_ hx
      · exact fun y hy => Algebra.subset_adjoin hy
      · exact fun y hy => Algebra.subset_adjoin hy
    · intro hx
      refine Algebra.adjoin_le_iff.2 ?_ hx
      intro y hy
      exact show y ∈ A ⊔ B from Or.inr hy]
  simpa using
    (Submodule.rank_mul_rank (R := R) (S := A) (V := Algebra.adjoin A (B : Set S)))
