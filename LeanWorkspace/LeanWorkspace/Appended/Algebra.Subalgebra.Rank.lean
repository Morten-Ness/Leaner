import Mathlib

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R A] [Module.Free A (Algebra.adjoin A (B : Set S))]

theorem rank_sup_eq_rank_left_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank A (Algebra.adjoin A (B : Set S)) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · haveI := Module.subsingleton R S; simp
  nontriviality S using rank_subsingleton'
  letI : Algebra A (Algebra.adjoin A (B : Set S)) := Subalgebra.algebra _
  letI : SMul A (Algebra.adjoin A (B : Set S)) := Algebra.toSMul
  haveI : IsScalarTower R A (Algebra.adjoin A (B : Set S)) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [rank_mul_rank R A (Algebra.adjoin A (B : Set S))]
  change _ = Module.rank R ((Algebra.adjoin A (B : Set S)).restrictScalars R)
  rw [Algebra.restrictScalars_adjoin]; rfl

end

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))]

theorem rank_sup_eq_rank_right_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R B * Module.rank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, Subalgebra.rank_sup_eq_rank_left_mul_rank_of_free]

end
