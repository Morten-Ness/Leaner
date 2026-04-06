FAIL
import Mathlib

open Cardinal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S)

variable [Module.Free R B] [Module.Free B (Algebra.adjoin B (A : Set S))]

theorem rank_sup_eq_rank_right_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R B * Module.rank B (Algebra.adjoin B (A : Set S)) := by
  let K : Subalgebra R S := B.copy (↑B) rfl
  have hK : K = B := by
    ext x
    rfl
  have hsup : A ⊔ B = (Algebra.adjoin K (A : Set S)).toSubalgebra := by
    ext x
    change x ∈ A ⊔ B ↔ x ∈ (Algebra.adjoin K (A : Set S)).toSubalgebra
    simp [Subalgebra.mem_sup]
  rw [hsup]
  let e : K ≃ₐ[R] B := {
    toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, by simpa [K, Subalgebra.copy] using x.2⟩
    left_inv := by intro x; ext <;> rfl
    right_inv := by intro x; ext <;> rfl
    map_mul' := by intro x y; rfl
    map_add' := by intro x y; rfl
    map_zero' := rfl
    map_one' := rfl
    commutes' := by intro r; rfl }
  let E : (Algebra.adjoin K (A : Set S)) ≃ₗ[R] (Algebra.adjoin B (A : Set S)) :=
    RestrictScalars.linearEquiv R
      ((Subalgebra.equivOfEq
        (by
          ext x
          change x ∈ Algebra.adjoin K (A : Set S) ↔ x ∈ Algebra.adjoin B (A : Set S)
          simp [K, Subalgebra.copy]))
        : Algebra.adjoin K (A : Set S) ≃ₐ[K] Algebra.adjoin B (A : Set S)).toLinearEquiv
  have hrank1 :
      Module.rank R ↥((Algebra.adjoin K (A : Set S)).toSubmodule) =
        Module.rank R (Algebra.adjoin B (A : Set S)) := by
    simpa using Cardinal.lift_id (Module.rank R (Algebra.adjoin B (A : Set S)))
  have hrank2 : Module.rank R K = Module.rank R B := by
    simpa [K] using Cardinal.lift_id (Module.rank R B)
  have hmul :
      Module.rank R (Algebra.adjoin B (A : Set S)) =
        Module.rank R B * Module.rank B (Algebra.adjoin B (A : Set S)) := by
    classical
    let b : Basis (Basis.ofVectorSpaceIndex R B) R B := Module.Free.chooseBasis R B
    let c : Basis (Basis.ofVectorSpaceIndex B (Algebra.adjoin B (A : Set S))) B
        (Algebra.adjoin B (A : Set S)) := Module.Free.chooseBasis B (Algebra.adjoin B (A : Set S))
    let bc := b.smul c
    simpa [Module.rank, bc.mk_eq_rank', b.mk_eq_rank', c.mk_eq_rank'] using bc.mk_eq_rank
  rw [hrank1, hmul]
