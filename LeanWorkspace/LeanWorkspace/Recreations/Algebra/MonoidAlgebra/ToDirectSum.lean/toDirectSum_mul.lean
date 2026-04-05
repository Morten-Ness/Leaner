import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f * g).toDirectSum = f.toDirectSum * g.toDirectSum := by
  let to_hom : AddMonoidAlgebra M ι →+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := AddMonoidAlgebra.toDirectSum_zero
    map_add' := AddMonoidAlgebra.toDirectSum_add }
  change to_hom (f * g) = to_hom f * to_hom g
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  ext xi xv yi yv : 4
  simp [to_hom, AddMonoidAlgebra.single_mul_single, DirectSum.of_mul_of]

