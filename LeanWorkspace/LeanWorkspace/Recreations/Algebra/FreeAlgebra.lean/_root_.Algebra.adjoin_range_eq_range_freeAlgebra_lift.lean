import Mathlib

open scoped MonoidAlgebra

variable (R X : Type*) [CommSemiring R]

variable {A : Type*} [Semiring A] [Algebra R A]

private theorem mk_mul (x y : Pre R X) :
    Quot.mk (Rel R X) (x * y) = (HMul.hMul (self := instHMul (α := FreeAlgebra R X))
    (Quot.mk (Rel R X) x) (Quot.mk (Rel R X) y)) :=
  rfl


set_option backward.privateInPublic true in
private def liftAux (f : X → A) : FreeAlgebra R X →ₐ[R] A where
  toFun a := Quot.liftOn a (FreeAlgebra.liftFun _ _ f) fun a b h ↦ by
      induction h
      · exact (algebraMap R A).map_add _ _
      · exact (algebraMap R A).map_mul _ _
      · apply Algebra.commutes
      · change _ + _ + _ = _ + (_ + _)
        rw [add_assoc]
      · change _ + _ = _ + _
        rw [add_comm]
      · change algebraMap _ _ _ + FreeAlgebra.liftFun R X f _ = FreeAlgebra.liftFun R X f _
        simp
      · change _ * _ * _ = _ * (_ * _)
        rw [mul_assoc]
      · change algebraMap _ _ _ * FreeAlgebra.liftFun R X f _ = FreeAlgebra.liftFun R X f _
        simp
      · change FreeAlgebra.liftFun R X f _ * algebraMap _ _ _ = FreeAlgebra.liftFun R X f _
        simp
      · change _ * (_ + _) = _ * _ + _ * _
        rw [left_distrib]
      · change (_ + _) * _ = _ * _ + _ * _
        rw [right_distrib]
      · change algebraMap _ _ _ * _ = algebraMap _ _ _
        simp
      · change _ * algebraMap _ _ _ = algebraMap _ _ _
        simp
      repeat
        change FreeAlgebra.liftFun R X f _ + FreeAlgebra.liftFun R X f _ = _
        simp only [*]
        rfl
      repeat
        change FreeAlgebra.liftFun R X f _ * FreeAlgebra.liftFun R X f _ = _
        simp only [*]
        rfl
  map_one' := by
    change algebraMap _ _ _ = _
    simp
  map_mul' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  map_zero' := by
    change algebraMap _ _ _ = _
    simp
  map_add' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  commutes' := by tauto


theorem _root_.Algebra.adjoin_range_eq_range_freeAlgebra_lift (f : X → A) :
    Algebra.adjoin R (Set.range f) = (FreeAlgebra.lift R f).range := by
  simp only [← Algebra.map_top, ← FreeAlgebra.adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, FreeAlgebra.lift_ι_apply]

