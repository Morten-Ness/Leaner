import Mathlib

open scoped MonoidAlgebra

variable (R X : Type*) [CommSemiring R]

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


theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι R : X → FreeAlgebra R X)) = ⊤ := by
  set S := Algebra.adjoin R (Set.range (ι R : X → FreeAlgebra R X))
  refine top_unique fun x hx => ?_; clear hx
  induction x with
  | grade0 => exact S.algebraMap_mem _
  | add x y hx hy => exact S.add_mem hx hy
  | mul x y hx hy => exact S.mul_mem hx hy
  | grade1 x => exact Algebra.subset_adjoin (Set.mem_range_self _)

