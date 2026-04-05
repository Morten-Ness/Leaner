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


theorem induction {motive : FreeAlgebra R X → Prop}
    (grade0 : ∀ r, motive (algebraMap R (FreeAlgebra R X) r)) (grade1 : ∀ x, motive (ι R x))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (a : FreeAlgebra R X) : motive a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : Subalgebra R (FreeAlgebra R X) :=
    { carrier := motive
      mul_mem' := mul _ _
      add_mem' := add _ _
      algebraMap_mem' := grade0 }
  let of : X → s := Subtype.coind (ι R) grade1
  -- the mapping through the subalgebra is the identity
  have of_id : AlgHom.id R (FreeAlgebra R X) = s.val.comp (FreeAlgebra.lift R of) := by
    ext
    simp [of, Subtype.coind]
  -- finding a proof is finding an element of the subalgebra
  suffices a = FreeAlgebra.lift R of a by
    rw [this]
    exact Subtype.prop (FreeAlgebra.lift R of a)
  simp only [AlgHom.ext_iff, AlgHom.coe_id, id_eq, AlgHom.coe_comp, Subalgebra.coe_val,
    Function.comp_apply] at of_id
  exact of_id a

