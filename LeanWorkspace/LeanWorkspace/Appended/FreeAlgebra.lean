import Mathlib

section

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


theorem _root_.Algebra.adjoin_eq_range_freeAlgebra_lift (s : Set A) :
    Algebra.adjoin R s = (FreeAlgebra.lift R ((↑) : s → A)).range := by
  rw [← Algebra.adjoin_range_eq_range_freeAlgebra_lift, Subtype.range_coe]

end

section

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

end

section

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

end

section

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


theorem algebraMap_eq_one_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1 := map_eq_one_iff (algebraMap _ _) FreeAlgebra.algebraMap_leftInverse.injective

-- this proof is copied from the approach in `FreeAbelianGroup.of_injective`

end

section

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


theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0 := map_eq_zero_iff (algebraMap _ _) FreeAlgebra.algebraMap_leftInverse.injective

end

section

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


theorem algebraMap_inj (x y : R) :
    algebraMap R (FreeAlgebra R X) x = algebraMap R (FreeAlgebra R X) y ↔ x = y := FreeAlgebra.algebraMap_leftInverse.injective.eq_iff

end

section

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


theorem algebraMap_leftInverse :
    Function.LeftInverse FreeAlgebra.algebraMapInv (algebraMap R <| FreeAlgebra R X) := fun x ↦ by
  simp [FreeAlgebra.algebraMapInv]

end

section

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


theorem hom_ext {f g : FreeAlgebra R X →ₐ[R] A}
    (w : (f : FreeAlgebra R X → A) ∘ ι R = (g : FreeAlgebra R X → A) ∘ ι R) : f = g := by
  rw [← FreeAlgebra.lift_symm_apply, ← FreeAlgebra.lift_symm_apply] at w
  exact (FreeAlgebra.lift R).symm.injective w

end

section

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

end

section

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


theorem lift_comp_ι (g : FreeAlgebra R X →ₐ[R] A) :
    FreeAlgebra.lift R ((g : FreeAlgebra R X → A) ∘ ι R) = g := by
  rw [← FreeAlgebra.lift_symm_apply]
  exact (FreeAlgebra.lift R).apply_symm_apply g

end

section

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


theorem lift_unique (f : X → A) (g : FreeAlgebra R X →ₐ[R] A) :
    (g : FreeAlgebra R X → A) ∘ ι R = f ↔ g = FreeAlgebra.lift R f := by
  rw [← (FreeAlgebra.lift R).symm_apply_eq, FreeAlgebra.lift]
  rfl

end

section

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


theorem lift_ι_apply (f : X → A) (x) : FreeAlgebra.lift R f (ι R x) = f x := by
  rw [ι_def, FreeAlgebra.lift]
  rfl

end

section

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


theorem ι_comp_lift (f : X → A) : (FreeAlgebra.lift R f : FreeAlgebra R X → A) ∘ ι R = f := by
  ext
  rw [Function.comp_apply, ι_def, FreeAlgebra.lift]
  rfl

end

section

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


theorem ι_injective [Nontrivial R] : Function.Injective (ι R : X → FreeAlgebra R X) := fun x y hoxy ↦
  by_contradiction <| by
    classical exact fun hxy : x ≠ y ↦
        let f : FreeAlgebra R X →ₐ[R] R := FreeAlgebra.lift R fun z ↦ if x = z then (1 : R) else 0
        have hfx1 : f (ι R x) = 1 := (FreeAlgebra.lift_ι_apply _ _).trans <| if_pos rfl
        have hfy1 : f (ι R y) = 1 := hoxy ▸ hfx1
        have hfy0 : f (ι R y) = 0 := (FreeAlgebra.lift_ι_apply _ _).trans <| if_neg hxy
        one_ne_zero <| hfy1.symm.trans hfy0

end

section

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


theorem ι_ne_algebraMap [Nontrivial R] (x : X) (r : R) : ι R x ≠ algebraMap R _ r := fun h ↦ by
  let f0 : FreeAlgebra R X →ₐ[R] R := FreeAlgebra.lift R 0
  let f1 : FreeAlgebra R X →ₐ[R] R := FreeAlgebra.lift R 1
  have hf0 : f0 (ι R x) = 0 := FreeAlgebra.lift_ι_apply _ _
  have hf1 : f1 (ι R x) = 1 := FreeAlgebra.lift_ι_apply _ _
  rw [h, f0.commutes, Algebra.algebraMap_self_apply] at hf0
  rw [h, f1.commutes, Algebra.algebraMap_self_apply] at hf1
  exact zero_ne_one (hf0.symm.trans hf1)

end
