import Mathlib

section

variable {α : Type u}

variable {β : Type u}

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

variable [LawfulApplicative m]

theorem traverse_mul' :
    Function.comp (traverse F) ∘ (HMul.hMul : FreeSemigroup α → FreeSemigroup α → FreeSemigroup α) =
      fun x y ↦ (· * ·) <$> traverse F x <*> traverse F y := funext fun x ↦ funext fun y ↦ FreeSemigroup.traverse_mul F x y

end

section

variable {α : Type u}

variable {β : Type u}

variable {m : Type u → Type u} [Applicative m] (F : α → m β)

variable [LawfulApplicative m]

theorem traverse_mul (x y : FreeSemigroup α) :
    traverse F (x * y) = (· * ·) <$> traverse F x <*> traverse F y := let ⟨x, L1⟩ := x
  let ⟨y, L2⟩ := y
  List.recOn L1 (fun _ ↦ rfl)
    (fun hd tl ih x ↦ show
        (· * ·) <$> pure <$> F x <*> traverse F (FreeSemigroup.mk hd tl * FreeSemigroup.mk y L2) =
          (· * ·) <$> ((· * ·) <$> pure <$> F x <*> traverse F (FreeSemigroup.mk hd tl)) <*> traverse F (FreeSemigroup.mk y L2)
        by rw [ih]; simp only [Function.comp_def, (mul_assoc _ _ _).symm, functor_norm])
    x

end

section

variable {α : Type u} [Mul α]

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

theorem lift_comp_of' (f : Magma.AssocQuotient α →ₙ* β) : Magma.AssocQuotient.lift (f.comp Magma.AssocQuotient.of) = f := Magma.AssocQuotient.lift.apply_symm_apply f

end

section

variable {α : Type u} [Mul α]

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

theorem lift_comp_of : (Magma.AssocQuotient.lift f).comp Magma.AssocQuotient.of = f := Magma.AssocQuotient.lift.symm_apply_apply f

end

section

variable {α : Type u}

variable {β : Type v} (f : α → β)

theorem length_map (x) : (FreeSemigroup.map f x).length = x.length := FreeSemigroup.recOnMul x (fun _ ↦ rfl) (fun x y hx hy ↦ by simp only [map_mul, FreeSemigroup.length_mul, *])

end

section

variable {α : Type u}

theorem length_mul (x y : FreeSemigroup α) : (x * y).length = x.length + y.length := by
  simp [FreeSemigroup.length, Nat.add_right_comm, List.length, List.length_append]

end

section

variable {α : Type u} {β : Type v}

theorem length_toFreeSemigroup (x : FreeMagma α) : (FreeMagma.toFreeSemigroup x).length = x.length := FreeMagma.recOnMul x (fun _ ↦ rfl) fun x y hx hy ↦ by
    rw [map_mul, FreeSemigroup.length_mul, hx, hy]; rfl

end

section

variable {α : Type u}

variable {β : Type v} [Semigroup β] (f : α → β)

theorem lift_of_mul (x y) : FreeSemigroup.lift f (FreeSemigroup.of x * y) = f x * FreeSemigroup.lift f y := by rw [map_mul, FreeSemigroup.lift_of]

end

section

variable {α : Type u} {β : Type v}

theorem toFreeSemigroup_map (f : α → β) (x : FreeMagma α) :
    FreeMagma.toFreeSemigroup (FreeMagma.map f x) = FreeSemigroup.map f (FreeMagma.toFreeSemigroup x) := DFunLike.congr_fun (FreeMagma.toFreeSemigroup_comp_map f) x

end
