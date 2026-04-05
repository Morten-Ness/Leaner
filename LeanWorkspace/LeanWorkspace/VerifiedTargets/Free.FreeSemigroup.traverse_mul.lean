import Mathlib

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

