import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

theorem domDomRestrict_apply (f : MultilinearMap R M₁ M₂) (P : ι → Prop)
    [DecidablePred P] (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) :
    f.domDomRestrict P z x = f (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) := rfl

-- TODO: Should add a ref here when available.

