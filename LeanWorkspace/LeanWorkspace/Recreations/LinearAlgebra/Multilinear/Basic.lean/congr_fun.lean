import Mathlib

variable {R : Type uR} {S : Type uS} {ι : Type uι} {n : ℕ}
  {M : Fin n.succ → Type v} {M₁ : ι → Type v₁} {M₁' : ι → Type v₁'} {M₁'' : ι → Type v₁''}

variable {M₂ : Type v₂} {M₃ : Type v₃} {M₄ : Type v₄} {M' : Type v'}

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [AddCommMonoid M₃] [AddCommMonoid M'] [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [Module R M₂]
  [Module R M₃] [Module R M'] (f f' : MultilinearMap R M₁ M₂)

theorem congr_fun {f g : MultilinearMap R M₁ M₂} (h : f = g) (x : ∀ i, M₁ i) : f x = g x := DFunLike.congr_fun h x

nonrec theorem congr_arg (f : MultilinearMap R M₁ M₂) {x y : ∀ i, M₁ i} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

