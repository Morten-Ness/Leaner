import Mathlib

variable (G : Type u) (H : Type v) [Mul G] [Mul H]

theorem of_injective_mulHom (f : H →ₙ* G) (hf : Function.Injective f)
    (_ : TwoUniqueProds G) : TwoUniqueProds H := of_mulHom f (fun _ _ _ _ _ ↦ .imp (hf ·) (hf ·))

