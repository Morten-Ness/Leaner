import Mathlib

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

theorem _root_.OrderHomClass.of_addMonoidHom {F' E₁' E₂' : Type*} [FunLike F' E₁' E₂'] [AddGroup E₁']
    [LE E₁'] [AddRightMono E₁'] [AddGroup E₂'] [LE E₂'] [AddRightMono E₂']
    [AddMonoidHomClass F' E₁' E₂']
    (h : ∀ f : F', ∀ x, 0 ≤ x → 0 ≤ f x) : OrderHomClass F' E₁' E₂' where
  map_rel f a b hab := by simpa using h f (b - a) (sub_nonneg.mpr hab)

