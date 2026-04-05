import Mathlib

variable {R : Type u} [Ring R]

variable {J : Type v} [Category.{t} J] (F : J ⥤ ModuleCat.{w} R)

variable [Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))]

theorem hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (ModuleCat.{w} R) where
  has_limits_of_shape _ := ModuleCat.hasLimitsOfShape

