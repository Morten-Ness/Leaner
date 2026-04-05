import Mathlib

variable {R : Type u} [Ring R]

variable {J : Type v} [Category.{t} J] (F : J ⥤ ModuleCat.{w} R)

variable [Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))]

theorem hasLimitsOfShape [Small.{w} J] : HasLimitsOfShape J (ModuleCat.{w} R) where
