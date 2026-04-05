import Mathlib

variable {R : Type u} [CommRing R]

variable {J : Type v} [Category.{t} J] (F : J ⥤ AlgCat.{w} R)

variable [Small.{w} (F ⋙ forget (AlgCat.{w} R)).sections]

theorem hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgCat.{w} R) := { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := AlgCat.HasLimits.limitCone F
          isLimit := AlgCat.HasLimits.limitConeIsLimit F } } }

