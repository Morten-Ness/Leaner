import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

theorem toQuotient_map_apply (x : relations.R →₀ A) :
    relations.toQuotient (relations.map x) = 0 := DFunLike.congr_fun Module.Relations.toQuotient_map relations x

