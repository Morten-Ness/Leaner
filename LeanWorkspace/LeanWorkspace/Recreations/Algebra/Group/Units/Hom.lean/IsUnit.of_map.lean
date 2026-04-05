import Mathlib

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

theorem IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit (f a)) : IsUnit a := IsLocalHom.map_nonunit a h

-- TODO : remove alias, change the parenthesis of `f` and `a`
alias isUnit_of_map_unit := IsUnit.of_map

