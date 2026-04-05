import Mathlib

variable {R : Type*}

variable {p q : R}

variable [NonAssocRing R]

theorem _root_.isStarProjection_one_sub_iff [StarRing R] :
    IsStarProjection (1 - p) ↔ IsStarProjection p := ⟨fun h ↦ sub_sub_cancel 1 p ▸ IsStarProjection.one_sub h, .one_sub⟩

alias ⟨of_one_sub, _⟩ := isStarProjection_one_sub_iff

