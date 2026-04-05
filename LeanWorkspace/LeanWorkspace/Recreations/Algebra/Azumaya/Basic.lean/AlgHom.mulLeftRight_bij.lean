import Mathlib

open scoped TensorProduct

variable (R A B : Type*) [CommSemiring R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem AlgHom.mulLeftRight_bij [h : IsAzumaya R A] :
    Function.Bijective (AlgHom.mulLeftRight R A) := h.bij

