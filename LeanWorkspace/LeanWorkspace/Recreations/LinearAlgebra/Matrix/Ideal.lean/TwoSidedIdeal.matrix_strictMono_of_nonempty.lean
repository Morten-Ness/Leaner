import Mathlib

variable {R : Type*} (n : Type*)

variable [NonUnitalNonAssocRing R] [Fintype n]

theorem matrix_strictMono_of_nonempty [h : Nonempty n] :
    StrictMono (TwoSidedIdeal.matrix (R := R) n) :=
  TwoSidedIdeal.matrix_monotone n |>.strictMono_of_injective <|
    .comp (fun _ _ => TwoSidedIdeal.mk.inj) <| (RingCon.matrix_injective n).comp ringCon_injective

