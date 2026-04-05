import Mathlib

theorem subsingleton_of_isZero {G : CommGrpCat} (h : Limits.IsZero G) :
    Subsingleton G := (h.iso (CommGrpCat.isZero_of_subsingleton <| .of PUnit)).commGroupIsoToMulEquiv.subsingleton

