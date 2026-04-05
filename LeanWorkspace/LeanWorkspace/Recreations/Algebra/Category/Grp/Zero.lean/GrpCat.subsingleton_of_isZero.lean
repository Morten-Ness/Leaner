import Mathlib

theorem subsingleton_of_isZero {G : GrpCat} (h : Limits.IsZero G) :
    Subsingleton G := (h.iso (GrpCat.isZero_of_subsingleton <| .of PUnit)).groupIsoToMulEquiv.subsingleton

