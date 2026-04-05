import Mathlib

theorem subsingleton_of_isTerminal {X : CommRingCat} (hX : IsTerminal X) : Subsingleton X := (hX.uniqueUpToIso CommRingCat.punitIsTerminal).commRingCatIsoToRingEquiv.toEquiv.subsingleton_congr.mpr
    (show Subsingleton PUnit by infer_instance)

