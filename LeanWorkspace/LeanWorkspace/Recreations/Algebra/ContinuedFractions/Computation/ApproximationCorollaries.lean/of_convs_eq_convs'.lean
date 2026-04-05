import Mathlib

open scoped Topology

variable {K : Type*} (v : K) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem of_convs_eq_convs' : (of v).convs = (of v).convs' := ContFract.convs_eq_convs' (c := ContFract.of v)

