import Mathlib

variable {K : Type u} [Field K]

theorem trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  obtain ⟨n, m, hn, hm, ⟨iso1⟩⟩ := hAB
  obtain ⟨p, q, hp, hq, ⟨iso2⟩⟩ := hBC
  exact ⟨p * n, m * q, by simp_all, by simp_all,
    ⟨reindexAlgEquiv _ _ finProdFinEquiv |>.symm.trans <| compAlgEquiv _ _ _ _|>.symm.trans <|
    iso1.mapMatrix (m := Fin p)|>.trans <| compAlgEquiv _ _ _ _|>.trans <|
    reindexAlgEquiv K B (.prodComm (Fin p) (Fin m))|>.trans <| compAlgEquiv _ _ _ _|>.symm.trans <|
    iso2.mapMatrix.trans <| compAlgEquiv _ _ _ _|>.trans <| reindexAlgEquiv _ _ finProdFinEquiv⟩⟩

