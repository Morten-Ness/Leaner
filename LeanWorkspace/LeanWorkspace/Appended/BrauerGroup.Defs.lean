import Mathlib

section

variable {K : Type u} [Field K]

theorem is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  IsBrauerEquivalent.refl := IsBrauerEquivalent.refl
  IsBrauerEquivalent.symm := IsBrauerEquivalent.symm
  IsBrauerEquivalent.trans := IsBrauerEquivalent.trans

end

section

variable {K : Type u} [Field K]

theorem refl (A : CSA K) : IsBrauerEquivalent A A := ⟨1, 1, one_ne_zero, one_ne_zero, ⟨AlgEquiv.refl⟩⟩

end

section

variable {K : Type u} [Field K]

theorem symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := let ⟨n, m, hn, hm, ⟨iso⟩⟩ := h
  ⟨m, n, hm, hn, ⟨iso.symm⟩⟩

end

section

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

end
