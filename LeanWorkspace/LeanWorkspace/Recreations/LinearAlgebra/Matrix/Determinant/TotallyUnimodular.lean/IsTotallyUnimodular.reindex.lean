import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem IsTotallyUnimodular.reindex {A : Matrix m n R} (em : m ≃ m') (en : n ≃ n')
    (hA : A.IsTotallyUnimodular) :
    (A.reindex em en).IsTotallyUnimodular := hA.submatrix _ _

