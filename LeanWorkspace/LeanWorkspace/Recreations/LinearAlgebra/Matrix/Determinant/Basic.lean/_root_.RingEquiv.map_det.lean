import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

variable {S : Type w} [CommRing S]

theorem _root_.RingEquiv.map_det (f : R ≃+* S) (M : Matrix n n R) :
    f M.det = Matrix.det (f.mapMatrix M) := f.toRingHom.map_det _

