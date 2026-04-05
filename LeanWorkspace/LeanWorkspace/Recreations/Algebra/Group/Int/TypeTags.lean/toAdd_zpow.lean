import Mathlib

theorem toAdd_zpow (a : Multiplicative ℤ) (b : ℤ) : (a ^ b).toAdd = a.toAdd * b := mul_comm _ _

