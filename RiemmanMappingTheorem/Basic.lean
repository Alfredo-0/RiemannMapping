import Mathlib.Data.Nat.Basic

def my_definition (n : ℕ) := n + 1

theorem my_lemma (n : ℕ) : my_definition n > n := by
  unfold my_definition
  exact Nat.lt_add_one n
