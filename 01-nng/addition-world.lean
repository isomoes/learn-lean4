import Mathlib.Data.Nat.Notation

theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero      => rw [Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, hd]

theorem succ_add (a b : ℕ) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero      => rw [Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, hd, Nat.add_succ]

theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction b with
  | zero      => rw [Nat.add_zero, zero_add]
  | succ d hd => rw [Nat.add_succ, succ_add, hd]

theorem add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with
  | zero      => rw [Nat.add_zero, Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, hd]

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, ← add_assoc]
