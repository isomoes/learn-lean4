theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero      => rw [Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, hd]

theorem succ_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero      => rw [Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, hd, Nat.add_succ]
