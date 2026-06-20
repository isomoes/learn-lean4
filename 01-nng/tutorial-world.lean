theorem one_eq_succ_zero   : (1 : Nat) = Nat.succ 0 := rfl
theorem two_eq_succ_one    : (2 : Nat) = Nat.succ 1 := rfl
theorem three_eq_succ_two  : (3 : Nat) = Nat.succ 2 := rfl
theorem four_eq_succ_three : (4 : Nat) = Nat.succ 3 := rfl

/-
## The real-Lean proof: just compute
-/
example : (2 : Nat) + 2 = 4 := rfl

example : (2 : Nat) + 2 = 4 := by
  rw [two_eq_succ_one, one_eq_succ_zero, Nat.add_succ, Nat.add_succ, Nat.add_zero,
      four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
