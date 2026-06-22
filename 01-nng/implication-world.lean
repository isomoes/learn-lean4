import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.ApplyAt          -- `apply t at h`
import Mathlib.Tactic.Relation.Symm    -- `symm`, `symm at h`

-- Implication World: proving statements of the form `P → Q` ("if P then Q").
-- New tactics:
--   `exact h`        close the goal when `h` is *exactly* a proof of it.
--   `apply t at h`   if `t : P → Q` and `h : P`, rewrite `h` into a proof of `Q`
--                    (forwards reasoning). `apply t` on goal `Q` turns the goal
--                    into `P` (backwards reasoning).
--   `intro h`        to prove `P → Q`, assume `h : P` and then prove `Q`.
--   `symm`           swap the sides of an `=`, `≠`, or `↔` goal (or `symm at h`).
-- `a ≠ b` is *notation* for `a = b → False`, so it behaves like any implication:
-- `intro` it as a goal, `apply` it as a hypothesis.

-- Peano facts. NNG postulates these as axioms; for the real `Nat` they are
-- theorems, named here so the level proofs read like the game. `succ_inj` is
-- the injectivity of `succ`; `zero_ne_succ` says `0` is not a successor.
theorem succ_inj {a b : ℕ} (hab : Nat.succ a = Nat.succ b) : a = b := Nat.succ.inj hab

theorem zero_ne_succ (n : ℕ) : (0 : ℕ) ≠ Nat.succ n := (Nat.succ_ne_zero n).symm

theorem one_eq_succ_zero : (1 : ℕ) = Nat.succ 0 := rfl
theorem four_eq_succ_three : (4 : ℕ) = Nat.succ 3 := rfl

-- Level 1 — `exact`: the goal is one of several hypotheses; pick the right one.
set_option linter.unusedVariables false in
theorem exact_example (x y z : ℕ) (h1 : x + y = 37) (h2 : 3 * x + z = 42) :
    x + y = 37 := by
  exact h1

-- Level 2 — `exact` practice: rewrite a hypothesis until it *is* the goal.
theorem exact_practice (x y : ℕ) (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  rw [Nat.zero_add] at h     -- h : x = 0 + y + 2
  rw [Nat.zero_add] at h     -- h : x = y + 2
  exact h                    -- one-liner: `repeat rw [Nat.zero_add] at h; exact h`

-- Level 3 — `apply ... at`: use an implication hypothesis to push `h1` forwards.
theorem apply_example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42) : y = 42 := by
  apply h2 at h1             -- h1 : y = 42
  exact h1

-- Level 4 — `succ_inj`, forwards: massage `h` into `succ x = succ 3`, then cancel.
theorem succ_inj_forwards (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  rw [four_eq_succ_three] at h     -- h : x + 1 = succ 3
  rw [← Nat.succ_eq_add_one] at h  -- h : succ x = succ 3
  apply succ_inj at h              -- h : x = 3
  exact h

-- Level 5 — the same fact, arguing backwards: `apply succ_inj` to the *goal*.
theorem succ_inj_backwards (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  apply succ_inj                   -- goal : succ x = succ 3
  rw [Nat.succ_eq_add_one]         -- goal : x + 1 = succ 3
  rw [← four_eq_succ_three]        -- goal : x + 1 = 4
  exact h

-- Level 6 — `intro`: to prove `P → Q`, assume `P` and prove `Q`.
theorem intro_example (x : ℕ) : x = 37 → x = 37 := by
  intro h
  exact h

-- Level 7 — `intro` practice: `x + 1 = y + 1 → x = y`.
theorem intro_practice (x y : ℕ) : x + 1 = y + 1 → x = y := by
  intro h
  repeat rw [← Nat.succ_eq_add_one] at h   -- h : succ x = succ y
  apply succ_inj at h                      -- h : x = y
  exact h

-- Level 8 — `≠` is `... → False`: contradictory hypotheses prove anything.
theorem ne_example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2 at h1     -- h2 : x = y → False, so applying it to h1 gives h1 : False
  exact h1

-- Level 9 — `zero_ne_succ`: prove `0 ≠ 1`.
theorem zero_ne_one : (0 : ℕ) ≠ 1 := by
  intro h                        -- h : 0 = 1
  rw [one_eq_succ_zero] at h     -- h : 0 = succ 0
  apply zero_ne_succ at h        -- h : False
  exact h

-- Level 10 — `symm`: flip the `≠` so we can reuse `zero_ne_one` for `1 ≠ 0`.
theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
  symm
  exact zero_ne_one

-- Level 11 — `2 + 2 ≠ 5`, with every numeral unfolded to `succ`s as in the game.
theorem two_add_two_ne_five :
    Nat.succ (Nat.succ 0) + Nat.succ (Nat.succ 0)
      ≠ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))) := by
  intro h
  rw [Nat.add_succ, Nat.add_succ, Nat.add_zero] at h   -- h : succ⁴ 0 = succ⁵ 0
  repeat apply succ_inj at h                            -- h : 0 = succ 0
  apply zero_ne_succ at h                               -- h : False
  exact h
