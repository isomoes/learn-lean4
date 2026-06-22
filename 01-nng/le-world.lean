import Mathlib.Data.Nat.Notation
import Mathlib.Tactic            -- `obtain`, `use`, `rcases`

-- ≤ World (Less-Or-Equal). NNG *defines* the order on ℕ by an existential:
--   `a ≤ b := ∃ c, b = a + c`   ("there is something you can add to a to get b").
-- For Lean's REAL `≤` on ℕ that existential is not the definition, but two core
-- lemmas form the exact bridge, and they mirror NNG's `use`/`obtain`:
--   `Nat.le.intro : a + k = b → a ≤ b`   — supply a witness k, like NNG's `use k`.
--   `Nat.le.dest  : a ≤ b → ∃ k, a + k = b` — pull out the witness, like `obtain`.
-- (NNG writes `b = a + c`; the core lemmas use `a + k = b`. Same content, sides
-- swapped — we just `symm`/rewrite as needed.) Every level below is stated with
-- the real `a ≤ b` so it reads like the game, and proved through the .intro/.dest
-- bridge plus the Addition-World lemmas — never by calling the matching core
-- order lemma (`Nat.le_refl`, `Nat.le_trans`, ...) directly.

-- Full `Mathlib.Tactic` puts root-level `zero_add`, `add_comm`, `le_refl`, ...
-- in scope, which would clash with the names we want to (re)prove. We work inside
-- a namespace so each level keeps its game name without colliding.
namespace LeWorld

-- Addition results carried over from Addition World (restated in NNG `succ` form).
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

-- Cancellation helper, by induction on the cancelled summand `n` (NNG's
-- `add_right_cancel`). Needed below to show a witness must be 0.
theorem add_right_cancel (a b n : ℕ) (h : a + n = b + n) : a = b := by
  induction n with
  | zero      => rw [Nat.add_zero, Nat.add_zero] at h; exact h
  | succ d hd =>
    rw [Nat.add_succ, Nat.add_succ] at h
    exact hd (Nat.succ.inj h)

-- If a sum is 0 then the right summand is 0 (the only witness reaching a ≤ 0).
theorem add_right_eq_zero (a b : ℕ) (h : a + b = 0) : b = 0 := by
  cases b with
  | zero   => rfl
  | succ d =>
    rw [Nat.add_succ] at h        -- h : succ (a + d) = 0
    exact absurd h (Nat.succ_ne_zero _)

-- Level 1 — le_refl: `a ≤ a`. NNG: `use 0`. Here: the witness is 0, fed to .intro.
theorem le_refl (a : ℕ) : a ≤ a := by
  apply Nat.le.intro (k := 0)     -- goal : a + 0 = a
  rw [Nat.add_zero]

-- Level 2 — zero_le: `0 ≤ a`. NNG: `use a`. The witness is `a` itself.
theorem zero_le (a : ℕ) : 0 ≤ a := by
  apply Nat.le.intro (k := a)     -- goal : 0 + a = a
  rw [zero_add]

-- Level 3 — le_succ_self: `a ≤ succ a`. NNG: `use 1`. The witness is 1.
theorem le_succ_self (a : ℕ) : a ≤ Nat.succ a := by
  apply Nat.le.intro (k := 1)     -- goal : a + 1 = succ a
  rw [← Nat.succ_eq_add_one]

-- Level 4 — le_trans: from `a ≤ b` and `b ≤ c`, get `a ≤ c`. NNG: `obtain` both
-- witnesses x, y, then `use x + y`. We add the two equations to land at `a + (x + y) = c`.
theorem le_trans (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  obtain ⟨x, hx⟩ := Nat.le.dest hab   -- hx : a + x = b
  obtain ⟨y, hy⟩ := Nat.le.dest hbc   -- hy : b + y = c
  apply Nat.le.intro (k := x + y)     -- goal : a + (x + y) = c
  rw [← add_assoc, hx, hy]

-- Level 5 — le_zero: `a ≤ 0 → a = 0`. NNG: `obtain` the witness; a sum is 0 only
-- when both parts are, so the witness reasoning forces a = 0.
theorem le_zero (a : ℕ) (h : a ≤ 0) : a = 0 := by
  obtain ⟨x, hx⟩ := Nat.le.dest h     -- hx : a + x = 0
  -- a + x = 0 means a = 0: commute, then peel x off.
  rw [add_comm] at hx                 -- hx : x + a = 0
  exact add_right_eq_zero x a hx

-- Level 6 — le_antisymm: `a ≤ b → b ≤ a → a = b`. Both witnesses are forced to 0.
-- NNG: obtain x with `a + x = b` and y with `b + y = a`; chase the arithmetic so
-- `x = 0`, hence `a + 0 = b`.
theorem le_antisymm (a b : ℕ) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  obtain ⟨x, hx⟩ := Nat.le.dest hab   -- hx : a + x = b
  obtain ⟨y, hy⟩ := Nat.le.dest hba   -- hy : b + y = a
  -- Substitute hx into hy: a + (x + y) = a, so x + y = 0, so x = 0.
  rw [← hx, add_assoc] at hy          -- hy : a + (x + y) = a
  -- a + (x + y) = a + 0, so cancel a on the left to get x + y = 0.
  have hy' : a + (x + y) = a + 0 := by rw [Nat.add_zero]; exact hy
  have hxy : x + y = 0 := by
    rw [add_comm a (x + y), add_comm a 0] at hy'   -- (x+y)+a = 0+a
    exact add_right_cancel (x + y) 0 a hy'
  have hx0 : x = 0 := by
    cases x with
    | zero   => rfl
    | succ d => rw [succ_add] at hxy; exact absurd hxy (Nat.succ_ne_zero _)
  rw [hx0, Nat.add_zero] at hx        -- hx : a = b
  exact hx

-- Level 7 — succ_le_succ: `a ≤ b → succ a ≤ succ b`. The witness is unchanged;
-- `succ a + k = succ b` follows from `a + k = b` by `succ_add`.
theorem succ_le_succ (a b : ℕ) (h : a ≤ b) : Nat.succ a ≤ Nat.succ b := by
  obtain ⟨k, hk⟩ := Nat.le.dest h     -- hk : a + k = b
  apply Nat.le.intro (k := k)         -- goal : succ a + k = succ b
  rw [succ_add, hk]

-- Level 8 — le_total: `a ≤ b ∨ b ≤ a`. By induction on `a`. Base: `0 ≤ b` always.
-- Step: if succ d ≤ b or b ≤ succ d holds, push the order through the new successor.
theorem le_total (a b : ℕ) : a ≤ b ∨ b ≤ a := by
  induction a with
  | zero      => exact Or.inl (zero_le b)
  | succ d hd =>
    cases hd with
    | inr hba =>
      -- b ≤ d ≤ succ d, so b ≤ succ d.
      exact Or.inr (le_trans b d (Nat.succ d) hba (le_succ_self d))
    | inl hdb =>
      -- d ≤ b: either the witness is 0 (so b = d ≤ succ d, giving b ≤ succ d) or
      -- positive (so succ d ≤ b). Inspect the witness.
      obtain ⟨k, hk⟩ := Nat.le.dest hdb   -- hk : d + k = b
      cases k with
      | zero   =>
        rw [Nat.add_zero] at hk           -- hk : d = b
        rw [← hk]
        exact Or.inr (le_succ_self d)
      | succ e =>
        -- d + succ e = b ⇒ succ d + e = b ⇒ succ d ≤ b.
        apply Or.inl
        apply Nat.le.intro (k := e)       -- goal : succ d + e = b
        rw [succ_add, ← Nat.add_succ, hk]

-- Level 9 — add_le_add_right: `a ≤ b → a + c ≤ b + c`. The witness carries over;
-- `(a + c) + k = b + c` from `a + k = b` by reassociating and commuting.
theorem add_le_add_right (a b : ℕ) (h : a ≤ b) (c : ℕ) : a + c ≤ b + c := by
  obtain ⟨k, hk⟩ := Nat.le.dest h     -- hk : a + k = b
  apply Nat.le.intro (k := k)         -- goal : (a + c) + k = b + c
  rw [add_assoc, add_comm c k, ← add_assoc, hk]

end LeWorld
