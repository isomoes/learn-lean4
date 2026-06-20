/-
# Tutorial World ✅

Status: **completed** — through the final level `2 + 2 = 4`.
Part of Phase 1 — Natural Number Game (see `README.md`).

NNG runs in the browser, so this file re-creates a *minimal* NNG environment in
core Lean (no Mathlib import) and re-proves the world's capstone level, so the
note is an artifact that actually type-checks. Open it in the editor and watch
the InfoView, exactly like the game.

Check it standalone with:  `lake env lean 01-nng/tutorial-world.lean`

--------------------------------------------------------------------------------
## Tactics introduced

* `rfl`  — closes a goal that is *syntactically* equal on both sides (in NNG,
  after `add_succ`/`add_zero` have computed the sums). This is **not** the full
  definitional `rfl` of real Lean.
* `rw [h]` — rewrites left→right with equation `h`; `rw [← h]` reverses. Rewrites
  **all** matching occurrences, then auto-tries `rfl`.
* `nth_rewrite n [h]` / `nth_rw n [h]` — rewrites only the **n-th** occurrence
  (1-indexed). `nth_rw` also auto-`rfl`s. These are Mathlib tactics and may be
  **locked** at this level — useful to know for later. (Shown as a comment below;
  using them for real would need `import Mathlib.Tactic`.)

## Key lemmas (defined concretely below)

* `add_zero a : a + 0 = a`
* `add_succ a b : a + succ b = succ (a + b)`   ← the engine that *computes* a sum
* `succ_eq_add_one n : succ n = n + 1`          ← turns a successor into `+ 1`
                                                  (rarely what you want)
* numeral expansions: `one_eq_succ_zero`, `two_eq_succ_one`,
  `three_eq_succ_two`, `four_eq_succ_three`
-/

namespace Nng

/-- NNG's natural numbers: `zero`, or the `succ`essor of a natural number. -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

/-- Addition, defined by recursion on the **second** argument (as in NNG):
    `a + 0 = a` and `a + succ b = succ (a + b)`. -/
def add : MyNat → MyNat → MyNat
  | a, .zero   => a
  | a, .succ b => .succ (add a b)

instance : Add MyNat := ⟨add⟩

-- Numerals 0..4 as `MyNat`, so `2 + 2 = 4` parses with literals, like in the game.
instance : OfNat MyNat 0 := ⟨.zero⟩
instance : OfNat MyNat 1 := ⟨.succ .zero⟩
instance : OfNat MyNat 2 := ⟨.succ (.succ .zero)⟩
instance : OfNat MyNat 3 := ⟨.succ (.succ (.succ .zero))⟩
instance : OfNat MyNat 4 := ⟨.succ (.succ (.succ (.succ .zero)))⟩

-- The world's lemmas. In this concrete model each holds *by definition* (`rfl`) —
-- which is exactly why NNG can hand them to you as facts to rewrite with.
theorem add_zero (a : MyNat) : a + 0 = a := rfl
theorem add_succ (a b : MyNat) : a + succ b = succ (a + b) := rfl
theorem succ_eq_add_one (n : MyNat) : succ n = n + 1 := rfl
theorem one_eq_succ_zero : (1 : MyNat) = succ 0 := rfl
theorem two_eq_succ_one : (2 : MyNat) = succ 1 := rfl
theorem three_eq_succ_two : (3 : MyNat) = succ 2 := rfl
theorem four_eq_succ_three : (4 : MyNat) = succ 3 := rfl

/-
## Lesson: proving `2 + 2 = 4`

**The trap:** expanding `4` into `1 + 1 + 1 + 1` (via `succ_eq_add_one`) leaves
`1 + 1 + (1 + 1) = 1 + 1 + 1 + 1`, which differs only by **associativity**. NNG's
`rfl` is syntactic and there's no `add_assoc` unlocked yet → dead end.

**The fix:** compute the left side down to `succ` form with `add_succ`/`add_zero`,
and expand `4` into `succ` form too — never use `succ_eq_add_one` to evaluate a sum.

Goal-state trace (watch the InfoView):

  #  command                    resulting goal
  0  (start)                    2 + 2 = 4
  1  rw [two_eq_succ_one]       succ 1 + succ 1 = 4
  2  rw [one_eq_succ_zero]      succ (succ 0) + succ (succ 0) = 4
  3  rw [add_succ]              succ (succ (succ 0) + succ 0) = 4
  4  rw [add_succ]              succ (succ (succ (succ 0) + 0)) = 4
  5  rw [add_zero]              succ (succ (succ (succ 0))) = 4
  6  rw [four_eq_succ_three]    … = succ 3
  7  rw [three_eq_succ_two]     … = succ (succ 2)
  8  rw [two_eq_succ_one]       … = succ (succ (succ 1))
  9  rw [one_eq_succ_zero]      both sides succ⁴ 0 → closed

(`rw`'s trailing `rfl` closes it after step 9 — don't add an extra `rfl`.)
-/
example : (2 : MyNat) + 2 = 4 := by
  rw [two_eq_succ_one, one_eq_succ_zero, add_succ, add_succ, add_zero,
      four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]

/-
**Alternative with `nth_rewrite`** (if unlocked — it's a Mathlib tactic, needs
`import Mathlib.Tactic`). Expand only the *right* summand:

    example : (2 : MyNat) + 2 = 4 := by
      nth_rewrite 2 [two_eq_succ_one]   -- 2 + succ 1 = 4
      rw [add_succ, one_eq_succ_zero, add_succ, add_zero,
          four_eq_succ_three, three_eq_succ_two]

## Takeaways

* Read the InfoView goal state before every tactic; watch how each `rw`
  transforms it.
* In NNG, `rfl` only closes syntactically-equal goals — *compute* with
  `add_succ`/`add_zero`.
* `rw` hits **all** occurrences; use `nth_rewrite n` to target one (once unlocked).
* If a goal is true only by re-bracketing, you need `add_assoc` — if it's not
  unlocked, you took a wrong turn earlier.
-/

end MyNat
end Nng
