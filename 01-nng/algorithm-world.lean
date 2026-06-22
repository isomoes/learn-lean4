import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.ApplyAt          -- `apply t at h`
import Mathlib.Tactic.Contrapose       -- `contrapose!`

-- Algorithm World (faithful to NNG4's `Game/Levels/Algorithm`). Proofs like
-- `2 + 2 = 4` and `a + b + c + d + e = e + d + c + b + a` are tedious by hand; this
-- world builds the machinery to make the *computer* do them.
--   • Levels 1–4 turn "rearrange a sum" into a one-tactic job: `add_left_comm`, then
--     `simp only [...]`, then a home-made `simp_add` macro.
--   • Levels 5–7 define the helper functions `pred` and `is_zero` and use them to
--     finally *prove* the Peano facts we had been assuming: `succ_inj`, `succ_ne_zero`,
--     and `succ_ne_succ`.
--   • Levels 8–9 introduce `decide`, which runs a verified equality algorithm.
--
-- Full Mathlib already has root-level `add_comm`, `add_left_comm`, `is_zero`, … which
-- would clash with the names we want to (re)prove, so — like NNG's own `namespace MyNat`
-- — we work inside a namespace and restate the Addition-World lemmas in `succ` form.
namespace AlgorithmWorld

-- Carried over from Addition World (restated by induction so the file stands alone).
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

-- Level 1 — add_left_comm: pull the second summand to the front of a grouped sum.
-- The key rearrangement lemma the algorithm below is built from; proved by hand
-- from commutativity and associativity (recall `a + b + c` means `(a + b) + c`).
theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

-- Level 2 — "making life easier": forget the brackets, just reorder the variables.
-- `a + b + (c + d) = a + c + d + b`: push all brackets right with `add_assoc`, then
-- swap `b` past `c` (`add_left_comm`) and `b` past `d` (`add_comm`).
theorem add_algo1 (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  repeat rw [add_assoc]
  rw [add_left_comm b c]
  rw [add_comm b d]

-- Level 3 — "making life simple": `simp`, "`rw` on steroids", rewrites with every
-- lemma you feed it as much as it can, ordering variables so it can't loop. An
-- eight-variable shuffle nobody wants to do by hand — solved in one line.
theorem add_algo2 (a b c d e f g h : ℕ) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_left_comm, add_comm]

-- Level 4 — "the simplest approach": you can bundle a `simp only [...]` call into your
-- own tactic. `simp_add` runs `simp only [add_assoc, add_left_comm, add_comm]`, and so
-- closes any pure-reassociation/commutation goal about `+`.
macro "simp_add" : tactic => `(tactic| simp only [add_assoc, add_left_comm, add_comm])

theorem add_algo3 (a b c d e f g h : ℕ) :
    (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

-- Level 5 — pred: addition was defined by recursion; functions out of ℕ can be too.
-- `pred` tries to subtract one, returning a junk value `37` at `0`:
--   `pred 0 := 37`,  `pred (succ n) := n`.
-- With the lemma `pred_succ : pred (succ n) = n` we can finally *prove* `succ_inj`,
-- the injectivity of `succ` we had been assuming as a Peano axiom.
def pred : ℕ → ℕ
  | 0          => 37
  | Nat.succ n => n

theorem pred_succ (n : ℕ) : pred (Nat.succ n) = n := rfl

theorem succ_inj (a b : ℕ) (h : Nat.succ a = Nat.succ b) : a = b := by
  rw [← pred_succ a, h, pred_succ]

-- Level 6 — is_zero: a predicate defined by the same recursion trick,
--   `is_zero 0 := True`,  `is_zero (succ n) := False`,
-- with lemmas `is_zero_zero : is_zero 0 = True` and `is_zero_succ n : is_zero (succ n) = False`.
-- Rewriting `False` into `is_zero (succ a)` and computing lets us prove Peano's last
-- axiom honestly (no appeal to `zero_ne_succ`). `trivial` discharges the goal `True`.
def is_zero : ℕ → Prop
  | 0          => True
  | Nat.succ _ => False

theorem is_zero_zero : is_zero 0 = True := rfl
theorem is_zero_succ (n : ℕ) : is_zero (Nat.succ n) = False := rfl

theorem succ_ne_zero (a : ℕ) : Nat.succ a ≠ 0 := by
  intro h
  rw [← is_zero_succ a, h, is_zero_zero]
  trivial

-- Level 7 — succ_ne_succ: the last piece of the equality-deciding algorithm — if
-- `a ≠ b` then `succ a ≠ succ b`. `contrapose! h` swaps to the contrapositive
-- (hypothesis `succ m = succ n`, goal `m = n`), which `succ_inj` finishes.
theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : Nat.succ m ≠ Nat.succ n := by
  contrapose! h
  apply succ_inj at h
  exact h

-- Level 8 — decide: the four facts above (`0 = 0`, `0 ≠ succ n`, `succ m ≠ 0`,
-- and `succ_ne_succ`) assemble into a verified `DecidableEq ℕ` algorithm. Because it
-- is proven correct, the `decide` tactic may run it to settle concrete (in)equalities.
theorem add_algo_decide : (20 : ℕ) + 20 = 40 := by decide

-- Level 9 — decide again: the unsatisfying hand proof of `2 + 2 ≠ 5` from Implication
-- World, now a one-liner. The boss of Algorithm World.
theorem two_add_two_ne_five : (2 : ℕ) + 2 ≠ 5 := by decide

end AlgorithmWorld
