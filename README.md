# Learn Lean 4: Prove Mathematics by Code

A self-paced learning plan for using the **Lean 4** proof assistant to formalize and machine-check mathematical proofs. This repo is your workspace, your notebook, and your roadmap.

> Official starting hub: <https://lean-lang.org/learn/>

---

## What is this?

**Lean** is an *interactive theorem prover*: a programming language whose programs are mathematical proofs, and a checker that mechanically verifies every step. When you "prove math by code," you write a statement (a *theorem*) and then construct a proof that Lean's kernel accepts as correct. If it compiles, it is *true* — there are no hand-waves, no "clearly," no gaps.

The core experience is the **goal–tactic loop**:

1. You state a goal (what you want to prove). Lean shows you the **goal state** in an *InfoView* panel: your hypotheses sit above a turnstile `⊢`, and the thing to prove sits below it.
2. You apply a **tactic** — a single proof step like `rw`, `intro`, `ring`, or `induction`.
3. Lean updates the goal state. Either the goal is closed, or you see exactly what remains.
4. Repeat until there are no goals left. Done — the theorem is proved and verified.

**Mathlib** is Lean's vast community library of formalized mathematics (algebra, analysis, topology, number theory, and far more). Most real formalization work builds on it.

**The goal of this repo:** take you from zero to confidently proving real theorems and contributing your own formalizations, following a curriculum ordered for someone who cares about *mathematics* first and programming second.

---

## Prerequisites & Setup (Arch Linux + Neovim)

You need: comfort with high-school algebra and the *idea* of a proof. No prior Lean, no prior programming required. The early phases (Natural Number Game) run entirely in a browser, so you can start learning today and install the toolchain in parallel.

This guide targets **Arch Linux** with **Neovim** (via [lean.nvim](https://github.com/Julian/lean.nvim)), following the [Arch Wiki Lean page](https://wiki.archlinux.org/title/Lean).

### What you'll install

- **elan** — the Lean toolchain manager (installs and version-manages `lean` and `lake` per project). On Arch, install it from the **AUR**, not the official repos.
- **Neovim** + **lean.nvim** — the editor and its Lean plugin: live **InfoView** (goal state), unicode input, and an LSP-backed proof loop. lean.nvim launches the Lean server itself — there is **no separate language server** to install for Lean 4.
- A **Mathlib-backed Lake project** — your local sandbox with the full library precompiled.

### 1. Install base tooling (official repos)

```bash
sudo pacman -S --needed git curl neovim
```

> lean.nvim needs Neovim **≥ 0.11** (0.12.x recommended). Check with `nvim --version`.

### 2. Install elan from the AUR

The Arch Wiki documents `elan` (from the AUR) as the *sole* recommended way to get Lean 4: it manages per-project toolchains under `~/.elan/toolchains` with no root access, which matters because Lean ships frequent nightly builds.

```bash
paru -S elan        # or:  yay -S elan
```

> If your AUR helper can't find `elan`, the package may be published as `elan-lean` — try `paru -S elan-lean`. Both provide the same `elan` binary.
>
> **Not using an AUR helper?** The upstream installer also works (this is *not* the Arch-preferred route, but it's the official upstream):
> ```bash
> curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
> ```
> Then restart your shell so `~/.elan/bin` is on `PATH`.

⚠️ Use elan **exclusively**. Don't install a separate system "lean" package, and **don't** install `lean-language-server` — that AUR package is **Lean 3 only**; the Lean 4 server ships inside the elan toolchain.

Verify:

```bash
elan --version
```

### 3. Install lean.nvim

Add [lean.nvim](https://github.com/Julian/lean.nvim) to your plugin manager. With **lazy.nvim**, drop this in your plugin spec (e.g. `~/.config/nvim/lua/plugins/lean.lua`):

```lua
return {
  'Julian/lean.nvim',
  ft = 'lean',                       -- load on Lean files (remove to load eagerly)
  dependencies = {
    -- Optional but recommended: enables :Telescope loogle and
    -- :Telescope lean_abbreviations. (Modern lean.nvim does NOT need plenary.)
    'nvim-telescope/telescope.nvim',
  },
  ---@type lean.Config
  opts = {
    mappings = true,                 -- suggested <LocalLeader> keymaps in Lean buffers
    abbreviations = { enable = true, leader = '\\' },  -- \to → → , \all → ∀ , ...
    infoview = { autoopen = true },  -- persistent goal-state window
    -- lean.nvim starts the Lean server itself (lake serve / lean --server);
    -- do NOT add Lean to nvim-lspconfig or mason, or you'll run two servers.
  },
}
```

> **Set your localleader before plugins load** — put `vim.g.maplocalleader = ','` near the top of `init.lua`, *before* `require('lazy').setup(...)`. The `mappings = true` keymaps hang off `<LocalLeader>`, and lean.nvim rebinds `K` to interactive hover in Lean buffers.

Then run `:Lazy sync`. (For vim-plug, the [Arch Wiki](https://wiki.archlinux.org/title/Lean#Using_Lean_with_Neovim) shows the `Plug` form ending in `:PlugInstall`.)

### 4. Create a Mathlib-backed project

```bash
# Creates a project pinned to exactly the toolchain Mathlib currently needs
lake +leanprover-community/mathlib4:lean-toolchain new my_project math
cd my_project
```

The `math` template adds **mathlib4** as a dependency and writes a `lakefile.toml` plus a `lean-toolchain` file. The `lake +leanprover-community/mathlib4:lean-toolchain` prefix runs Lake using the exact Lean version Mathlib needs, so the toolchains match.

> Alternative (pin a specific release): `lake +v4.24.0 new my_project math` — substitute the current stable tag.

### 5. Download the precompiled Mathlib cache

```bash
lake exe cache get
```

This downloads thousands of precompiled `.olean` files. **Always do this** — skipping it forces `lake build` to compile all of Mathlib from source, which takes *hours* and a lot of RAM. (`cache get` only works in projects that depend on mathlib4.)

### 6. Build to verify the wiring

```bash
lake build
```

After `cache get`, this is fast — only your own files compile.

### 7. Smoke-test in Neovim

Create `Test.lean` in the **project root**:

```lean
import Mathlib.Topology.Basic
#check TopologicalSpace
```

Open it from *inside* the project so lean.nvim can find it (the server walks up for `lakefile.toml` / `lean-toolchain`):

```bash
nvim Test.lean
```

Put your cursor on the `#check` line. The **InfoView** auto-opens (toggle with `<LocalLeader>i` / `:LeanInfoviewToggle`) and should show type information. Wait for the progress bars to clear — the *first* Mathlib file in a session can take many seconds to elaborate even with the cache. If the goal state appears, Mathlib imports resolve and you're ready.

> ⚠️ Always open Neovim **inside the project** (the folder with `lakefile.toml` + `lean-toolchain`), not a stray `.lean` file elsewhere — outside a project you get a degraded server with no Mathlib.

### Verify the CLI

```bash
elan --version
lean --version
lake --version
elan toolchain list
```

### Keeping things up to date

```bash
# Bump to the current Mathlib toolchain, then refetch deps + cache
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
lake exe cache get     # use cache get! to force a clean re-download
```

### Neovim InfoView & unicode input

**InfoView.** lean.nvim opens a persistent **InfoView** window that live-updates as you move the cursor: it lists your local hypotheses, then a turnstile line `⊢`, then the goal below it (multiple goals are numbered). It auto-opens on your first `.lean` buffer; toggle it with `<LocalLeader>i`, jump into it with `<LocalLeader><Tab>`. **Pins** (`<LocalLeader>x` add / `<LocalLeader>c` clear) and **diff-pins** freeze and compare goal states so you can see exactly what a tactic changed. With the InfoView closed, `:LeanGoal` shows the goal in a popup. If a file gets wedged, `:LeanRestartFile` (`<LocalLeader>r`) restarts just that file's server.

**Unicode input.** In insert mode, type the backslash leader `\` then a name and it expands on `<Tab>` / `<CR>` (or when you leave insert mode): `\to` → →, `\all` → ∀, `\le` → ≤, `\and` → ∧, `\iff` → ↔, `\Nat` → ℕ, `\R` → ℝ, `\lam` → λ, `\exists` → ∃. For a literal backslash, type `\\`. To learn how to type a symbol already on screen, put the cursor on it and run `:LeanAbbreviationsReverseLookup` (`<LocalLeader>\`), or browse them all with `:Telescope lean_abbreviations`. Use a **Nerd Font / unicode-capable terminal font** so `⊢ λ ∀ ≤` and goal markers render.

**Loogle in-editor.** With telescope.nvim installed, `:Telescope loogle` searches Mathlib by name or type signature without leaving Neovim (needs network — it calls the public Loogle API).

### Common pitfalls

| Symptom | Fix |
| --- | --- |
| `lake build` compiles all of Mathlib for hours | You skipped `lake exe cache get`. Run it first. |
| InfoView empty / no goal on first Mathlib file | Expected — importing Mathlib reads huge `.olean` files. Wait for the progress bars to clear. |
| Mathlib imports unresolved; degraded server | You opened a stray `.lean` outside the project. Launch `nvim` **inside** the project root. |
| Installed `lean-language-server` for Lean 4 | Don't — that AUR package is Lean 3 only. The Lean 4 server ships in the elan toolchain. |
| Added Lean to nvim-lspconfig / mason → two servers | Don't. lean.nvim starts `leanls` itself via `vim.lsp.enable`. |
| `mappings = true` keymaps on wrong prefix; `K` changed | Set `vim.g.maplocalleader` **before** lean.nvim loads. `K` → interactive hover is intentional. |
| `elan` not found by AUR helper | Try the `elan-lean` package name, or the upstream `elan-init.sh` script. |
| Build errors after editing `lean-toolchain` by hand | Toolchain must match the Mathlib commit. Run `lake update` then `lake exe cache get`. |
| `:Telescope loogle` returns nothing | Needs telescope.nvim installed **and** network access. |

---

## Phased Curriculum

A spine ordered for a **math learner**. Each phase has a goal, primary resource(s), what to skip, a concrete milestone, and a time estimate. You can start Phase 1 in a browser *before* finishing setup.

### Phase 0 — Setup & orientation

| | |
| --- | --- |
| **Goal** | Working Lean 4 + Neovim + Mathlib project; understand the goal–tactic loop and the InfoView. |
| **Resource** | The **Prerequisites & Setup** section above; the official hub <https://lean-lang.org/learn/>. |
| **Skip** | Nothing — but you can defer full local setup until Phase 2 and play Phase 1 in the browser meanwhile. |
| **Milestone** | The `#check TopologicalSpace` smoke test shows type info in the InfoView; `lake build` succeeds. |
| **Time** | 1–2 hours (plus background time for the Mathlib cache download). |

### Phase 1 — Natural Number Game (NNG4)

| | |
| --- | --- |
| **Goal** | Internalize the core tactics by building the natural numbers from scratch. Zero install, browser-only. |
| **Resource** | **Natural Number Game** at <https://adam.math.hhu.de/> — 9 worlds, ~79 levels. |
| **Order** | Tutorial → Addition → Multiplication → Power, doing **Implication before/with Power** (Power uses inequality + logic tactics). Then Advanced Addition → Less-Or-Equal → Advanced Multiplication → Algorithm. |
| **Skip** | If you only want a feel for Lean, you can stop after the first **4–5 worlds**. Advanced Addition/Multiplication and Algorithm are repetitive — skim them if impatient. |
| **Key takeaways** | `rfl`, `rw` (rewriting with equalities), `induction`, and the logic tactics `intro` / `exact` / `apply` (Implication World). |
| **Milestone** | *You can now prove* `add_comm`, `add_assoc`, `mul_comm`, and basic inequalities by induction — entirely on your own. |
| **Time** | ~4–10 hours. |

> Optional follow-on games (same site, save for after the basics click): **Set Theory Game** (Velleman), **Robo/Scribble** (Zibrowius), **Logic Game**, **Knights and Knaves**. Topic-specific ones (**Real Analysis Game**, **Linear Algebra Game**) are best saved until you're comfortable with tactics.

### Phase 2 — The Mechanics of Proof (Math 2001)

| | |
| --- | --- |
| **Goal** | Bridge from NNG's sandbox to genuine mathematical reasoning, while keeping the Lean surface small. This is the step that prevents the "Mathlib cliff." |
| **Resource** | Heather Macbeth, **The Mechanics of Proof** — <https://hrmacbeth.github.io/math2001/> |
| **Do thoroughly (in Lean, not passively)** | Ch. 1 Calculation (`calc`, `ring`, `rel`), Ch. 2 Structure (`intro`, `obtain`, `constructor`), Ch. 3 Parity & Divisibility, Ch. 4 Casework (`rcases`, `left`/`right`), **Ch. 5 Logic** (negation, `by_cases`, `push_neg`), **Ch. 6 Induction** (the full induction zoo). `calc`, induction, and quantifier/negation handling are the load-bearing skills. |
| **Skim if short on time** | Ch. 7 Number Theory, Ch. 8 Functions, Ch. 9 Sets, Ch. 10 Relations — at least skim for the Lean *idioms* even if you know the math. |
| **Do NOT skip** | The **"Transitioning to Mainstream Lean"** appendix and the **Index of Tactics** — read them right before Phase 3. They map the book's training-wheel tactics (`numbers`→`norm_num`, `addarith`→`linarith`, `rel`→`gcongr`, `exhaust`→`duper`) to real Mathlib tactics. |
| **Milestone** | *You can now write* multi-step `calc` proofs, case-split on `Or`, prove statements with `∀`/`∃` and negations, and run several flavors of induction — and you know how to translate to real Mathlib. |
| **Time** | ~40–80 hours full; a fast track is Ch. 1–2, then 5, 6, and the transition appendix. |

### Phase 3 — Mathematics in Lean (MIL): the core

The canonical do-it-by-doing formalization tutorial. **Website = textbook; companion repo = workspace.**

- Read: <https://leanprover-community.github.io/mathematics_in_lean/>
- Clone the companion repo: `git clone https://github.com/leanprover-community/mathematics_in_lean`, then run `lake exe cache get` inside it.
- **Copy the `MIL` folder** so the originals stay intact, and edit your copy. Read the prose with Neovim open beside it, fill in each exercise, watch the InfoView, and check `solutions/` only *after* attempting.
- Keep current: `git pull` then `lake exe cache get`.

| Sub-phase | Chapters | Status | Notes |
| --- | --- | --- | --- |
| **3a — Foundations (must-do)** | 2 Basics, 3 Logic, 4 Sets and Functions | Required | Teaches the core tactic vocabulary (`rw`, `calc`, `ring`, `linarith`, `intro`, `rcases`, `use`, `apply`, `exact`) and lemma search (`apply?`, Loogle). Do not skip. |
| **3b — Mathlib fluency** | 5 Number Theory, 6 Discrete Math, 7 Structures, 8 Hierarchies, 9 Groups & Rings | Strongly recommended | Builds real Mathlib fluency and type-class understanding (`Finset`, `BigOperators`, defining your own structures, the algebraic hierarchy). |
| **3c — Domain showcases** | 10 Linear Algebra, 11 Topology, 12 Differential Calculus, 13 Integration & Measure Theory | Sample | Pick the ones matching your interests; **skip those whose math you don't yet know.** Don't grind all of them. |

| | |
| --- | --- |
| **Goal** | Formalize real undergraduate mathematics directly on top of Mathlib. |
| **Milestone** | *You can now prove* things like the irrationality of √2, infinitude of primes, and facts about injective/surjective functions — and find the Mathlib lemmas you need yourself. |
| **Time** | ~40–80 hours total; foundations (3a) are ~15–25 hours and are the non-negotiable core. |

### Phase 4 — Deepen the foundations (as needed)

Pull from these *when you hit something you don't understand* — they are companions, not a linear grind.

- **Theorem Proving in Lean 4 (TPIL)** — <https://lean-lang.org/theorem_proving_in_lean4/>
  Read when confusing type errors or low-level proofs make you ask *why Lean works*. Essential chapters: **2** Dependent Type Theory, **3** Propositions and Proofs (proofs *are* terms), **4** Quantifiers and Equality, **5** Tactics. Defer 7–9 (inductive types, recursion, structures) and 10 (type classes) until you need them; 11 (`conv`) and 12 (axioms) are reference.
- **Logic and Proof** — <https://leanprover-community.github.io/logic_and_proof/>
  Use if you want to truly understand *why proofs work*: natural-deduction inference rules, classical reasoning, intro/elim rules. Work the alternating logic-then-Lean chapters through **Ch. 10**, plus **Ch. 5** (classical reasoning). Treat Ch. 11–23 (sets/relations/functions/number theory applications) as optional, and skip the semantics/completeness chapters (6, 10) if you only want to formalize.

| | |
| --- | --- |
| **Goal** | Solid grounding so type errors and quantifier/logic subtleties stop being mysterious. |
| **Milestone** | *You can now* read and write term-mode proofs, explain propositions-as-types, and reason confidently about negation and classical logic. |
| **Time** | TPIL essentials ~10–20 hours; Logic and Proof core ~40–80 hours (sample as needed). |

### Phase 5 — Your own project / contribute to Mathlib

| | |
| --- | --- |
| **Goal** | Formalize something *you* care about, or contribute to Mathlib. This is where it becomes real. |
| **Ideas** | Formalize a theorem from a course or paper; fill a small gap in Mathlib; reprove a favorite result from scratch. |
| **Contribute** | Mathlib community + contribution guide via <https://leanprover-community.github.io/> and the Lean Zulip chat. |
| **Advanced reference** | **The Hitchhiker's Guide to Logical Verification (2025)** — <https://github.com/lean-forward/logical_verification_2025>. Graduate-level; strongest free resource for the *verification/semantics* side (operational/denotational semantics, Hoare logic, metaprogramming) that math tutorials omit. For a pure math track, prioritize Lectures **1–6** and **12–14** (logical foundations, mathematical structures, constructing ℚ and ℝ as quotient types); do Lecture **8** (Metaprogramming) if you want to write your own tactics. Prefer the 2025 edition for current Lean/Mathlib compatibility. |
| **Milestone** | *You have* a self-contained formalized result in this repo (or an open/merged Mathlib PR). |
| **Time** | Open-ended — this is the work. |

### Optional sidebar — Functional Programming in Lean (FPIL)

<https://lean-lang.org/functional_programming_in_lean/> — Lean *as a programming language*. Treat as a **supplement**, not the main path. Useful slice for a formalization learner: **Ch. 1** (Getting to Know Lean — the best concise tour of term syntax, `def`/`let`, inductive datatypes, pattern matching, recursion, polymorphism, structures), **Ch. 3** (Type Classes — central to how Mathlib organizes algebra), and a skim of the first **Interlude** (propositions as types). **Skip** Ch. 2 (IO) and Ch. 4–6 (monads/transformers) unless you'll write tactics or tooling.

---

## Reference & Tooling

### Lemma-search ladder

When you need a library lemma and don't know its name, climb this ladder:

1. **`exact?` / `apply?`** in the editor — instant, tries imported lemmas first.
2. **Mathlib4 docs** if you can *guess* the name from the naming convention.
3. **Loogle** if you know the *structure* (the Lean shapes).
4. **LeanSearch / LeanExplore** if you only know the math *in words*.

| Tool | URL | Use when… |
| --- | --- | --- |
| **Loogle** | <https://loogle.lean-lang.org/> | You can spell the definitions. Search by constant (`Real.sin`), name substring (`"differ"`), subexpression with `_`/`?a` wildcards (`_ * (_ ^ _)`), type signature (`(?a -> ?b) -> List ?a -> List ?b`), or conclusion (`|- _ < _ -> _`); comma-separate to AND filters. |
| **LeanSearch** | <https://leansearch.net/> | You know the math but not the Lean name. Natural-language/semantic search over Mathlib4 ("sum of a geometric series"). Watch for terminology mismatches ("sum" vs "add"). |
| **LeanExplore** | <https://www.leanexplore.com/> | Keyword + name search failed. Hybrid semantic search across multiple libraries with informal translations; also has an API/MCP. Open in a browser (may block plain HTTP fetches). |
| **Mathlib4 docs** | <https://leanprover-community.github.io/mathlib4_docs/> | You can guess names from the convention. Fuzzy substring search; full signatures, docstrings, source links. **Learn the naming convention here.** |

### In-editor search tactics

| Tactic | What it does |
| --- | --- |
| `exact?` | Finds a lemma that closes the goal *exactly*; offers a "Try this:" replacement. **Blind spot:** won't find rearranged equalities (`a - b = c` vs `a = b + c`). |
| `apply?` | Like `exact?` but also finds lemmas that *apply* and leave new subgoals. More powerful, slower. |
| `rw?` | Suggests rewrite lemmas matching a subterm; pick a suggestion to insert the `rw`. |
| `simp?` | Runs `simp`, then reports the exact `simp only [...]` lemmas used — makes `simp` reproducible/fast and reveals lemma names you can reuse. |

### Beginner tactic cheat sheet

| Tactic | What it proves / does |
| --- | --- |
| `rfl` | Goal true by definitional/computational equality (`a = a`, `2 + 2 = 4`). |
| `rw [h]` | Rewrites with equation/iff `h` (left→right; `rw [← h]` for right→left); `rfl`-closes when it reaches reflexivity. |
| `simp` | Simplifies using the `@[simp]` lemma set; `simp [foo]` to add, `simp only [...]` for a fixed set. |
| `exact e` | Supplies a term `e` whose type is exactly the goal. |
| `intro x` | Introduces a variable/hypothesis from `∀ x, P x` or `P → Q`. |
| `apply f` | Applies `f` whose conclusion matches the goal, leaving its hypotheses as subgoals. |
| `ring` | Equalities in any commutative (semi)ring (handles `+`, `*`, `^`, distributivity). |
| `linarith` | Goals following by linear arithmetic over ordered fields; `nlinarith` for some nonlinear cases. |
| `omega` | Decision procedure for linear arithmetic over `Nat`/`Int` (bounds, indices). |
| `norm_num` | Proves concrete numeric (in)equalities (`3 < 5`, primality via extensions). |
| `constructor` | Applies the goal's constructor: splits `And`, builds `Exists`/structures. |
| `rcases` / `obtain` | Destructures hypotheses: `obtain ⟨a, b, hab⟩ := h` for `And`/`Exists`/structures; `|` splits `Or`. |
| `cases h` | Case-splits by inductive constructors (`Or` → two goals, `Nat` → zero/succ). |
| `induction n` | Structural induction: base case + inductive step with an induction hypothesis (`with` to name cases). |
| `calc` | A readable transitive chain of (in)equalities, each step justified by a proof. |

---

## How to study effectively

- **Type every example yourself.** Reading proofs feels productive and teaches almost nothing. The skill is in your fingers and in reading goal states, not in recognizing finished proofs.
- **Read the InfoView goal state first, always.** Everything above `⊢` are hypotheses you can use; the expression below it is what you must prove. Move the cursor through the proof to watch each tactic transform the state — this is your single most important feedback loop.
- **Try to prove it before reading the solution.** Struggle is the point. Only peek at `solutions/` (MIL) or a hint after a genuine attempt.
- **Follow the search ladder, don't guess blindly.** `exact?`/`apply?` → docs → Loogle → LeanSearch. Use `simp?`/`rw?` to *discover* lemma names, then reuse them in precise `rw`/`exact` calls.
- **Learn Mathlib's naming convention early.** Names describe the statement: `add_comm`, `mul_pos`, `le_of_lt`, `Nat.succ_le_succ`. Once it clicks, you can *guess* names and confirm via dot-completion or docs.
- **Read the error, don't guess the fix.** When a tactic "almost" works, the InfoView names the offending subterm and expected type — that usually points straight to the fix or the lemma to search for.
- **Prefer `simp only` / named `rw` in finished proofs.** Bare `simp` is a great explorer but can break when Mathlib's simp set changes; pin down what you actually used.
- **Keep a notes file** (`notes/`). Record tactics you learned, lemmas you found, and the shape of proofs that worked. Future-you will reuse it constantly.
- **Don't fight the cliff.** If MIL feels brutal, you skipped too much of *The Mechanics of Proof*. Go back — that's exactly the bridge it builds.

---

## Suggested repo structure

```
learn-lean4/
├── README.md                 ← this plan
├── lakefile.toml             ← Mathlib-backed Lake project
├── lean-toolchain            ← pins the Lean version (managed by elan)
├── 00-setup/
│   └── Test.lean             ← import Mathlib.Topology.Basic smoke test
├── 01-nng/
│   └── notes.md              ← NNG is browser-based; record takeaways here
├── 02-mechanics/             ← exercises worked through Mechanics of Proof
│   └── Ch01Calculation.lean
├── 03-mil/                   ← your editable COPY of the MIL companion folder
│   └── ...
├── 04-foundations/           ← TPIL / Logic and Proof scratch work
├── 05-project/               ← your own formalization(s)
│   └── MyTheorem.lean
└── notes/
    ├── tactics.md            ← tactic cheat sheet you build as you go
    └── lemmas.md             ← useful Mathlib lemmas you discovered
```

Initialize the project at the repo root (see Setup) so a single `lakefile.toml` / `lean-toolchain` covers all phase folders, and run `lake exe cache get` once.

### Progress checklist

**Phase 0 — Setup**
- [x] elan installed; `lean`, `lake`, `elan` versions print
- [x] Neovim + lean.nvim installed (elan from the AUR)
- [x] Mathlib project created and `lake exe cache get` done
- [x] `lake build` succeeds; `#check TopologicalSpace` shows type info in InfoView

**Phase 1 — Natural Number Game**
- [ ] Tutorial + Addition + Multiplication + Power worlds
- [ ] Implication World (intro / exact / apply)
- [ ] (Optional) Advanced Addition, Less-Or-Equal, Advanced Multiplication, Algorithm
- [ ] Proved `add_comm` / `mul_comm` by induction on my own

**Phase 2 — The Mechanics of Proof**
- [ ] Ch. 1 Calculation · Ch. 2 Structure
- [ ] Ch. 3 Parity & Divisibility · Ch. 4 Casework
- [ ] Ch. 5 Logic · Ch. 6 Induction
- [ ] (Optional skim) Ch. 7–10 Number Theory / Functions / Sets / Relations
- [ ] Read "Transitioning to Mainstream Lean" + Index of Tactics

**Phase 3 — Mathematics in Lean**
- [ ] 3a Foundations: Basics, Logic, Sets and Functions (required)
- [ ] 3b Fluency: Number Theory, Discrete Math, Structures, Hierarchies, Groups & Rings
- [ ] 3c Showcases: sampled the domain chapter(s) I care about

**Phase 4 — Foundations as needed**
- [ ] TPIL ch. 2–5 (when type errors confuse me)
- [ ] Logic and Proof core (if I want deeper logic grounding)

**Phase 5 — Build something**
- [ ] Chose a theorem / Mathlib gap to formalize
- [ ] Formalized it in `05-project/`
- [ ] (Stretch) Opened a Mathlib PR · (Advanced) sampled the Hitchhiker's Guide

---

## Resources appendix

| Resource | Link | One-liner | Audience / tag |
| --- | --- | --- | --- |
| **Lean learning hub** | <https://lean-lang.org/learn/> | Official directory of everything below. | Everyone · start here |
| **Natural Number Game (NNG4)** | <https://adam.math.hhu.de/> | Browser-based game: build ℕ from scratch, learn `rfl`/`rw`/`induction`. | Complete beginners · beginner |
| **The Mechanics of Proof** | <https://hrmacbeth.github.io/math2001/> | Rigorous proof-writing mirrored in Lean with simplified, pedagogical tactics; bridges NNG → Mathlib. | New-to-proofs students · beginner |
| **Mathematics in Lean (MIL)** | <https://leanprover-community.github.io/mathematics_in_lean/> | The canonical hands-on tutorial for formalizing real math on Mathlib. | Math students / mathematicians · core |
| **MIL companion repo** | <https://github.com/leanprover-community/mathematics_in_lean> | The exercise files you edit alongside the MIL textbook. | MIL workers · workspace |
| **Theorem Proving in Lean 4** | <https://lean-lang.org/theorem_proving_in_lean4/> | Foundations: dependent type theory, propositions-as-types, how tactics make terms. | Why-does-it-work learners · intermediate |
| **Logic and Proof** | <https://leanprover-community.github.io/logic_and_proof/> | Symbolic logic + natural deduction, each idea replayed in Lean. | Logic-foundations learners · beginner |
| **Functional Programming in Lean** | <https://lean-lang.org/functional_programming_in_lean/> | Lean as a strict pure functional language; useful early chapters for syntax/type classes. | Programmers / tactic authors · optional sidebar |
| **Hitchhiker's Guide to Logical Verification (2025)** | <https://github.com/lean-forward/logical_verification_2025> | Graduate course: verification, semantics, Hoare logic, metaprogramming, ℚ/ℝ construction. | Grad students / researchers · advanced |
| **Mathlib4 docs** | <https://leanprover-community.github.io/mathlib4_docs/> | Generated API reference; learn the naming convention here. | Reference · all levels |
| **Loogle** | <https://loogle.lean-lang.org/> | Structure-aware lemma search by shape, name, type, or conclusion. | Reference · all levels |
| **LeanSearch** | <https://leansearch.net/> | Natural-language semantic search over Mathlib4. | Reference · all levels |
| **LeanExplore** | <https://www.leanexplore.com/> | Hybrid semantic search across multiple Lean libraries; API/MCP. | Reference · all levels |
| **Lean community** | <https://leanprover-community.github.io/> | Hub for Mathlib, contribution guide, and the Zulip chat. | Contributors · all levels |
| **lean.nvim** | <https://github.com/Julian/lean.nvim> | The Neovim plugin for Lean 4: InfoView, unicode input, LSP, Loogle. | Neovim users · setup |
| **Arch Wiki: Lean** | <https://wiki.archlinux.org/title/Lean> | Arch-specific install (elan via the AUR) and Neovim/Emacs integration. | Arch users · setup |

---

*Now open the InfoView, type something yourself, and prove `2 + 2 = 4`. The rest follows.*
