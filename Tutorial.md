# STILL Prover Tutorial

STILL is a proof assistant for **session types**, grounded in the Curry-Howard
correspondence between intuitionistic linear logic and the π-calculus. Proving a
session type proposition produces a concurrent process that implements the
corresponding communication protocol.

The proof scripts in this tutorial have not all been fully evaluated at the
current time, but are provided as a reference for the general structure of proof
scripts. This disclaimer will be removed when the proof scripts are all
evaluated.

---

## 1. Core Propositions

Session types are built from these proposition forms:

| Syntax | Reading | What the channel does |
|--------|---------|----------------------|
| `1` | Unit | Terminates (sends nothing, consumes nothing). |
| `$M` | Lift | Carries a functional value of type `M`. |
| `A -o B` | Linear implication | Receives a channel of type `A`, then continues as `B`. |
| `A * B` | Tensor | Sends a channel of type `A` and continues as `B`. |
| `A & B` | With | Offers a choice: the peer selects either `A` or `B`. |
| `A + B` | Plus | Makes a choice internally: selects and sends either `A` or `B`. |
| `!A` | Replication | Provides unlimited copies of `A`. |
| `nu X.A` | Recursive type | Coinductive (infinite) session type. |
| `forall x:M.A` | First-order forall | Receives a term of functional type `M`, then continues as `A`. |
| `exists x:M.A` | First-order exists | Sends a term of functional type `M`, then continues as `A`. |
| `forall X:stype.A` | Second-order forall | Receives a session type, then continues. |
| `exists X:stype.A` | Second-order exists | Sends a session type, then continues. |
| `X` | Type variable | Abstract variable introduced by `nu` or `forall X:stype`. |

**Key rules:**
- Linear assumptions must be used **exactly once**; they cannot be discarded or duplicated.
- Unrestricted assumptions (from `!`) may be used any number of times.
- Propositions must always be **double-quoted** in script syntax: `"A -o B"`.

**Base types and literals:**

| Syntax | Meaning |
|--------|---------|
| `Int` | The type of integers (`42`, `-7`). Lives at `Type 0`. |
| `String` | The type of strings (`'hello'`). Lives at `Type 0`. |
| `42` | Integer literal. Has type `Int`. |
| `'hello'` | String literal (single-quoted). Has type `String`. Escapes: `\'` `\\` `\n` `\t`. |
| `#add`, `#sub`, `#mul`, `#div`, `#mod`, `#neg` | Integer arithmetic built-ins. |
| `#eq`, `#lt` | Comparison built-ins (return `1` for true, `0` for false). |
| `#show` | Convert `Int` to `String`. |
| `#strlen` | Length of a `String` as `Int`. |
| `#concat` | Concatenate two `String`s. |

---

## 2. File Structure

Every STILL proof file has the form:

```
module ModuleName [imports Mod1 Mod2 ...] begin

-- Optional type synonyms
stype Name = "proposition"

-- Optional functional assumptions
assume x is "Type j"
assume X is stype

-- Theorems
theorem TheoremName [consumes "B1" "B2" ...] : "Goal"
apply tactic1
apply tactic2
...
done

-- Optional: extract the synthesized process term
extract TheoremName

end
```

**Notes:**
- The `module ... begin` declaration is mandatory.
- `end` is optional.
- Comments start with `--`.
- `consumes "B"` declares that the theorem linearly consumes a resource of type `B` as an assumption.

---

## 3. Proof State

After each `apply`, the prover displays the current proof state. A subgoal looks like:

```
[unrestricted: u:A, v:B] [linear: a:C, b:D] [functional: x:M] ⊢ z : Goal
```

- **Unrestricted context** (`[unrestricted: ...]`): Available unlimited times.
- **Linear context** (`[linear: ...]`): Must be used exactly once.
- **Functional context** (`[functional: ...]`): Term-level bindings for the ECC layer.
- **`z : Goal`**: The channel `z` offers the session type `Goal`.

When multiple subgoals are open, they are listed in sequence. `apply` always targets the **first** subgoal. Use `defer` to move the current goal to the end.

---

## 4. A First Proof: Identity

The session type `A -o A` says: receive a channel of type `A`, then offer a channel of type `A`.

```
module Example begin

theorem id: "A -o A"
apply ImpliesR
apply IdA
done
```

**Step by step:**

1. **Initial goal:** `⊢ z : A -o A`
2. **`apply ImpliesR`** — Introduces the implication. Adds assumption `a : A` to the linear context; goal becomes `⊢ z : A`.
3. **`apply IdA`** — Links channel `z` with assumption `a`. Both are of type `A`. Subgoal closed. ✓

---

## 5. Tensor Commutativity

```
module Example begin

theorem tensor_comm: "A * B -o B * A"
apply ImpliesR
apply TensorLA
apply TensorR
apply IdA
apply IdA
done
```

**Step by step:**

1. `ImpliesR` — Assumption `a : A * B`; goal `⊢ z : B * A`.
2. `TensorLA` — Auto-destructs `a : A * B` into `a1 : A` and `a2 : B`.
3. `TensorR` — Splits goal `B * A` multiplicatively. Two subgoals: `⊢ z : B` and `⊢ z' : A`.
4. `IdA` — Closes `⊢ z : B` by linking with `a2 : B`.
5. `IdA` — Closes `⊢ z' : A` by linking with `a1 : A`.

The same proof with tacticals:

```
theorem tensor_comm: "A * B -o B * A"
apply ImpliesR; TensorLA; TensorR; IdA
done
```

---

## 6. With Commutativity

The `&` connective is additive: the same context is shared between branches.

```
module Example begin

theorem with_comm: "A & B -o B & A"
apply ImpliesR
apply WithR
apply WithL2A
apply IdA
apply WithL1A
apply IdA
done
```

**Step by step:**

1. `ImpliesR` — Assumption `a : A & B`; goal `⊢ z : B & A`.
2. `WithR` — Two subgoals (same context): prove `⊢ z : B`, then prove `⊢ z : A`.
3. `WithL2A` — Selects right branch of `a : A & B`, giving `a' : B`. Closes first subgoal with `IdA`.
4. `WithL1A` — Selects left branch of `a : A & B`, giving `a' : A`. Closes second subgoal with `IdA`.

---

## 7. Replication and Copy

`BangL` moves a `!A` assumption to the unrestricted context. `Copy` then instantiates it.

```
module Example begin

theorem share: "!A -o A * A"
apply ImpliesR
apply BangLA
apply TensorR
apply Copy a
apply IdA
apply Copy a
apply IdA
done
```

1. `ImpliesR` — Assumption `a : !A`; goal `⊢ z : A * A`.
2. `BangLA` — Moves `a : !A` to unrestricted as `a : A`.
3. `TensorR` — Two subgoals: both need to prove `A`.
4. `Copy a` — Copies `a` from unrestricted into linear. `IdA` closes the first `A` goal.
5. `Copy a` — Another copy. `IdA` closes the second.

---

## 8. Tacticals

Tactic expressions can be composed:

| Syntax | Meaning |
|--------|---------|
| `T1 ; T2` | Apply `T1`, then `T2` to every resulting subgoal. |
| `T1 <\|> T2` | Try `T1`; if it fails, apply `T2`. |
| `T+` | Repeat `T` until it fails (at least once). |
| `Skip` | Always succeeds, changes nothing. `Skip+` will loop forever. |

**Precedence:** `+` > `<|>` > `;`

**Example — strip all tensors then close:**
```
apply ImpliesR; TensorLA+; (TensorR; (IdA <|> Skip))+
```

This is the idiomatic pattern for permuting large tensors (see `Commutative.still`).

**Example — apply multiple intros at once:**
```
apply Intros
```
`Intros` repeatedly applies all non-branching introductions (`ImpliesR`, `ForallR`, `BangR`, etc.).

---

## 9. CutTheorem: Reusing Proven Results

`CutTheorem t` introduces the session type of theorem `t` as a linear assumption, allowing it to be composed into the current proof.

```
module Example begin

theorem helper: "A -o A"
apply ImpliesR; IdA
done

theorem main: "!(A -o A) -o A -o A"
apply ImpliesR
apply BangLA
apply Copy f
apply ImpliesL f
apply IdA
apply IdA
done
```

Or using `CutTheorem`:

```
theorem main2: "A -o A"
apply CutTheorem helper
apply ImpliesLA
apply IdA
done
```

`CutTheorem helper` adds `helper`'s type `A -o A` as a linear assumption. `ImpliesLA` then applies it: creates a subgoal to prove `A` (closed with `IdA`), then the channel of type `A` is linked.

---

## 10. Defer

`defer` moves the current subgoal to the end of the queue. Use it when a later branch is easier, or when you need to discharge subgoals in a different order.

```
theorem example: "A -o B -o A * B"
apply ImpliesR
apply ImpliesR
apply TensorR
defer       -- defer the first subgoal (A)
apply IdA   -- close B (now first)
apply IdA   -- close A (was deferred)
done
```

---

## 11. Functional Layer (ECC)

When proving propositions involving functional types (`forall x:M.A`, `exists x:M.A`, `$M`), functional subgoals appear. These are discharged with ECC tactics (`Ax`, `Var`, `Exact`, etc.) using the same `apply` command.

**Functional tactic keywords do not carry an `F` prefix** (except `FSkip`). The functional layer implements the Embedded Calculus of Constructions.

### Example: Receiving and sending a term

```
module Bank begin

assume nat is "Type 1"

theorem ping: "forall n:nat. $n -o $n"
apply ForallR    -- adds n:nat to functional context; goal: forall n:nat.$n -o $n -> $n -o $n
apply FTermLA    -- eliminates $n assumption; adds n to functional context
apply FTermR     -- opens ECC subgoal: prove n:nat
apply VarA       -- closes by finding n in the functional context
apply IdA        -- closes the remaining session goal
done
```

### Example: Providing an existential witness

```
apply ExistsR
apply Exact "fst (pair)"   -- supply the witness term; Exact checks it against the goal type
```

### ForallL / ForallLA

`ForallL x` (or `ForallLA`) instantiates a universal assumption, creating functional subgoals for the witness:

```
apply ForallLA         -- selects the first forall assumption
apply Exact "myTerm"   -- provides the witness
```

---

## 12. Recursive Types

`nu X.A` is a coinductive session type. Use `NuR` to introduce a corecursion and `TyVar` to make recursive calls.

```
module Semaphore begin

theorem stream: "nu Y. $resource -o $resource * Y"
apply NuR S () ()
apply ImpliesR
apply TensorR; (IdA <|> Skip)
apply TyVar S ()
done
```

**How it works:**

1. `NuR S () ()` — Introduces the corecursion binding named `S` with no parameters (`()`) and no initial arguments (`()`). Goal becomes the body `$resource -o $resource * Y`.
2. `ImpliesR` — Standard implication introduction.
3. `TensorR; (IdA <|> Skip)` — Proves the tensor: links the resource, leaves the `Y` goal.
4. `TyVar S ()` — Makes the recursive call to `S` with no arguments. Closes the `Y` goal coinductively.

**With parameters:** If the corecursion carries state, supply parameter names and initial values:
```
apply NuR S (handle) (a)   -- binding S, parameter 'handle', initial value 'a'
apply TyVar S (c)           -- recurse with new argument 'c'
```

---

## 13. Second-Order Quantification

`forall X:stype.A` and `exists X:stype.A` quantify over session types themselves.

```
module Example begin

theorem poly: "forall X:stype. X -o X"
apply Forall2R      -- adds X to type variable context
apply ImpliesR
apply IdA
done
```

`Forall2L x "B"` instantiates a second-order universal assumption with a concrete session type:
```
apply Forall2L a "nat -o 1"
```

---

## 14. ExactPi: Direct Process Terms

For experienced users (or when extraction is known), close a goal by supplying the process term directly:

```
theorem server: "A -o A"
apply ExactPi "z(x).[x <-> z]"
done
```

The process `z(x).[x <-> z]` is type-checked against `A -o A`. Process syntax:

| Process | Meaning |
|---------|---------|
| `0` or `stop` | Halt |
| `P \| Q` | Parallel composition |
| `(nu x:A)P` | Restriction: fresh channel `x` of type `A` |
| `x[y].P` | Send channel `y` on `x`, continue as `P` |
| `x[$M].P` | Send functional term `M` on `x`, continue as `P` |
| `x(y).P` | Receive on `x`, bind to `y`, continue as `P` |
| `x.inl;P` | Send left injection on `x` |
| `x.inr;P` | Send right injection on `x` |
| `x.case(inl: P, inr: Q)` | Receive injection on `x`; branch on inl→P, inr→Q |
| `[x <-> y]` | Link channels `x` and `y` (identity/forwarding) |
| `[x <- M]` | Lift: bind result of evaluating term `M` to channel `x` |
| `!x(y).P` | Replicated receive |
| `(corec S(ys) P)(zs)` | Corecursive process |
| `print[M].P` | Evaluate `M`, print it to stdout, continue as `P` |
| `readline(x).P` | Read a line from stdin, bind as string `x`, continue as `P` |

---

## 15. Module Imports

Theorems from other modules are available after importing:

```
module MyModule imports Semaphore SNat begin

-- CutTheorem can reference theorems from imported modules:
theorem example: "..."
apply CutTheorem stream
...
done
```

---

## 16. Common Proof Patterns

### Strip all top-level implications
```
apply Intros
```

### Destruct all tensor assumptions
```
apply TensorLA+
```

### Prove a tensor goal with identity on both sides
```
apply TensorR; IdA
```

### Use an unrestricted assumption multiple times
```
apply BangLA          -- move !A to unrestricted
apply Copy a          -- first use
apply IdA
apply Copy a          -- second use
apply IdA
```

### Apply a first-order universal assumption
```
apply ForallLA         -- or: apply ForallL x
apply Exact "term"     -- supply the witness
```

### Introduce a cut for an intermediate session type
```
apply Cut "A -o B"
-- first subgoal: prove A -o B
apply ImpliesR; IdA
-- second subgoal: use A -o B as assumption
apply ImpliesLA; IdA
```

### Prove a goal by Plus injection
```
apply PlusR1    -- or PlusR2
apply ...       -- prove the selected branch
```

### Branch on a Plus assumption
```
apply PlusLA            -- or: apply PlusL x
-- first subgoal: assume left branch
apply ...
-- second subgoal: assume right branch
apply ...
```

---

## 17. MCP Tools Reference

When using STILL through the MCP server, these tools are available:

### `check_proof`
Execute a STILL proof script and return outputs and errors.
- **Input:** `text` — the full `.still` script as a string.
- **Output:** Whether the proof succeeded, any outputs, and any errors.
- **Use for:** Verifying a proof, running a script, checking for parse or tactic errors.

### `get_proof_state`
Get the proof state at a specific cursor position in a script.
- **Input:** `text`, `line` (0-based), `col` (0-based).
- **Output:** The proof state (goals, contexts) immediately after the command at that position.
- **Use for:** Inspecting what the goal looks like at any point in a proof.

### `list_theorems`
List all theorems proven in a script.
- **Input:** `text` — the full script.
- **Output:** Names of all proven theorems.
- **Use for:** Checking what has been established in a module.

### `get_tactic_reference`
Get the complete tactic reference documentation.
- **Input:** None.
- **Output:** Full tactic reference (Tactics.md content).

### `get_tutorial`
Get this tutorial.
- **Input:** None.
- **Output:** Full tutorial (Tutorial.md content).

---

## 18. Workflow for Writing Proofs with MCP

1. **Start with the theorem statement.** Write the `theorem Name: "..."` line.
2. **Apply introductions.** Use `apply Intros` or individual introduction tactics.
3. **Check state.** Use `get_proof_state` at the current line to inspect the subgoal.
4. **Proceed.** Add more `apply` lines based on the visible goal and context.
5. **Verify.** Use `check_proof` to run the script and confirm it succeeds.
6. **Iterate.** If there are errors, read the error message and adjust tactics.

### Example workflow

Write a partial proof:
```
module Test begin
theorem t: "A * B -o B * A"
apply ImpliesR
```

Call `get_proof_state` at the `apply ImpliesR` line to see:
```
[linear: a : A * B] ⊢ z : B * A
```

Continue:
```
apply TensorLA
apply TensorR
apply IdA
apply IdA
done
```

Call `check_proof` to confirm `Success: True`.

---

## 19. Type Synonym Abbreviations

`stype` declarations create abbreviations that expand throughout the module:

```
module Protocol begin

stype Request = "forall n:nat. $n -o $n"
stype Server  = "!Request"

theorem server: "Server"
apply BangR
apply ForallR
apply FTermLA
apply FTermR
apply VarA
apply IdA
done
```

Synonyms can be used anywhere a proposition is expected (they are expanded automatically before proof checking).

---

## 20. Functional Assumptions

`assume x is "M"` declares a functional variable available in all theorems of the module:

```
module Bank begin

assume string is "Type 1"
assume nat    is "Type 1"
assume uid    is "Pi s:string. Type 1"

theorem client: "forall s:string. $uid s -o ..."
...
```

`assume X is stype` declares an abstract session type variable:

```
assume resource is stype

theorem token: "resource -o resource * 1"
...
```

---

## 21. Integer and String Literals

STILL's functional layer supports integer and string base types directly.

```
module Literals begin

-- Integer literal: type is Int
-- String literal:  type is String (single-quoted)

-- Proves the type Int lives at Type 0
theorem intType: "exists x : Type 0 . $x"
apply ExistsR
apply Exact "Int"
apply FTermR
apply Exact "42"
done
```

String literals use single quotes `'...'`. Supported escape sequences: `\'`, `\\`, `\n`, `\t`.

**Built-in functions** are written `#name` and applied like ordinary functional terms:

| Built-in | Type | Example |
|----------|------|---------|
| `#add` | `Int -> Int -> Int` | `#add 3 4` → `7` |
| `#sub` | `Int -> Int -> Int` | `#sub 10 3` → `7` |
| `#mul` | `Int -> Int -> Int` | `#mul 6 7` → `42` |
| `#div` | `Int -> Int -> Int` | `#div 10 3` → `3` |
| `#mod` | `Int -> Int -> Int` | `#mod 10 3` → `1` |
| `#neg` | `Int -> Int` | `#neg 5` → `-5` |
| `#eq` | `Int -> Int -> Int` | `#eq 3 3` → `1` (true) |
| `#lt` | `Int -> Int -> Int` | `#lt 2 5` → `1` (true) |
| `#show` | `Int -> String` | `#show 42` → `'42'` |
| `#strlen` | `String -> Int` | `#strlen 'hi'` → `2` |
| `#concat` | `String -> String -> String` | `#concat 'a' 'b'` → `'ab'` |

Built-ins reduce automatically during term evaluation (`Simp`, `Exact`, `run`, etc.).

---

## 22. Console I/O: print and readline

Two process constructors provide console I/O, each with a corresponding session type.

### `print[M].P` — output

Session type: `($T) * A`

Evaluates `M : T`, prints it to stdout, then continues as `P` providing `A`.

```
module Hello begin

process Hello : "($String) * 1" = "print['Hello, World!'].stop"
run Hello
```

Output: `Hello, World!`

The type `($String) * 1` reads: "send a string value, then terminate."

### `readline(x).P` — input

Session type: `$String -o A`

Reads a line from stdin, binds it as `x : String`, then continues as `P`.

```
module Echo begin

process Echo : "$String -o ($String) * 1" = "readline(x).print[x].stop"
run Echo
```

This process reads a line and echoes it back.

### Combining I/O

```
module Calc begin

-- Reads a greeting prefix and appends "!" to it.
process Exclaim : "$String -o ($String) * 1" =
    "readline(x).print[#concat x '!'].stop"
```

### I/O in tactic proofs

`print` and `readline` can also appear as sub-processes when using `ExactPi`:

```
theorem echo: "$String -o ($String) * 1"
apply ExactPi "readline(x).print[x].stop"
done
```

The type checker verifies:
- `readline(x)` consumes the `$String -o` prefix and binds `x : String` in the functional context.
- `print[x]` matches `$String` (since `x : String`), leaving goal `1`.
- `stop` closes `1`.

---

## 23. The `process` and `run` Commands

### `process Name : "A" = "P"`

Defines a named process directly from a process term, without writing a tactic proof:

```
module Demo begin

process Greet : "($String) * 1" = "print['Hi from STILL!'].stop"
```

The process body `P` is **parsed and type-checked** against session type `A`. If type-checking succeeds, `Name` is stored as a theorem exactly as if it had been proven with tactics. The theorem can then be used with `CutProc`, `run`, or `extract`.

**Syntax reminder:** `A` and `P` are each wrapped in double quotes. String literals *inside* `P` use single quotes to avoid ambiguity.

### `run Name`

Executes the process extracted from a theorem:

```
module Demo begin

process Hello : "($String) * 1" = "print['Hello, World!'].stop"
run Hello
```

`run` calls `verifyProofM` on the theorem's stored proof to recover the process term, then runs it. Any `print` output appears immediately; any `readline` waits for user input.

```
module Demo begin

theorem id_str: "$String -o ($String) * 1"
apply ImpliesR
apply FTermLA
apply FTermR
apply VarA
apply IdA
done

process echo : "$String -o ($String) * 1" = "readline(x).print[x].stop"
run echo
```

Both `theorem`-defined and `process`-defined theorems can be run.

### Execution model

- **Sequential within a process**: actions execute left-to-right.
- **Parallel (`P | Q`)**: `P` and `Q` run concurrently. STILL uses Haskell MVars for channel communication; linear channels are synchronous rendezvous points.
- **Replication (`!x(y).P`)**: spins up a persistent server loop; each incoming connection forks a new copy of `P`.
- **Corecursion (`corec`)**: runs the body and loops via Haskell lazy knot-tying; use for infinite server processes.
- **Exceptions**: if a runtime error occurs (stuck channel, unmatched pattern, etc.) it is caught and reported as an error in the proof state rather than crashing the process.
