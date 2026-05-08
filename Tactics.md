# STILL Tactic Reference

## Session Type Tactics

### Identity

- `IdA` — Close the current subgoal by linking the channel with the first matching assumption in the linear context. The two must have the same session type.
- `Id x` — Close the current subgoal by linking the channel with the named assumption `x`.

### Functional Term Lift

- `FTermR` — Refine a lifted functional term goal (`$M`). Opens an ECC subgoal to prove the term `M` in the functional layer.
- `FTermL x` — Eliminate a lifted functional term assumption `$M` named `x`. Adds `M` to the functional context. Alias: `LiftL x`.
- `FTermLA` — Auto-apply `FTermL` to the first lifted term (`$M`) in the linear context. Alias: `LiftLA`.

### Implication (`-o`)

- `ImpliesR` — Refine an implication goal `A -o B`. Adds `A` as a fresh linear assumption; goal becomes `B`.
- `ImpliesL x` — Eliminate an implication assumption `A -o B` named `x`. Creates two subgoals: prove `A`, then continue with `B` as a linear assumption.
- `ImpliesLA` — Auto-apply `ImpliesL` to the first implication (`-o`) in the linear context.

### Unit (`1`)

- `UnitR` — Close a unit goal `1`. The linear context must be empty at this point.
- `UnitL x` — Eliminate a unit assumption `1` named `x`. Removes it from the linear context.
- `UnitLA` — Auto-apply `UnitL` to the first unit assumption (`1`) in the linear context.

### Replication (`!`)

- `BangR` — Refine a replication goal `!A`. The linear context must be empty; proves `A` under the unrestricted context alone.
- `BangL x` — Eliminate a replication assumption `!A` named `x`. Moves the inner proposition `A` to the unrestricted context.
- `BangLA` — Auto-apply `BangL` to the first replication assumption (`!`) in the linear context.
- `Copy u [v]` — Copy the unrestricted assumption named `u` into the linear context. Optionally rename the copy `v`; if omitted a fresh name is generated.

### Tensor (`*`)

- `TensorR` — Refine a tensor goal `A * B`. Creates two subgoals with a multiplicative split of the linear resources: one to prove `A`, one to prove `B`.
- `TensorL x` — Eliminate a tensor assumption `A * B` named `x`. Both `A` and `B` become separate linear assumptions.
- `TensorLA` — Auto-apply `TensorL` to the first tensor assumption (`*`) in the linear context.

### With (`&`)

- `WithR` — Refine a with goal `A & B`. Creates two subgoals sharing the same context (additive split): the **first subgoal proves `A`** (left) and the **second subgoal proves `B`** (right), ordered left-to-right matching the goal proposition. Each branch receives its own independent copy of the entire linear context; resources are not split between branches.
- `WithL1 x` — Eliminate a with assumption `A & B` named `x`, selecting the left branch `A`. **Consumes** the assumption entirely; the right branch `B` is discarded.
- `WithL1A` — Auto-apply `WithL1` to the first with assumption (`&`) in the linear context. **Consumes** the assumption, keeping only the left (`A`) branch. Note: unlike `WithR` (which copies the context additively), `WithL` eliminates the assumption — only one branch is chosen.
- `WithL2 x` — Eliminate a with assumption `A & B` named `x`, selecting the right branch `B`. **Consumes** the assumption entirely; the left branch `A` is discarded.
- `WithL2A` — Auto-apply `WithL2` to the first with assumption (`&`) in the linear context. **Consumes** the assumption, keeping only the right (`B`) branch.

### Plus (`+`)

- `PlusR1` — Refine a plus goal `A + B`, choosing the left injection `A`.
- `PlusR2` — Refine a plus goal `A + B`, choosing the right injection `B`.
- `PlusL x` — Eliminate a plus assumption `A + B` named `x`. Creates two subgoals: one with `A` assumed, one with `B` assumed.
- `PlusLA` — Auto-apply `PlusL` to the first plus assumption (`+`) in the linear context.

### First-Order Quantification

- `ForallR` — Refine a first-order universal goal `forall x:M.A`. Adds a fresh variable of type `M` to the functional context; goal becomes `A`.
- `ForallL x` — Instantiate a first-order universal assumption `forall y:M.A` named `x`. Produces functional subgoals to supply and type-check the witness term, then continues with the instantiated proposition.
- `ForallLA` — Auto-apply `ForallL` to the first first-order universal assumption in the linear context.
- `ExistsR` — Refine a first-order existential goal `exists x:M.A`. Produces functional subgoals to supply and type-check the witness term, then continues with the instantiated goal.
- `ExistsL x` — Eliminate a first-order existential assumption `exists y:M.A` named `x`. Adds the variable to the functional context.
- `ExistsLA` — Auto-apply `ExistsL` to the first first-order existential assumption in the linear context.

### Second-Order Quantification

- `Forall2R` — Refine a second-order universal goal `forall X:stype.A`. Adds `X` to the type variable context.
- `Forall2L x "B"` — Instantiate a second-order universal assumption named `x` with the session type `B`.
- `Exists2R "B"` — Refine a second-order existential goal `exists X:stype.A` by providing the session type `B`.
- `Exists2L x` — Eliminate a second-order existential assumption named `x`. Adds `X` to the type variable context.
- `Exists2LA` — Auto-apply `Exists2L` to the first second-order existential assumption in the linear context.

### Recursive Types (`nu`)

- `NuR x (ys) (zs)` — Introduce a corecursive session type `nu X.A`. `x` names the binding, `ys` are the parameter names, and `zs` are the initial argument values.
- `NuL c` — Unfold the corecursive assumption `nu X.A` named `c` one step.
- `NuLA` — Auto-apply `NuL` to the first recursive assumption in the linear context.
- `TyVar x (zs)` — Fire a corecursive call. `x` is the binding name from a prior `NuR`; `zs` are the new argument values for this iteration.

### Cut

- `Cut "A"` — Cut the session type `A`. Two subgoals: prove `A`, then continue with `A` as a linear assumption.
- `CutRepl "A"` — Cut the replicating type `!A`. Two subgoals: prove `A`, then continue with `A` in the unrestricted context.
- `CutTheorem t` — Cut a previously proven theorem named `t`. Its session type becomes a linear assumption in the current goal.
- `CutProc n` — Cut a process assumption `n` declared with `assume process` into the current proof.

### Structural

- `Weaken t` — Remove variable `t` from the unrestricted or functional context (weakening structural rule). Does not affect the linear context.

### Direct Proof

- `ExactPi "P"` — Close the current goal by directly supplying a process term `P`. The process is type-checked against the current session type goal.

### Automation

- `Intros` — Repeatedly apply all available non-branching introduction rules (`ImpliesR`, `ForallR`, `BangR`, etc.) until none apply.

---

## Tacticals

Tacticals compose tactic expressions using operator syntax. They apply uniformly to both session-type and ECC functional tactic expressions.

| Syntax | Name | Meaning |
|--------|------|---------|
| `T1 ; T2` | Then | Apply `T1`, then apply `T2` to every resulting subgoal. |
| `T1 <\|> T2` | Alt | Try `T1`; if it fails, try `T2` instead. |
| `T+` | Repeat | Apply `T` repeatedly until failure; requires at least one success. |
| `Skip` | Skip | Always succeeds, leaves goals unchanged. Use `FSkip` inside ECC tactic expressions. |

**Operator precedence** (tightest to loosest): `+` (postfix) > `<|>` (left-associative) > `;` (left-associative).

**Example:**
```
apply TensorLA+; (TensorR; (IdA <|> Skip))+
```
Repeatedly destructs all tensor assumptions, then for each tensor subgoal repeatedly tries to prove it—using `IdA` where possible, falling back to `Skip` on subgoals that are not yet ready.

---

## ECC Functional Tactics

These tactics operate on the ECC (Embedded Calculus of Constructions) subgoals that arise from `FTermR`, `ForallR`, `ExistsR`, `ForallL`, and related tactics. They are applied with the same `apply` command as session-type tactics.

**Note on names:** Most functional tactics do **not** use an `F` prefix in the actual syntax—`Ax`, `Var`, `Lambda`, etc. The exception is `FSkip`, which carries the prefix to distinguish it from the session-type `Skip`.

### Axiom and Variables

- `Ax` — Prove the axiom `Prop : Type 0`.
- `VarA` — Automatically select the variable in the functional context whose type matches the current goal type.
- `Var x` — Prove the goal using the variable `x` from the functional context.

### Pi Types (Dependent Functions)

- `PiProp` — For goals of the form `(Pi x:A.B) : Prop`. Types `A` as a proposition.
- `Pi ["A"]` — For goals of the form `(Pi x:A.B) : Type j`. Optionally supply `A` explicitly if it is not already determined.
- `Lambda` — For goals of the form `(lambda x:A.N) : (Pi x:A.B)`. Introduces the lambda abstraction.
- `App x "A" ["n"]` — Apply function `x` of type `A` to an argument. Optionally supply the argument term `n` explicitly if it cannot be inferred.

### Sigma Types (Dependent Pairs)

- `Sigma ["A"]` — For goals of the form `(Sigma x:A.B) : Type j`. Optionally supply `A`.
- `Pair ["m"] ["n"] j` — For goals of the form `(m,n) : (Sigma x:A.B)` at universe level `j`. Optionally supply pair components `m` and/or `n`.
- `Proj1 x "B"` — Refine a goal `fst M : A` where `M : Sigma x:A.B`. `x` names the pair; `B` is the second component type.
- `Proj2 x "A" ["m"]` — Refine a goal `snd M : [fst M/x]B`. `x` names the pair; `A` is the first component type. Optionally supply `m = fst M`.

### Reduction and Proof Terms

- `Cummulativity "A" j` — Refine the goal type to `A` using at most `j` definitional reduction steps. Used when the goal and expected type are definitionally equal but syntactically different.
- `Simp [n]` — Simplify the current goal term using up to `n` beta-reduction steps (default: 100).
- `Exact "t"` — Close the functional goal by supplying term `t` as the proof inhabitant. The term is checked against the goal type.
- `ExactKnown` — Auto-close the functional goal if the proof term is already fully determined by prior tactic applications.
- `FSkip` — Identity tactic for functional proof contexts. Always succeeds and leaves the goal unchanged. (Use `Skip` in session-type contexts.)

---

## Script-Level Commands

These are top-level commands in a `.still` file, not tactic expressions.

| Command | Effect |
|---------|--------|
| `module Name begin` | Declare a module named `Name`. |
| `module Name imports Mod1 Mod2 ... begin` | Module with imports from other modules. |
| `stype Name = "A"` | Declare a session type synonym: `Name` expands to proposition `A`. |
| `assume x is "M"` | Declare a functional assumption: variable `x` has type `M` (e.g., `"Type 1"`). |
| `assume process x is "A"` | Declare a process assumption `x` with session type `A`. |
| `assume X is stype` | Declare `X` as an abstract session type variable. |
| `theorem Name : "A"` | Begin a proof of session type `A`. |
| `theorem Name consumes "B1" "B2" : "A"` | Theorem that linearly consumes resources `B1`, `B2`, ... as assumptions. |
| `apply T` | Apply tactic expression `T` to the current proof state. |
| `defer` | Move the current subgoal to the end of the subgoal queue. |
| `done` | Assert the proof is complete (all subgoals closed). |
| `extract Name` | Extract and display the process term synthesized for theorem `Name`. |
| `process Name : "A" = "P"` | Parse process `P`, type-check it against session type `A`, and store it as a theorem named `Name`. No tactic proof required. |
| `run Name` | Extract the process from theorem `Name` (via `verifyProofM`) and execute it. I/O side effects are performed immediately. |
| `print_theorems` | Print all theorems proven so far in this module. |
| `help` | Print a command reference. |
