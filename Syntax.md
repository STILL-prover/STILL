# Syntax for the STILL system

In general terms and propositions must be wrapped in double quotes when using the system.

```
n        ::= (natural numbers)
s        ::= (string literals, single-quoted: 'hello', with \', \\, \n, \t escapes)
x,y,z    ::= (variable names)
xs,ys,zs ::= x,xs | ε
t        ::= tactic atom (IdA, ForallR, ForallL x "A", ...)

-- Functional terms
M,N,S,T ::= Pi x : M . N | Sigma x : M . N | lambda x : M . N
        | (M,N) : Sigma x : S . T | fst M | snd M | M N
        | Prop | Type n
        | Int | String          -- base types
        | n | 's'               -- integer and string literals
        | #name                 -- built-in function (e.g. #add, #show, #concat)
        | _                     -- hole (placeholder)
        | x

-- Session types
A,B ::= 1 | $M | A -o B | A * B | A & B | A + B
    | forall x : M . A | exists x : M . A | forall x : stype . A | exists x : stype . A
    | nu x . A | !A | x

-- Commands
C ::= module x I begin | module x begin
    | theorem x: "A" PC
    | process x : "A" = "P"     -- define and type-check a process directly
    | run x                     -- execute the process extracted from theorem x

-- Imports
I ::= imports [x]

-- Proving commands
PC ::= apply TE | defer | done

-- Tactic expressions
TE ::= (TE) | TE;TE | TE<|>TE | TE+ | t

-- Process terms
P,Q ::= P|Q | (nu x:A)P
    | x[y].P | x[$M].P | x[stype A].P   -- send channel / term / type
    | x(y).P                             -- receive
    | x.inl;P | x.inr;P                 -- plus injection
    | x.case(inl: P, inr: Q)            -- plus case
    | !x(y).P                           -- replicated receive
    | [x <-> y]                         -- link / forward
    | [x <- M]                          -- lift term
    | (corec x(ys) P)(zs)               -- corecursion
    | call x(ys) | x(ys)                -- corecursive call
    | print[M].P                        -- print term M, continue as P
    | readline(x).P                     -- read a line into x, continue as P
    | 0 | stop                          -- halt

-- Built-in functions (#name syntax)
-- Arithmetic:  #add  #sub  #mul  #div  #mod  #neg  #eq  #lt
-- Strings:     #concat  #strlen  #show
```

## Notes on literals and built-ins

String literals use **single quotes**: `'hello world'`.  
Supported escape sequences: `\'` `\\` `\n` `\t`.

Built-in functions are written `#name` and can be applied like any functional term:
- `#add 1 2` → `3`
- `#show 42` → `'42'`
- `#concat 'hello ' 'world'` → `'hello world'`

## Session types for print and readline

| Process | Required goal shape | Meaning |
|---------|---------------------|---------|
| `print[M].P` | `($T) * A` | Evaluate `M : T`, print it, continue as `A` |
| `readline(x).P` | `$T -o A` | Read a line into `x : T`, continue as `A` |

For console I/O use `T = String` (i.e. `($String) * A` and `$String -o A`).