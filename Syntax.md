# Syntax for the STILL system

```
n        ::= (natural numbers)
x,y,z    ::= (variable names)
xs,ys,zs ::= x,xs | \(\epsilon\)
t        ::= tactic atom (IdA, ForallR, ForallL x "A", ...)

-- Functional terms
M,N,S,T ::= Pi x : M . N | Sigma x : M . N | lambda x : M . N
        | (M,N) : Sigma x : S . T | fst M | snd M | M N | Prop | Type n | x

-- Session types
A,B ::= 1 | $M | A -o B | A * B | A & B | A + B
    | forall x : M . A | exists x : M . A | forall x : stype . A | exists x : stype . A
    | nu x . A | !A | x

-- Commands
C ::= module x I begin | module x begin | theorem x: "A" PC

-- Imports
I ::= imports [x]

-- Proving commands
PC ::= apply TE | defer | done

-- Tactic expressions
TE ::= (TE) | TE;TE | TE<|>TE | TE+ | t

-- Process terms
P,Q ::= P|Q | (\(\nu\)x)P | x[y].P | x[M].P | x[A].P | x.inl;P | x.inr;P | x.case(P, Q)
    | x(y).P | !x(y).P | x <-> y | [x <- M] | (corec x(ys) P) (zs) | x(ys)
```