Sheaf lang demo
===============

This is a small demo I put together to play with the idea of interpreting
a (normal, functional, programming) language in a sheaf over some other
category which defines “actual” computations.

I may be iterating on the language a bit to explore variants. I'll make releases
for the checkpoint which could be interesting references on their own.

The sheaves extend the base category computations with all the things you
usually have in a language, however limited the base language is (even some
flavour of dependent types potentially). Since this is just a demo, I just built
a simply typed λ-calculus.

The flipside of this model is that you can only execute functions at
representable types. I only chose `Int -> Int` for simplicity, but any
`Int × … × Int -> Int × … × Int` would work too, if I had taken the time to set
them up.

To interpret into presheaves, it seems useful to use an intrinsically typed
representation (another good reason to use simple types). I didn't want to
bother with typed de Bruijn so I thought a parametric higher-order abstract
syntax (PHOAS) would be better. It probably was, but it turned out to be harder
to use than I expected (and the typechecker ends up encoding de Bruijn indices
anyway, so I didn't really avoid dealing with type level lists).

The silver lining is that this repository can also serve as a decently minimal
example of how to use PHOAS, with a typechecker and an interpreter.

## How to play around

The executable has two subcommands:

### `run` -- evaluate an expression

```
stack exec sheaf-lang-demo -- run N EXPR
```

Compiles `EXPR` (which must have type `Int -> Int`), applies it to `N`, and
prints the result.

```
$ stack exec sheaf-lang-demo -- run 5 '\(x : Int). x * x + 1'
26
```

### `show` -- display the compiled arithmetic expression

```
stack exec sheaf-lang-demo -- show [-d DEPTH] [-w WIDTH] EXPR
```

Compiles `EXPR` and pretty-prints the lowered arithmetic expression instead of
evaluating it. This is useful to see what the sheaf interpretation produces.
Because fixed points generate infinite arithmetic terms, the output is truncated
at depth `DEPTH` (default 10). `WIDTH` controls the line width for formatting
(default 80).

```
$ stack exec sheaf-lang-demo -- show '\(x : Int). if iszero x then 0 else x * x'
if iszero id then 0 else id * id

$ stack exec sheaf-lang-demo -- show -w 30 '\(x : Int). if iszero x then 0 else x * x'
if iszero id
  then 0
  else id * id
```

### Language overview

The input language is a simply typed lambda calculus with integers, booleans, and
lists. Some examples:

```
\(x : Int). x + 1
\(x : Int). if iszero x then 0 else x * x
let (f : Int -> Int) (x : Int) = x * 2 in f 3
let rec (f : Int -> Int) (n : Int) = if iszero n then 1 else n * f (n - 1) in f
```

Type annotations are optional when the type can be inferred from context:

```
\x. x + 1
let f x = x * 2 in f 3
```

See also the `examples/` directory.

## Some notes

### Sheaves vs presheaves

A [previous
iteration](https://github.com/aspiwack/sheaf-lang-demo/releases/tag/presheaves)
of this repository interpreted the λ-calculus into presheaves. Presheaves are a
little bit more direct than sheaves (also sheaves are much less documented in
the context of programming languages, so it took me quite a lot of trial and
error to get there, I learnt a lot).

The problem is that presheaves _create_ all colimits. No matter how many
colimits you have in your base category (in particular sums/coproducts), they
won't be colimits in the category of presheaves. For a two-level programming
language like ours, it means that all the control flow is entirely at the
λ-calculus level and can't involve arithmetic types. A strict separation is
kept.

Quite concretely, in this version of the language we have a function `iszero ::
Int -> Bool`. And we can branch on Booleans with `if b then … else …`. With
presheaves this would simply be impossible: Booleans are evaluated at the
arithmetic level, so they are still symbolic when we want to evaluate the `if`
branch.

With sheaves, however, the evaluator is going to postpone evaluating branches
and compile them to `if` branches in the arithmetic level.

#### Weaknesses

Even though the frontend language and the base category share control flow, I
don't know how to make fixed points (or any sort of looping behaviour) in the
frontend language compile to fixed point (or any sort of looping behaviour) in
the base category.

Effectively this means that fixed points generate infinite terms of the base
category. Using laziness, this isn't a problem. These infinite terms can still
be evaluated. We just have to be careful when printing to only print up to a
certain depth.

### PHOAS and binders

I have found that it's better to represent binders as

``` haskell
Lam :: (forall w. (forall ρ. v ρ -> w ρ) -> w σ -> Expr w τ) -> Expr v (σ `TArr` τ)
```

Rather than the more usual, but weaker

``` haskell
Lam :: (v σ -> Expr v τ) -> Expr v (σ `TArr` τ)
```

(why weaker? instantiate with `id`)

This form is quite close to the type of presheaves' internal homs. So it's
probably not surprising that it works well to interpret presheaves internal hom
elements as functions. But I believe it to be the right way to represent PHOAS
binders, at least for intrinsically typed representations, because it gives the
ability to change the type of the context.

I haven't been able to find a source for this trick. At least not in code.
Someone must have done it before me: I even had an LLM suggest it to me. if you
find a source, please let me know. I **need** to know.

However, [_ Semantical analysis of higher-order abstract syntax_ (Martin
Hoffmann 1999)][presheaf-hoas] ([author version][presheaf-hoas-author]) shows
how several flavours of higher-order abstract syntax, including a version quite similar to
parametric higher-order abstract syntax, can be analysed as presheaves (but they
always arrange for the left-hand side of arrows to be representable so that they
don't need the more complex representation).

[presheaf-hoas]: https://ieeexplore.ieee.org/document/782616
[presheaf-hoas-author]: https://www.dcs.ed.ac.uk/home/mxh/lics99hoas.ps.gz

## Acknowledgement

Making sheaves work has been arduous. It's only been possible to get to this
point with the help of James Haydon and Jean-Philippe Bernardy.
