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

## Some notes

### Sheaves vs presheaves

A [previous
iteration](https://github.com/aspiwack/presheaf-lang-demo/releases/tag/presheaves)
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
