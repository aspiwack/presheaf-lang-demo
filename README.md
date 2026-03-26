Presheaf lang demo
==================

This is a small demo I put together to play with the idea of interpreting
a (normal, functional, programming) language in a presheaf over some other
category which defines “actual” computations.

I may be iterating on the language a bit to explore variants. I'll make releases
for the checkpoint which could be interesting references on their own.

The presheaves extend the base category computations with all the things you
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
