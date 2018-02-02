<h2 align="center">Pico: towards Dependent Haskell</h2>

This repo hosts an in-progress implementation of the Pico type-system and core language from [Richard A. Eisenberg's thesis](https://github.com/goldfirere/thesis/).

Plans: once that is done, I will implement the Bake algorithm from the paper, which is a constraint-generating type inference engine similar to the corresponding part of OutsideIn(X). With Bake, I will be able to convert the formalised subset of Haskell from Eisenberg's thesis into Pico.

## Current status

I'm working on the small-step evaluation at present.

- [ ] implement small-step evaluation for Pico
- [ ] typechecker for Pico
- [ ] tbd

## Links

- an incomplete implementation of Vytinotis et al.'s [OutsideIn(X)](https://github.com/mrkgnao/preposterous) by me

## License

The source code for this implementation is licensed under GPL-3.

The source theory, languages, and the [paper](https://github.com/goldfirere/thesis/) are all copyright Richard Eisenberg.
