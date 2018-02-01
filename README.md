# Opal Semantics

Alex Renda,
Harrison Goldstein,
Sarah Bird,
Chris Quirk,
Adrian Sampson

## Contents

1. Formalization of [Opal](https://capra.cs.cornell.edu/research/opal/) semantics ([semantics.pdf](semantics.pdf)).
2. Coq implementation of semantics ([src/OpalSemantics.v](src/OpalSemantics.v))
3. Coq implementation of an interpreter ([src/OpalInterp.v](src/OpalInterp.v))
4. Theorems and proofs over the Coq implementation of semantics ([src/OpalProofs.v](src/OpalProofs.v))
5. An unverified "compiler" from a nicer syntax to constructors for the Coq embedding ([src/compiler](src/compiler))

## Usage

Run `make` to make everything, `make tex` to regenerate the semantics pdf, and `make coq` to machine check each of the proofs.
