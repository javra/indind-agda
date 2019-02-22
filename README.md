# Reduction of Inductive-Inductive Types in Agda

## II.agda

Contains the syntax for closed inductive-inductive types

## IF.agda

Contains the syntax for indexed inductive types with contexts for sort (`Scon`) and for point constructors (`Con`).

## IFA.agda

Contains the Set interpretation of the syntax described in IF.agda, describing algebras of indexed inductive types.

## IFM.agda

Contains the model for the indexed inductive types which describes morphisms.

## IFD.agda

Contains displayed algebras of indexed inductive types. These algebras depend on an algebra as described in IFA.agda.

## IFS.agda

Contains the indexed inductive type interpretation for the section of the aforementioned displayed algebras.

## EWRSg.agda

Contains the definitions on how to obtain the the erasure `E`, the wellformedness `w`, the eliminator relation `R` and the initial object `Sg` for inductive-inductive types.

## II2IF.agda

Encapsulates the previous file by assuming the existence of indexed inductive types and deriving the existence of inductive-inductive types.
