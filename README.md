# RUXt: Under-approximation for Type Unsoundness in Unsafe Rust

This Coq development contains a formalization of a simple expression language with function calls, as a simplified model of the Rust programming language. For reasoning about its programs, we formalize two separation logics:
+ an over-approximate SL, a simplification of the type system of RustBelt;
+ an under-approximate SL, an adaptation of Incorrectness SL.

The formalization provides key principles that relate both logics. Notably, a derivable UX triple may disprove a type specification in Rust, enabling the detectation of type unsoundness for safe functions with internal unsafe code.
To compile this Coq development, simply run `make`.


### Prerequisites
This development is known to compile with
+ Coq 8.19.2


### Directory Structure
The `lib/` directory contains auxiliary definitions and lemmas for generic definitions.
+ `gmap.v`: Additional facts about the `gmap` type from the `stdpp` library.

The `lang/` directory contains the formalization of our programming language.
+ `lang.v`: Language syntax, pure expression evaluation, variable substitution.
+ `semantics.v`: Operational semantics, frame preservation.

The `assertion/` directory contains the formalization of our assertion language.
+ `hprop.v`: Logical assertions on heaps.
+ `types.v`: Generic type definition, assertions for type ownership.
+ `types/`: Directory containing some default type definitions.

The `logic/` directory contains the formalization of both logics and properties relating them.
+ `specs.v`: Under-approximate logic.
+ `typing.v`: Over-approximate logic.
+ `sound.v`: Principles relating OX and UX reasoning.
