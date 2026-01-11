# RUXtBelt: The Semantic Model of RUXt

To compile this Coq development, simply run `make`.

### Prerequisites
This development is known to compile with
+ Rocq 9.0.1
+ Rocq-std++ 1.12.0


### Directory Structure
The `lib/` directory contains auxiliary definitions and lemmas for generic definitions.
+ `list.v`: Additional facts about the `list` type from the `stdpp` library.
+ `gmap.v`: Additional facts about the `gmap` type from the `stdpp` library.

The `lang/` directory contains the formalization of the semantics for our programming language and assertions.
+ `lang.v`: Language syntax, pure expression evaluation, variable substitution.
+ `semantics.v`: Operational semantics, frame preservation.
+ `assertion.v`: Logical assertions on heaps.

The `model/` directory contains the formalization of RUXt.
+ `logic.v`: Template for a sound under-approximate program logic.
+ `risl.v`: RISL proof rules, instantiation as UX logic.
+ `typechecker.v`: Function type signatures and safe programs.
+ `summary.v`: Summary contexts and properties.
+ `refute.v`: The refutation algorithm and the inadequacy theorem.


### Additional Content

The `types/` directory contains the formalization of Rust types à la RustBelt.
+ `type.v`: Generic type definition, assertions for type ownership.
+ `lib/`: Directory containing some default type definitions.
+ `rules.v`: Rules of the type system.
+ `validity.v`: Properties relating OX and UX reasoning.
