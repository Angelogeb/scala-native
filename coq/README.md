## Coq Proofs for STLC 1/2 ##


This directory contains mechanized proofs of safety properties in STLC 1/2↩
built on top of the artifacts of STLC1/2 (https://github.com/tiarkrompf/scala-escape).
Mechanization was tested on `Coq 8.15.0`.

The following is a table mapping definitions and theorems in Coq
to the corresponding Theorems and Lemmas in the paper.

|File     |Item            | Description                          | Definition
|---------|----------------|--------------------------------------|-----------
| stlc1.v | Figure 3       | Term                                 | `tm`
|         |                | Type                                 | `ty`
|         |                | Environment                          | `env`
|         |                | Lookup                               | `lookup`
|         |                | Typing Relation                      | `has_type`
|         | Figure 4       | Value (Instrumented Semantics)       | `vl`
|         |                | Evaluation (Instrumented Semantics)  | `teval`
| stlc4.v | Theorem 3      | Soundness `teval`                    | `full_safety`
| stlc2.v | Figure 5       | Value (Stack Semantics)              | `vl_stack`
|         |                | Evaluation (Stack Semantics)         | `teval_stack`
|         |                | Separation of environment and stack  | `fc_eval`
| stlc3.v | Theorem 5      | Equivalence `teval` ~ `teval_stack`  | `teval_equiv`
| dsub.v  |                | Soundness D_{<:}                     | `full_safety`

## DSUB 1/2 details ##

We extend our formal model with polymorphism and subtyping in System DSUB 1/2 [dsub.v](dsub.v).

This file contains our Coq development for System DSUB 1/2 (Section 4.1 in the paper).

- Language syntax (types `ty`, terms `tm`, values `vl`)
- Type Assignment (`has_type`)
- Subtyping (static: `stp`, dynamic: `stp2`)
- Operational semantics (`teval`)
- **Theorem**: type soundness (`full_safety`, corresponds to Theorem 4.2 in the paper)

The type system and operational semantics are as described in the paper, and set up
like in the STLC 1/2 development.

One difference is in how we treat environments: in STLC 1/2 environments were split
into 1st and 2nd part, but here we use flat environments and add a 1st/2nd class tag
to each element, and also a boolean flag denoting whether the element is accessible.

Evaluation and type assignment remove 2nd-class items from the environment by
turning their access flags to false. Note however, that the dynamic subtyping
relation must ignore these flags in order to relate path-dependent types across
environments. Since this is only an invariant used in the soundness proof and
not part of the operational semantics, this is not a safety concern. 

The type soundness result shows that the type system correctly predicts the runtime
checks by the evaluator, which are the same as in STLC 1/2. It would be easy, 
but not very insightful, to redo the formal proof of semantic equivalence 
with a stack-based evaluator, as we have done for STLCs 1/2.
