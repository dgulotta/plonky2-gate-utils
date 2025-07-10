# plonky2_gate_utils

A library for simplifying the construction of plonky2 gates.

## Overview

Typically, implementing a gate in plonky2 requires writing a variety of
functions including `eval_unfiltered`, `eval_unfiltered_circuit`, and
`generators`.  The first two functions are supposed to compute the same
polynomials.  Depending on the design of the gate, `generators` may also
compute these polyomials.  This library makes it possible to write a gate
that computes a polynomial by writing just one function.

## Example

Defining a gate:
```rust
use plonky2::{field::extension::OEF, hash::hash_types::RichField};
use plonky2_gate_utils::SimpleGate;

struct ConvolutionGate;

impl<F: RichField> SimpleGate<F> for ConvolutionGate {
    const ID: &'static str = "ConvolutionGate";
    const INPUTS_PER_OP: usize = 20;
    const OUTPUTS_PER_OP: usize = 19;
    const DEGREE: usize = 2;
    fn eval<E, const D: usize>(wires: &[E]) -> Vec<E>
    where
        E: OEF<D, BaseField = F>,
    {
        let mut output = vec![E::ZERO; 19];
        for i in 0..10 {
            for j in 0..10 {
                output[i + j] += wires[i] * wires[j + 10];
            }
        }
        output
    }
}
```

Using the gate:
```rust
let input = builder.add_virtual_targets(20);
let output = ConvolutionGate::apply(&mut builder, &input);
```

## Assumptions

- `INPUTS_PER_OP + OUTPUTS_PER_OP` must be less than or equal to the number of
routable wires.
- If `D * (INPUTS_PER_OP + OUTPUTS_PER_OP)` is greater than the number of
routable wires, then the `apply_ext` function must be implemented manually.

## Assumptions

- `INPUTS_PER_OP + OUTPUTS_PER_OP` must be less than or equal to the number of
routable wires.
- If `D * (INPUTS_PER_OP + OUTPUTS_PER_OP)` is greater than the number of
routable wires, then the `apply_ext` function must be implemented manually.

## How it works

If `G` implements `SimpleGate`, then the library creates a gate `GateAdapter<G>`
is that computes `G::eval`.  In order to evaluate
`GateAdapter<G>::eval_unfiltered_circuit`, the library generates a second gate
uses a second gate called `RecursiveGateAdapter<G>` that computes `G::eval`
over the extension field (unless `G::apply_ext` is manually overridden).

The `RecursiveGateAdapter<G>` can evaluate its own `eval_unfiltered_circuit`
function, so there is no infinite explosion of gate types.  It makes use of the
following fact: If $E/F$ is a finite Galois extension of fields, then
$E\otimes_F E$ is isomorphic to $E^{[E:F]}$.

