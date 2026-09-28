
# Triple Map

Triple map is a weight-balanced map implementation for ocaml using fat leaves.

Leaves contain up to 3 key-value pairs, while taking up only about as much space as one
node of Stdlib.Map, drastically improving space efficiency (and cache hit rate).

The weight balancing scheme is proven in Rocq (balance property is maintained during
building/rebalacing). Other operations are not yet proven.

Performance is usually faster than Stdlib.Map for almost all operations.
Sometimes triple map is slightly slower (on the order of a couple of percent), but
memory usage and intermediate allocations are consistently better (sometimes by a very
large factor, such as 6x for the `equal` operation or 1.6x to 1.8x for `union`).

Cardinal is O(1), compared to Stdlib.Map's O(n).

In general, modifying operations attempt to maintain the original map if the operation
ends up being the identity (including in the case of `map` or `union`, where the resulting
types may be different).

Some unsafe operations are used to work around limitations in the what we can express to
the OCaml compiler, but they are intended to be safe in practice (and real unsafety is
considered a bug). Generally, the operations are wrapped in interfaces and should not be
used directly from outside the library.

## Balancing Scheme

We maintain the following balance: omega2 * n1 > 2 * n2, where n1,n2 are the weights of
the two children, and omega2 = 5.

Weight is defined as the sum of the weights of the child nodes, with weight(empty) = 1.
Thus, weight is one more than the number of elements.

## Performance Engineering

Flambda at -O3 is strictly required to achieve acceptable performance.
