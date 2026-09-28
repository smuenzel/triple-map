
# Triple Map

Triple map is a weight-balanced map implementation for ocaml using fat leafs.

Leafs contain up to 3 key-value pairs, while taking up only about as much space as one
node of Stdlib.Map, drastically improving space efficiency (and cache hit rate).

The weight balancing scheme is proven in Rocq (balance property is maintained during
building/rebalacing). Other operations are not yet proven.

Performance is usually faster than Stdlib.Map for almost all operations.
Sometimes triple map is slightly slower (on the order of a couple of percent), but
memory usage and intermediate allocations are consistently better.
