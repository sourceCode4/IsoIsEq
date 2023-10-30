# UniMath formalization of "Isomorphism is equality"
This is a formalization of results from the paper "Isomorphism is equality" by Coquand and Danielsson.
All the code is located in the file `IsoIsEq.v`, which is organized into three sections: `code`, `universe` and `monoid`. Below is an overview of the file contents. More information can be found in the comments above definitions.

### code
This section contains the formalization of the main results of the paper:
* definitions of types `code` and `instance`
* instance projections `carier` and `element`
* proofs of `equality_pair_lemma` and the `isomorphism_is_equality` theorem.
* propositions `isisomorphism` and `isomorphic`

### universe
This section contains the formalization of a concrete universe example given in the paper:
* definition of the universe `U`
* definition of the decoding function `El`
* definition of `cast`, `resp` and `resp_id` along with several lemmas used for their definitions

### monoid
This section contains the formalization of a type of monoids encoded as an instance of the appropriate `code`, and additional proofs that this instance is weakly equivalent (and hence equal) to the type `monoid` from the UniMath library. It contains the following definitions:
* `monoidcode`, the code of monoids, and `monoidinstance`, the type of monoids coded by `monoidcode`, along with several helper definitions
* `toinstance` and `frominstance` conversion functions
* proofs `weqmonoid` and `eqmonoid` of weak equivalence and equality between the instance and the library type

## Instructions
Make sure that your load path contains the path to UniMath. This could be done by passing the following flag to your Coq LSP:
```
--rec-load-path=/your/path/to/UniMath,UniMath
```
