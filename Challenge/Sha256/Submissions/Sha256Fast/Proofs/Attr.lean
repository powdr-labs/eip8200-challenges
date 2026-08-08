import Lean
/-!
# Simp-set attributes for the optimized SHA-256 proof

`evmStep` is the unfolding set used to reduce a straight-line EVM block.  It
lives in its own module because Lean requires a simp attribute to be declared
in a module earlier than the one that uses it.  A submission tags its own
generated `path`, artifact, instruction list and byte literal with `@[evmStep]`;
the generic stepper definitions are tagged in `Sha256Fast.Block`.
-/
register_simp_attr evmStep
