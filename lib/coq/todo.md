# For testing purpose

## Inputing
- [DONE] Port and adapt Guillaume's surface syntaxe in Coq for CFML
- [Somewhat DONE] Write down Fibonacci

## Computing
- [DONE] problem with computability of maps -> move to CompCert's PTrees
- [DONE] PTrees: no union operation defined? To add?
- [DONE: added `option ident` to the `var` type] Need to convert
  cfml's vars to AST.ident == positive to this end

# On ident generation
- Reusing essentially the [mon] monad from CompCert that is more or less [FreshT fail]
- Question of initial seed: should be fine to just use ~~0~~ 1
  (`positive` > 0) for us
- Question of tracking ident to source name: duplicate locally [mon]
  with an extended [trail] field?

# Semantics

- omnismall for clight statements -> [Workaround: defined *eventually*
  judgement from Clight's small step]
- [DONE] remove subst for cfml omnismall, and add envs
- Rewrite memory model of CFML_C to be closer to Clight's
  (*ie* `block -> offset -> val`)
- Maybe Add traces to CFML_C's semantic?
- Actually refactor semantics (cf Clight.state)
