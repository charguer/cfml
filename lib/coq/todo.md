# For testing purpose

## Inputing
- Port and adapt Guillaume's surface syntaxe in Coq for CFML
- Write down Fibonacci

## Computing
- problem with computability of maps -> move to CompCert's PTrees
- PTrees: no union operation defined? To add?
- Need to convert cfml's vars to AST.ident == positive to this end

# On ident generation
- Reusing essentially the [mon] monad from CompCert that is more or less [FreshT fail]
- Question of initial seed: should be fine to just use 0 for us
- Question of tracking ident to source name: duplicate locally [mon] with an extended [trail] field?
