module
public import GenExpr.Types
public meta import GenExpr.Types

/-!
GenExpr — a general expression parser.

Raw text in, ranked type-inferred Lean code out. The library is independent of OEIS: callers
supply their own function catalogue, desired signatures and known values.
-/
