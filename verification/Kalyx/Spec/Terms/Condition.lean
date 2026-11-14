module

public import Kalyx.Spec.Terms.Call

/-!
# Terms: conditions

A condition is a term of rank 7 (TRM-R15; architecture, "Conditions"): the
truth values `true` and `false`, a comparison of two values by one of the
relations `==`, `!=`, `<`, `<=`, `>` and `>=`, a property predicate
`is_<property>(u)` or `defined(u)` of one value, and the connectives `not` of
one condition and `and` and `or` of two or more. At each assignment of its
symbols a condition is true, false or undefined.

This specification states the place of conditions after the sums, their
order within the rank (by shape with its relation or property, in the order
that the parameter `Orders.condition` gives, then by their operands), the
separation of the two classes and the atomicity of conditions: no rule of
sums, products and powers takes or enters a condition, a condition operand
of a value constructor fails with `Syntax`, and the one rule of the term core
that reads a condition is the rule of `piecewise` on a truth value
(`piecewiseBranch`).

The constructor of conditions here checks the number and the classes of the
operands (`CondShape.takes`) and builds the node as it is. The structural
normalization of kalyx's constructor of conditions (flattening `and` and
`or`, sorting their operands and removing repeated ones, `not` of `not`, and
absorbing `true` and `false`), the strong Kleene connectives, the decision of
comparisons and the list of the properties are not part of this
specification. The meaning of a condition is a parameter of the semantics,
which fixes only the truth values.
-/

@[expose] public section

namespace Kalyx.Spec.Terms

/-- The truth value `b` as a condition, without operands. -/
def Term.ofBool (b : Bool) : Term := .condition (.truth b) []

/-- The constructor of conditions (TRM-R15): the condition node of the shape
`s` and the operands `ops`, canonical terms, when the shape takes them, and
`Syntax` when their number or a class is wrong. The node is built as it is,
without structural normalization. -/
def mkCondition (s : CondShape) (ops : List Term) : Result Term :=
  if s.takes ops then .value (.condition s ops) else .fault (.syntax none)

end Kalyx.Spec.Terms

end
