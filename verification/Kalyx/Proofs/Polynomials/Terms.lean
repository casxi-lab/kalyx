module

public import Kalyx.Statements.Polynomials
import Kalyx.Proofs.Polynomials.Roundtrip

/-!
# Proofs of the statements about expansion and conversion

One theorem for each registered statement of `Kalyx.Statements.Polynomials`
about the expansion of terms and their conversion back, whose type is exactly
that statement. They state that the expansion of a term into a polynomial and
the conversion of a polynomial back to a term keep the meaning of terms.

The proof rests on three helper modules of this directory. Every operation of
the ring over `ℚ` that returns a value returns a canonical polynomial that
denotes its result, so by induction over a term, the factors of its products
and the monomials of its sums, a term whose expansion returns a polynomial
holds only numbers, the variable, sums, products and powers with nonnegative
exponents, and has the value of the polynomial at every assignment
(`Kalyx.Proofs.Polynomials.Expansion`). The conversion back builds its term
through the constructors of the term core, which on canonical operands
without calls keep the meaning of their input under the rules of calls that
keep every call, so its value is that of the polynomial
(`Kalyx.Proofs.Polynomials.Conversion`). Its term is the number of the
constant, the term of a single term, or the sum of the terms of the terms in
the stored order, since the powers of the variable increase in the order of
terms as their degrees do; its expansion forms only the constants of the
coefficients, the powers of the variable up to a degree, the terms of the
polynomial and the sums of its first terms, each of which costs no more and
has no higher degree than the polynomial, so under limits that admit the
polynomial and the depth of the term each passes its checks and the last sum
is the polynomial (`Kalyx.Proofs.Polynomials.Roundtrip`).
-/

namespace Kalyx.Proofs.Polynomials

open Kalyx.Statements.Polynomials
open Kalyx.Proofs.Polynomials.Expansion Kalyx.Proofs.Polynomials.Conversion
open Kalyx.Proofs.Polynomials.Roundtrip

/-- Proves `ExpansionKeepsMeanings`. -/
public theorem expansionKeepsMeanings : ExpansionKeepsMeanings :=
  ⟨fun _ _ I _ _ h ρ => (expand_denote h I).2 ρ,
    fun _ _ _ _ ho hI _ _ ha h => ⟨fun ρ => toTerm_denote ho hI h ρ,
      fun hdepth hcheck => toTerm_expand ho ha h hdepth hcheck⟩⟩

end Kalyx.Proofs.Polynomials
