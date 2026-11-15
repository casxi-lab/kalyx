module

public import Kalyx.Statements.Terms
import Kalyx.Proofs.Terms.Faults
import Kalyx.Proofs.Terms.Grouping
import Kalyx.Proofs.Terms.Closure

/-!
# Proofs of the statements about the canonical forms

One theorem for each registered statement of `Kalyx.Statements.Terms` about
the canonical forms that the constructors return: their independence of the
order and the grouping of the operands, their closure and idempotence,
merging, the bases of negative powers, the faults of strict evaluation and the
atomicity of calls, whose type is exactly that statement. Each theorem
assembles the results of the helper modules, which register nothing:
`Kalyx.Proofs.Terms.Sums` and `Kalyx.Proofs.Terms.Products` for sums and
products, `Kalyx.Proofs.Terms.Grouping` for the grouping of products and the
powers of roots, `Kalyx.Proofs.Terms.Closure` for the closure, the rebuild and
the negation, `Kalyx.Proofs.Terms.Bases` for the bases of negative powers and
the calls, and `Kalyx.Proofs.Terms.Faults` for strict evaluation.
-/

namespace Kalyx.Proofs.Terms

open Kalyx.Spec.Terms Kalyx.Statements.Terms

/-- Proves `SumsAndProductsIgnoreOrderAndGrouping`. -/
public theorem sumsAndProductsIgnoreOrderAndGrouping : SumsAndProductsIgnoreOrderAndGrouping :=
  fun o me R ho _ =>
  ⟨Sums.sumsIgnoreOrder o me R ho, Sums.sumsIgnoreGrouping o me R ho,
    fun _ _ _ _ _ hp hu hu' =>
      Result.value.inj (hu.symm.trans ((Products.mkProduct_perm o ho me hp).trans hu')),
    Grouping.productsIgnoreGrouping o me R ho, Sums.sumsOfValuesSucceed o,
    fun _ h => Products.mkProduct_value_or_limit o ho me fun t ht => (h t ht).2,
    fun _ _ _ hu hle => Products.mkProduct_mono hu hle⟩

/-- Proves `CanonicalFormsAreClosedAndIdempotent`. -/
public theorem canonicalFormsAreClosedAndIdempotent : CanonicalFormsAreClosedAndIdempotent :=
  Closure.canonicalFormsAreClosedAndIdempotent_holds

/-- Proves `MergingAddsCoefficientsAndExponents`. -/
public theorem mergingAddsCoefficientsAndExponents : MergingAddsCoefficientsAndExponents :=
  fun o me R ho _ =>
  ⟨Sums.sumsMergeCoefficients o me R ho,
    fun _ _ _ _ hc hp hr h0 hu hq => Products.mkProduct_parts o ho hc hp hr h0 hu hq,
    fun _ _ _ h => Products.mkProduct_zero o ho me h,
    fun _ _ _ hb => Products.mkProduct_one o ho me hb,
    fun _ hk => Products.mkPower_imaginaryUnit o me hk,
    Grouping.powersOfRoots o me R ho⟩

/-- Proves `ConstructorsKeepNegativeBases`. -/
public theorem constructorsKeepNegativeBases : ConstructorsKeepNegativeBases :=
  Bases.constructorsKeepNegativeBases_of Closure.negationReadsOpposite

/-- Proves `StrictEvaluationFaults`. -/
public theorem strictEvaluationFaults : StrictEvaluationFaults :=
  strictEvaluationFaults_holds

/-- Proves `CallsAreAtoms`. -/
public theorem callsAreAtoms : CallsAreAtoms :=
  Bases.callsAreAtoms_holds

end Kalyx.Proofs.Terms
